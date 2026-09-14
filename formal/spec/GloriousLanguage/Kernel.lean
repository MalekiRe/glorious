import GloriousLanguage.Storage

/-! Structural language, not a compiler IR commitment (§19). Sequencing is
explicit. No constructor recognizes a source-library control name. -/
namespace Glorious.Language.Kernel

inductive Projection where
  | field (index : Nat)
  | index (localSlot : Identity)
  | dereference
  deriving DecidableEq, BEq, Repr, Inhabited

structure Place where
  localSlot : Identity
  projections : List Projection := []
  deriving DecidableEq, BEq, Repr, Inhabited

structure Local where
  id : Identity
  type : Term
  mutable : Bool
  deriving Repr, Inhabited

/-- The explicit continuation binder shared by source admission and clause
entry. Ordinary locals do not introduce a generative brand. -/
def Local.resumptionBrand (localSlot : Local) : Option Identity :=
  match localSlot.type with
  | .continuation (.scopedBrand brand) _ _ _ _ => some brand
  | _ => none

inductive CaptureMode where
  | shared | unique | own
  deriving DecidableEq, BEq, Repr, Inhabited

structure Capture where
  formal : Identity
  place : Place
  mode : CaptureMode
  type : Term
  deriving Repr, Inhabited

inductive Pattern where
  | wildcard
  | bind (localSlot : Local)
  | scalar (value : ScalarValue)
  | unit
  | tuple (fields : List Pattern)
  | array (fields : List Pattern)
  | constructor (variant : DeclId) (fields : List Pattern)
  | reference (mode : Mutability) (pattern : Pattern)
  deriving Repr, Inhabited

inductive Atom where
  | constant (value : Term)
  | acquire (source : Place) (forceMove : Bool)
  | borrow (source : Place) (mode : Mutability) (region : Term)
  | construct (type : Term) (variant : Option DeclId) (fields : List Place)
  | closure (function : DeclId) (arguments : List Term) (captures : List Capture)
  | function (function : DeclId) (arguments : List Term)
  | operation (operation : DeclId) (familyArguments itemArguments : List Term)
  | label (brand : Term)
  | primitive (declaration : DeclId) (arguments : List Term) (operands : List Place)
  | available (witness : Place)
  | bindings (pack : Place)
  deriving Repr, Inhabited

/-- Receiver access and environment access are independent. The witness is
a lexical place, never a forgeable runtime availability-table key. -/
structure EnvironmentAccess where
  witness : Place
  access : Access
  region : Term
  after : Term
  deriving Repr, Inhabited

structure Invocation where
  callee : Place
  arguments : List Place
  receiver : Access
  environment : Option EnvironmentAccess
  signature : Signature
  deriving Repr, Inhabited

/-- The same selected Fn/RunsIn obligation is consumed by structural typing
and contextual execution. A witness's presence is not an invocation proof. -/
def RunsInEnvironment (program : Language.Program) (context : Language.Context)
    (call : Invocation) (receiver brand region : Term) (residents : List Term) : Prop :=
  ∃ selected, call.environment = some selected ∧
    WellKinded program context selected.region .region ∧
    Entails program context (.outlives region selected.region) ∧
    Entails program context (.callable (call.receiver.type selected.region receiver)
      call.signature.parameters call.signature.result call.signature.effects call.signature.unsafeAllowed) ∧
    Entails program context (.runsIn (call.receiver.type selected.region receiver)
      (selected.access.type selected.region (.environment brand region residents)) call.signature.parameters
      selected.after call.signature.unsafeAllowed) ∧
    (selected.access ≠ .owned → selected.after = .environment brand region residents)

mutual
  inductive Code where
    | result (value : Place)
    | bind (localSlot : Local) (value : Atom) (next : Code)
    | evaluate (localSlot : Local) (value : Code) (next : Code)
    | assign (destination value : Place) (next : Code)
    | discard (value : Place) (next : Code)
    | invoke (result : Local) (call : Invocation) (next : Code)
    | tail (call : Invocation)
    | scope (identity : Identity) (body : Code)
    | label (brand region : Identity) (result : Term) (body : Code)
    | choose (subject : Place) (arms : List Arm)
    | handle (identity : Identity) (computation : Code) (handler : Handler)
    | test (result : Local) (subject : Place) (pattern : Pattern) (patternId : Identity) (next : Code)
    | endLoan (handle : Place) (next : Code)
    | unsafeScope (body : Code)
    | closeAvailable (value : Place) (next : Code)
    | reserve (localSlot : Local) (brand : Identity) (places : List Place) (next : Code)
    | abort
    deriving Repr, Inhabited

  inductive Arm where
    | clause (pattern : Pattern) (body : Code)
    deriving Repr, Inhabited

  inductive OperationArm where
    | clause (operation : DeclId) (familyArguments itemArguments : List Term)
        (patterns : List Pattern) (continuation : Option Local) (body : Code)
    deriving Repr, Inhabited

  inductive Handler where
    | attached (result : Term) (completion : List Arm) (operations : List OperationArm) (captures : List Capture)
    deriving Repr, Inhabited
end

def Arm.pattern : Arm → Pattern | .clause pattern _ => pattern
def Arm.body : Arm → Code | .clause _ body => body
def OperationArm.operation : OperationArm → DeclId | .clause id _ _ _ _ _ => id
def OperationArm.arguments : OperationArm → List Term | .clause _ family item _ _ _ => family ++ item
def OperationArm.patterns : OperationArm → List Pattern | .clause _ _ _ patterns _ _ => patterns
def OperationArm.continuation : OperationArm → Option Local | .clause _ _ _ _ continuation _ => continuation
def OperationArm.body : OperationArm → Code | .clause _ _ _ _ _ body => body
def Handler.result : Handler → Term | .attached result _ _ _ => result
def Handler.completion : Handler → List Arm | .attached _ completion _ _ => completion
def Handler.operations : Handler → List OperationArm | .attached _ _ operations _ => operations
def Handler.captures : Handler → List Capture | .attached _ _ _ captures => captures

structure Function where
  declaration : DeclId
  parameters : List Local
  captures : List Local
  signature : Signature
  body : Code
  activationRegion : Identity
  namedExit : Option Identity
  deriving Repr, Inhabited

def Pattern.terms : Pattern → List Term
  | .wildcard | .scalar _ | .unit => []
  | .bind localSlot => [localSlot.type]
  | .tuple fields | .array fields | .constructor _ fields => fields.flatMap Pattern.terms
  | .reference _ pattern => pattern.terms

def Atom.terms : Atom → List Term
  | .constant value | .borrow _ _ value | .construct value _ _ | .label value => [value]
  | .closure _ arguments captures => arguments ++ captures.map (·.type)
  | .function _ arguments | .primitive _ arguments _ => arguments
  | .operation _ family item => family ++ item
  | .acquire _ _ | .available _ | .bindings _ => []

def Invocation.terms (call : Invocation) : List Term :=
  call.signature.terms ++ call.environment.toList.flatMap (fun access => [access.region,access.after])

mutual
  /-- Complete lexical-template terms, including patterns, nested handler
  clauses, invocation contracts and binder defaults in their signatures. -/
  def Code.terms : Code → List Term
    | .result _ | .abort => []
    | .bind localSlot atom next => localSlot.type :: (atom.terms ++ next.terms)
    | .evaluate localSlot value next => localSlot.type :: (value.terms ++ next.terms)
    | .assign _ _ next | .discard _ next | .scope _ next | .endLoan _ next |
      .unsafeScope next | .closeAvailable _ next => next.terms
    | .invoke localSlot call next => localSlot.type :: (call.terms ++ next.terms)
    | .tail call => call.terms
    | .label _ _ result body => result :: body.terms
    | .choose _ arms => arms.flatMap Arm.terms
    | .handle _ computation handler => computation.terms ++ handler.terms
    | .test localSlot _ pattern _ next => localSlot.type :: (pattern.terms ++ next.terms)
    | .reserve localSlot _ _ next => localSlot.type :: next.terms

  def Arm.terms : Arm → List Term
    | .clause pattern body => pattern.terms ++ body.terms

  def OperationArm.terms : OperationArm → List Term
    | .clause _ family item patterns continuation body =>
        family ++ item ++ patterns.flatMap Pattern.terms ++ continuation.toList.map (·.type) ++ body.terms

  def Handler.terms : Handler → List Term
    | .attached result completion operations captures =>
        result :: (completion.flatMap Arm.terms ++ operations.flatMap OperationArm.terms ++ captures.map (·.type))
end

def Function.terms (function : Function) : List Term :=
  function.signature.terms ++ function.parameters.map (·.type) ++ function.captures.map (·.type) ++ function.body.terms

def Function.Lexical (function : Function) : Prop := ∀ term ∈ function.terms, term.Lexical

structure Program extends RuntimeProgram where
  functions : List Function

instance : Coe Program RuntimeProgram := ⟨Program.toRuntimeProgram⟩

def Program.function (program : Program) (id : DeclId) : Option Function :=
  program.functions.find? (fun function => function.declaration == id)

theorem Program.function_declaration {program : Program} {identity : DeclId} {function : Function}
    (found : program.function identity = some function) : function.declaration = identity := by
  have matching := List.find?_some found
  change (function.declaration.package == identity.package && function.declaration.serial == identity.serial) = true at matching
  simp only [Bool.and_eq_true,beq_iff_eq] at matching
  cases declared : function.declaration
  cases identity
  simp_all


/-- The body/declaration and caller-contract metadata boundary, shared by
specification admission and resident typing. This asserts no execution or
resource-soundness conclusion. -/
def BodyInventory (program : Program) : Prop :=
  (program.functions.map (·.declaration)).Nodup ∧
  (∀ function ∈ program.functions, ∃ declaration, program.declarations.function function.declaration = some declaration ∧
    function.signature = declaration.signature ∧ function.parameters.map (·.id) = declaration.parameters ∧
    function.captures.map (·.type) = declaration.captures) ∧
  (∀ declaration anchor, program.declarations.function declaration.header.id = some declaration → declaration.origin = .source anchor →
    ∃ function ∈ program.functions, function.declaration = declaration.header.id) ∧
  (∀ function ∈ program.functions, function.Lexical) ∧ program.UnsafeContractsValid

abbrev Binding := StorageBinding

abbrev Environment := List Binding

def Environment.SelectsKey (environment : Environment) (key : BindingKey) (binding : Binding) : Prop :=
  binding ∈ environment ∧ binding.key = key ∧
    ∀ other ∈ environment, other.key = key → other = binding

/-- Ordinary places and index operands use the same unique lexical binding
selection. An ambiguous environment supplies no usable binding. -/
def Environment.Selects (environment : Environment) (localSlot : Identity) (binding : Binding) : Prop :=
  environment.SelectsKey (.localSlot localSlot) binding

def Environment.implicit (environment : Environment) : Environment :=
  environment.filter fun binding => match binding.key with
    | .localSlot _ => false
    | .resourceInput _ | .obligation _ => true

/-- Contract ports are local to an invocation. Once an output enters its
recipient's ordinary environment, the actual fresh claim identity names it. -/
def StorageBinding.asObligation (binding : StorageBinding) : StorageBinding :=
  { binding with key := match binding.authority.parentLoan with
      | some identity => .obligation identity
      | none => binding.key }

def Environment.install (environment additions : Environment) : Environment :=
  additions ++ environment.filter (fun binding =>
    !(additions.any (fun addition => addition.key == binding.key)))

def Environment.inheritImplicit (outer inner : Environment) : Environment :=
  outer.install inner.implicit

inductive ResolvesProjections (world : World) (environment : Environment) :
    Address → Authority → List Projection → Address → Authority → Prop where
  | nil {address authority} : ResolvesProjections world environment address authority [] address authority
  | field {base authority field projections result permission value child} : world.Stores base value →
      value.fields[field]? = some (some child) →
      ResolvesProjections world environment (base.child field) authority projections result permission →
      ResolvesProjections world environment base authority (.field field :: projections) result permission
  | vacantField {base authority field value} : world.Stores base value → value.fields[field]? = some none →
      ResolvesProjections world environment base authority [.field field] (base.child field) authority
  | index {base authority localSlot projections binding value integer result permission} :
      environment.Selects localSlot binding → world.Stores binding.address value →
      value.head = .scalar (.integer false .pointer integer) → value.Initialized →
      Permitted world binding.authority .shared binding.address → 0 ≤ integer →
      ResolvesProjections world environment base authority (.field integer.toNat :: projections) result permission →
      ResolvesProjections world environment base authority (.index localSlot :: projections) result permission
  | dereference {base authority projections value id loan result permission view access} :
      world.Stores base value → value.head = .reference id → value.Initialized → Permitted world authority .shared base →
      world.loans.get id = some loan → loan.live = true →
      ReferenceView world base authority id loan.mode view access →
      ResolvesProjections world environment loan.referent view projections result permission →
      ResolvesProjections world environment base authority (.dereference :: projections) result permission

inductive ResolvesPlace (world : World) (environment : Environment) : Place → Address → Authority → Prop where
  | localSlot {place binding address authority} : environment.Selects place.localSlot binding →
      ResolvesProjections world environment binding.address binding.authority place.projections address authority →
      ResolvesPlace world environment place address authority

/-- Unsafe pointee inputs resolve from the same actual bindings and ordinary
projection relation. Physical pointer matching is a later, independent check;
there is deliberately no pointer-to-owner constructor here. -/
inductive ResolvesResource (world : World) (environment : Environment) (custody : ClaimCustody) : ResolvedPlace → Prop where
  | binding {key binding} : environment.SelectsKey key binding →
      binding.authority.Custodied world custody → ResolvesResource world environment custody binding.place
  | project {source projections address authority} : ResolvesResource world environment custody source →
      ResolvesProjections world environment source.address source.authority projections address authority →
      authority.Custodied world custody → ResolvesResource world environment custody ⟨address,authority⟩
  | subplace {source address} : ResolvesResource world environment custody source → source.address.Prefix address →
      world.Located address → ResolvesResource world environment custody ⟨address,source.authority⟩

theorem ResolvesPlace.binding {world environment place address authority}
    (resolved : ResolvesPlace world environment place address authority) :
    ∃ binding ∈ environment, binding.key = .localSlot place.localSlot := by
  cases resolved with
  | localSlot selected _ => exact ⟨_,selected.1,selected.2.1⟩

mutual
  inductive Matches (program : Language.Program) (world : World) : Address → Pattern → Prop where
    | wildcard {address} : Matches program world address .wildcard
    | bind {address localSlot value} : world.Stores address value → value.Initialized → Matches program world address (.bind localSlot)
    | scalar {address expected value} : world.Stores address value → value.Initialized →
        value.head = .scalar expected → (∀ width bits, expected ≠ .floating width bits) →
        Matches program world address (.scalar expected)
    | unit {address value} : world.Stores address value → value.head = .unit → value.Initialized →
        Matches program world address .unit
    | tuple {address value fields} : world.Stores address value → value.head = .tuple → value.shellLive = true →
        value.fields.length = fields.length → MatchesFields program world address 0 fields →
        Matches program world address (.tuple fields)
    | array {address value fields} : world.Stores address value → value.head = .array → value.Initialized →
        value.fields.length = fields.length → MatchesFields program world address 0 fields →
        Matches program world address (.array fields)
    | constructor {address value variant fields} : world.Stores address value → value.head = .constructor variant →
        value.shellLive = true → value.fields.length = fields.length → MatchesFields program world address 0 fields →
        Matches program world address (.constructor variant fields)
    | reference {address value id loan mode pattern} : world.Stores address value → value.head = .reference id →
        world.loans.get id = some loan → loan.live = true → loan.mode = mode →
        Matches program world loan.referent pattern → Matches program world address (.reference mode pattern)

  inductive MatchesFields (program : Language.Program) (world : World) : Address → Nat → List Pattern → Prop where
    | nil {address offset} : MatchesFields program world address offset []
    | cons {address offset first rest} : Matches program world (address.child offset) first →
        MatchesFields program world address (offset+1) rest → MatchesFields program world address offset (first :: rest)
end

def FirstArm (program : Language.Program) (world : World) (address : Address) (arms : List Arm) (arm : Arm) : Prop :=
  ∃ skipped rest, arms = skipped ++ arm :: rest ∧ Matches program world address arm.pattern ∧
    ∀ earlier ∈ skipped, ¬ Matches program world address earlier.pattern

inductive PatternAction where
  | bind (localSlot : Local) (address : Address) (authority : Authority) (access : Access)
  | consumeShell (address : Address) (authority : Authority)
  | dispose (address : Address) (authority : Authority)
  deriving Repr, Inhabited

structure PatternActions where
  shells : List PatternAction := []
  bindings : List PatternAction := []
  cleanup : List PatternAction := []
  deriving Repr, Inhabited

mutual
  inductive PatternPlan (program : Language.Program) (world : World) :
      Address → Authority → Access → Pattern → PatternActions → Prop where
    | wildcardOwned {address authority} : PatternPlan program world address authority .owned .wildcard
        ⟨[],[],[.dispose address authority]⟩
    | wildcardBorrowed {address authority access} : access ≠ .owned →
        PatternPlan program world address authority access .wildcard ⟨[],[],[]⟩
    | bind {address authority access localSlot} : PatternPlan program world address authority access (.bind localSlot)
        ⟨[],[.bind localSlot address authority access],[]⟩
    | scalarOwned {address authority scalar} : PatternPlan program world address authority .owned (.scalar scalar)
        ⟨[],[],[.dispose address authority]⟩
    | scalarBorrowed {address authority access scalar} : access ≠ .owned →
        PatternPlan program world address authority access (.scalar scalar) ⟨[],[],[]⟩
    | unitOwned {address authority} : PatternPlan program world address authority .owned .unit
        ⟨[],[],[.dispose address authority]⟩
    | unitBorrowed {address authority access} : access ≠ .owned →
        PatternPlan program world address authority access .unit ⟨[],[],[]⟩
    | aggregate {address authority access pattern fields actions} :
        (pattern = .tuple fields ∨ pattern = .array fields ∨ ∃ id, pattern = .constructor id fields) →
        PatternPlans program world address authority access 0 fields actions →
        PatternPlan program world address authority access pattern
          ⟨(if access = .owned then [.consumeShell address authority] else []) ++ actions.shells,
            actions.bindings, actions.cleanup ++ (if access = .owned then [.dispose address authority] else [])⟩
    | reference {address authority access pattern mode value id loan actions view nestedAccess} : world.Stores address value →
        value.head = .reference id → world.loans.get id = some loan → loan.mode = mode → loan.live = true →
        value.Initialized → Permitted world (authority.lend access) .shared address →
        ReferenceView world address (authority.lend access) id mode view nestedAccess →
        PatternPlan program world loan.referent view nestedAccess pattern actions →
        PatternPlan program world address authority access (.reference mode pattern)
          ⟨actions.shells,actions.bindings,actions.cleanup ++ (if access = .owned then [.dispose address authority] else [])⟩

  inductive PatternPlans (program : Language.Program) (world : World) :
      Address → Authority → Access → Nat → List Pattern → PatternActions → Prop where
    | nil {address authority access index} : PatternPlans program world address authority access index [] ⟨[],[],[]⟩
    | cons {address authority access index pattern rest first later} :
        PatternPlan program world (address.child index) authority access pattern first →
        PatternPlans program world address authority access (index+1) rest later →
        PatternPlans program world address authority access index (pattern :: rest)
          ⟨first.shells ++ later.shells,first.bindings ++ later.bindings,later.cleanup ++ first.cleanup⟩
end

inductive InvocationOrigin where
  | receiver | capture (index : Nat) | argument (index : Nat) | obligation (identity : Identity)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- A raw-storage formal denotes a logical storage obligation, not an invented
source local or an initialized value of its pointee type. -/
inductive InputFormal where
  | resident (localSlot : Local)
  | storage (identity : Identity) (type : Term)
  | allocation (identity : Identity) (type : Term)
  | loan (identity : Identity) (type : Term)
  deriving Repr, Inhabited

instance : Coe Local InputFormal := ⟨InputFormal.resident⟩

def InputFormal.key : InputFormal → BindingKey
  | .resident localSlot => .localSlot localSlot.id
  | .storage identity _ | .allocation identity _ | .loan identity _ => .resourceInput identity

def InputFormal.type : InputFormal → Term
  | .resident localSlot => localSlot.type
  | .storage _ type | .allocation _ type | .loan _ type => type

def InputFormal.mutable : InputFormal → Bool
  | .resident localSlot => localSlot.mutable
  | .storage _ _ | .allocation _ _ | .loan _ _ => true

def InputFormal.IsResident : InputFormal → Prop
  | .resident _ => True
  | .storage _ _ | .allocation _ _ | .loan _ _ => False

def InputFormal.resident? : InputFormal → Option Local
  | .resident localSlot => some localSlot
  | .storage _ _ | .allocation _ _ | .loan _ _ => none

structure InvocationInput where
  origin : InvocationOrigin
  formal : InputFormal
  storage : Address
  authority : Authority
  access : Access
  deriving Repr, Inhabited

def InvocationInput.binding (input : InvocationInput) : StorageBinding :=
  ⟨input.formal.key,input.storage,input.authority⟩

/-- Only owned resident inputs clear their old contents. Passing allocation
or storage-loan custody preserves the resident and is not a resident write. -/
def InvocationInput.clearedStorage (input : InvocationInput) : List Address :=
  match input.formal with
  | .resident _ => if input.access = .owned then [input.storage] else []
  | _ => []

theorem InvocationInput.mem_clearedStorage {input : InvocationInput} {address : Address} :
    address ∈ input.clearedStorage ↔ input.formal.IsResident ∧ input.access = .owned ∧ address = input.storage := by
  cases input with
  | mk origin formal storage authority access =>
      cases formal <;> by_cases owned : access = .owned <;>
        simp [InvocationInput.clearedStorage,InputFormal.IsResident,owned]


/-- Readiness belongs to the actual common input, not to an imagined
resident for an erased port. Allocation and raw-loan handoffs preserve their
existing child-reference identities and therefore do not require exclusive
access to a currently borrowed T. -/
def InvocationInput.ReadyFor (program : RuntimeProgram) (world : World)
    (footprint : List Address) (input : InvocationInput) : Prop :=
  match input.formal with
  | .resident localSlot => ∃ value, world.Stores input.storage value ∧ value.Initialized ∧
      value.type = localSlot.type ∧ value.HandoffReady program world input.access footprint ∧
      Permitted world input.authority input.access input.storage
  | .storage _ type => AddressType program.declarations world input.storage type ∧
      world.Located input.storage ∧ Permitted world input.authority input.access input.storage
  | .allocation _ type => input.access = .owned ∧ AddressType program.declarations world input.storage type ∧
      AllocationClaim world input.authority input.storage ∧
      ((∃ identity, input.authority = .loan identity) ∨
        ∃ backing guard, input.authority = .guarded backing guard ∧
          Permitted world input.authority .owned input.storage)
  | .loan _ type => input.access = .owned ∧ AddressType program.declarations world input.storage type ∧
      ∃ identity loan, world.loans.get identity = some loan ∧ loan.live = true ∧
        loan.kind = .storageBorrow ∧ loan.referent = input.storage ∧
        ((input.authority = .loan identity ∧ loan.mode = .unique) ∨
          ∃ backing, input.authority = .shared backing ∧ backing.parentLoan = some identity ∧ loan.mode = .shared)

/-- A single input is the singleton specialization of the same batch
readiness contract. No independent capture or argument readiness is inferred. -/
abbrev InvocationInput.Ready (program : RuntimeProgram) (world : World) (input : InvocationInput) : Prop :=
  input.ReadyFor program world input.clearedStorage

/-- Every input is ready against the writes of the actual entire pending
batch. Lent resident storage itself is retained, in addition to the support
of its value; two ownership transfers cannot consume overlapping sources. -/
def InvocationInputsReadyFor (program : RuntimeProgram) (world : World)
    (footprint : List Address) (inputs : List InvocationInput) : Prop :=
  (∀ address ∈ inputs.flatMap InvocationInput.clearedStorage, address ∈ footprint) ∧
  (inputs.flatMap InvocationInput.clearedStorage).Pairwise (fun first last => ¬ first.Overlaps last) ∧
  ∀ input ∈ inputs, input.ReadyFor program world footprint ∧
    (input.formal.IsResident → input.access ≠ .owned →
      ∀ source ∈ footprint, ¬ input.storage.Overlaps source)

abbrev InvocationInputsReady (program : RuntimeProgram) (world : World)
    (inputs : List InvocationInput) : Prop :=
  InvocationInputsReadyFor program world (inputs.flatMap InvocationInput.clearedStorage) inputs

theorem InvocationInput.ReadyFor.restrict {program : RuntimeProgram} {world : World}
    {input : InvocationInput} {all kept : List Address}
    (ready : input.ReadyFor program world all)
    (included : ∀ address ∈ kept, address ∈ all) : input.ReadyFor program world kept := by
  cases input with
  | mk origin formal storage authority access =>
    cases formal with
    | resident localSlot =>
      obtain ⟨value,stored,initialized,type,resources,permitted⟩ := ready
      exact ⟨value,stored,initialized,type,resources.restrict included,permitted⟩
    | storage _ _ | allocation _ _ | loan _ _ => exact ready

theorem InvocationInputsReadyFor.member {program : RuntimeProgram} {world : World}
    {inputs : List InvocationInput} {footprint : List Address}
    (ready : InvocationInputsReadyFor program world footprint inputs)
    {input : InvocationInput} (member : input ∈ inputs) : input.Ready program world :=
  (ready.2.2 input member).1.restrict
    (fun address present => ready.1 address (List.mem_flatMap.mpr ⟨input,member,present⟩))

theorem InvocationInput.ReadyFor.resident {program : RuntimeProgram} {world : World}
    {input : InvocationInput} {footprint : List Address} {value : Value}
    (ready : input.ReadyFor program world footprint) (resident : input.formal.IsResident)
    (stored : world.Stores input.storage value) :
    value.Initialized ∧ value.type = input.formal.type ∧
      value.HandoffReady program world input.access footprint ∧
      Permitted world input.authority input.access input.storage := by
  cases input with
  | mk origin formal storage authority access =>
    cases formal with
    | resident localSlot =>
      obtain ⟨actual,selected,initialized,type,resources,permitted⟩ := ready
      have same := Option.some.inj (stored.symm.trans selected)
      subst actual
      exact ⟨initialized,type,resources,permitted⟩
    | storage _ _ | allocation _ _ | loan _ _ => cases resident

/-- Explicit unsafe inputs must be resolved from the caller's actual domain.
The chosen formal identifies a contract port, not a fresh allocation identity. -/
inductive ResourceInputs (program : Language.Program) (world : World) (environment : Environment) (custody : ClaimCustody) :
    List InvocationInput → Prop where
  | nil : ResourceInputs program world environment custody []
  | cons {identity type place access inputs} : ResolvesResource world environment custody place →
      AddressType program world place.address type → ResourceInputs program world environment custody inputs →
      ResourceInputs program world environment custody
        (⟨.obligation identity,.storage identity type,place.address,place.authority,access⟩ :: inputs)
  | allocation {identity type place inputs} : ResolvesResource world environment custody place →
      AllocationClaim world place.authority place.address → AddressType program world place.address type →
      ResourceInputs program world environment custody inputs →
      ResourceInputs program world environment custody
        (⟨.obligation identity,.allocation identity type,place.address,place.authority,.owned⟩ :: inputs)
  | loan {identity type place inputs} : ResolvesResource world environment custody place →
      AddressType program world place.address type → ResourceInputs program world environment custody inputs →
      ResourceInputs program world environment custody
        (⟨.obligation identity,.loan identity type,place.address,place.authority,.owned⟩ :: inputs)

/-- Resource preconditions and key uniqueness are checked on the original
invocation world and its original ordered inputs, before any preparation.
An arbitrary unsafe predicate is never transported across internal mutation. -/
def IncomingResources (program : Program) (function : Function) (world : World)
    (inputs : List InvocationInput) : Prop :=
  (inputs.map (fun input => input.formal.key)).Nodup ∧
  match program.unsafeContracts function.declaration with
  | none => ∀ input ∈ inputs, input.formal.IsResident ∨ ∃ index, input.origin = .capture index
  | some contract => contract.inputs world (inputs.map InvocationInput.binding)

/-- Invocation lending owns an ordinary reference handle. Its location and
loan identity are the same ones consumed by normal reference cleanup. -/
structure InvocationLease where
  handle : Address
  loan : Identity
  deriving Repr, Inhabited

/-- Captured storage, whole receivers and contextual witnesses share this
producer. A lent view creates a real child loan in the supplied activation;
it is not an authority wrapper that leaves competing parent access enabled. -/
inductive LendsResident (program : RuntimeProgram) (activation scope region : Identity) :
    World → Address → Authority → Access → Option InvocationLease → Authority → World → Prop where
  | owned {world address authority} :
      LendsResident program activation scope region world address authority .owned none authority world
  | lent {before address authority access mode value handle allocated after layout sourceRegion} :
      (access = .shared ∧ mode = .shared ∨ access = .unique ∧ mode = .unique) →
      before.Stores address value →
      authority.BorrowRegion before address sourceRegion →
      Allocates program.declarations before (.temporary activation scope) region
        (.reference mode (.runtimeRegion sourceRegion) value.type) layout true handle allocated →
      FormsLoan program .invocation allocated authority mode sourceRegion address handle after →
      LendsResident program activation scope region before address authority access
        (some ⟨handle,allocated.nextLoan⟩) (.loan allocated.nextLoan) after

/-- Captures and ordinary arguments bind through the same storage relation.
Lent capture storage remains the original object, including zero-sized fields;
the fresh reference owner is only the lifetime witness for that access. -/
inductive BindsInputAt (program : RuntimeProgram) (recipient : ClaimCustody) (activation scope region : Identity) :
    World → InvocationInput → Binding → World → Prop where
  | lent {before input value lease authority after} : input.Ready program before → input.access ≠ .owned →
      input.formal.IsResident →
      before.Stores input.storage value → value.Initialized → value.type = input.formal.type →
      Permitted before input.authority input.access input.storage →
      LendsResident program activation scope region before input.storage input.authority input.access lease authority after →
      BindsInputAt program recipient activation scope region before input
        ⟨input.formal.key,input.storage,authority⟩ after
  | owned {before input address allocated after layout value} : input.Ready program before → input.access = .owned →
      input.formal.IsResident →
      before.Stores input.storage value → value.type = input.formal.type →
      Allocates program.declarations before (.localSlot activation scope) region input.formal.type layout input.formal.mutable address allocated →
      Transfers program allocated input.authority input.storage address after →
      BindsInputAt program recipient activation scope region before input ⟨input.formal.key,address,.owner⟩ after
  | storage {before input identity type loan after} : input.Ready program before → input.formal = .storage identity type →
      AddressType program.declarations before input.storage type →
      ClaimsStorage recipient before input.authority input.access input.storage loan after →
      BindsInputAt program recipient activation scope region before input
        ⟨.resourceInput identity,input.storage,ClaimedAuthority input.access loan⟩ after
  | allocation {before input identity type after} : input.Ready program before → input.formal = .allocation identity type →
      input.access = .owned → AddressType program.declarations before input.storage type →
      TransfersAllocation recipient before ⟨input.storage,input.authority⟩ after →
      BindsInputAt program recipient activation scope region before input
        ⟨.resourceInput identity,input.storage,input.authority⟩ after
  | guardedAllocation {before input identity type backing guard loan after} :
      input.Ready program before → input.formal = .allocation identity type → input.access = .owned →
      input.authority = .guarded backing guard → AddressType program.declarations before input.storage type →
      ClaimsAllocation recipient before input.authority input.storage loan after →
      BindsInputAt program recipient activation scope region before input
        ⟨.resourceInput identity,input.storage,.loan loan⟩ after
  | loan {before input identity type after} : input.Ready program before → input.formal = .loan identity type →
      input.access = .owned → AddressType program.declarations before input.storage type →
      TransfersStorageLoan recipient before ⟨input.storage,input.authority⟩ after →
      BindsInputAt program recipient activation scope region before input
        ⟨.resourceInput identity,input.storage,input.authority⟩ after

/-- The source resident and its real lending permissions are ready, but the
positively validated temporary handle has no physical extent. The failure
occurs before allocating that handle or creating its child loan. -/
inductive LendsResidentExhausted (program : RuntimeProgram) (region : Identity) :
    World → Address → Authority → Access → Prop where
  | lent {before address authority access mode value sourceRegion layout} :
      (access = .shared ∧ mode = .shared ∨ access = .unique ∧ mode = .unique) →
      before.Stores address value → value.Initialized →
      value.ResourcesAccessible program before access → Permitted before authority access address →
      authority.BorrowRegion before address sourceRegion →
      AllocationExhausted program.declarations before region
        (.reference mode (.runtimeRegion sourceRegion) value.type) layout →
      LendsResidentExhausted program region before address authority access

/-- Erased ports never allocate resident storage, so have no fabricated
allocation-failure case. Both resident modes consume the same original input
readiness as successful binding. -/
inductive BindsInputExhausted (program : RuntimeProgram) (region : Identity) : World → InvocationInput → Prop where
  | owned {before input layout} : input.Ready program before → input.access = .owned → input.formal.IsResident →
      AllocationExhausted program.declarations before region input.formal.type layout →
      BindsInputExhausted program region before input
  | lent {before input} : input.Ready program before → input.formal.IsResident →
      LendsResidentExhausted program region before input.storage input.authority input.access →
      BindsInputExhausted program region before input

inductive PreparationOutcome where
  | complete | exhausted
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Resident locals and erased resource ports retain their distinct keys in
the one binding domain. An erased port never acquires a fictitious local ID. -/
theorem BindsInputAt.binding_key {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {before after : World} {input : InvocationInput} {binding : Binding}
    (bound : BindsInputAt program recipient activation scope region before input binding after) :
    binding.key = input.formal.key := by
  cases bound with
  | lent | owned => rfl
  | storage _ formal _ _ => simp only [formal,InputFormal.key]
  | allocation _ formal _ _ _ => simp only [formal,InputFormal.key]
  | guardedAllocation _ formal _ _ _ _ => simp only [formal,InputFormal.key]
  | loan _ formal _ _ _ => simp only [formal,InputFormal.key]

abbrev BindsInput (program : RuntimeProgram) (activation scope region : Identity) :=
  BindsInputAt program (.activation activation) activation scope region

/-- Pattern borrowing constructs a reference value, unlike a lent invocation
input, whose formal still denotes the original resident type and storage. -/
inductive BindsPattern (program : RuntimeProgram) (activation scope region : Identity) :
    World → Local → Address → Authority → Access → Binding → World → Prop where
  | owned {before localSlot source authority binding after} :
      BindsInput program activation scope region before
        ⟨.argument 0,.resident localSlot,source,authority,.owned⟩ binding after →
      BindsPattern program activation scope region before localSlot source authority .owned binding after
  | borrowed {before localSlot source authority mode loanRegion value address allocated after layout} :
      before.Stores source value → localSlot.type = .reference mode (.runtimeRegion loanRegion) value.type →
      Allocates program.declarations before (.localSlot activation scope) region localSlot.type layout localSlot.mutable address allocated →
      Borrows program allocated authority mode loanRegion source address after →
      BindsPattern program activation scope region before localSlot source authority
        (if mode = .shared then .shared else .unique) ⟨localSlot.id,address,.owner⟩ after

inductive BindsInputsAttemptFor (program : RuntimeProgram) (recipient : ClaimCustody)
    (activation scope region : Identity) (footprint : List Address) :
    World → List InvocationInput → Environment → World → PreparationOutcome → Prop where
  | nil {world} : BindsInputsAttemptFor program recipient activation scope region footprint world [] [] world .complete
  | cons {before input rest binding bindings middle after outcome} :
      InvocationInputsReadyFor program before footprint (input :: rest) →
      BindsInputAt program recipient activation scope region before input binding middle →
      BindsInputsAttemptFor program recipient activation scope region footprint middle rest bindings after outcome →
      BindsInputsAttemptFor program recipient activation scope region footprint before (input :: rest) (binding :: bindings) after outcome
  | exhausted {before input rest} :
      InvocationInputsReadyFor program before footprint (input :: rest) →
      BindsInputExhausted program region before input →
      BindsInputsAttemptFor program recipient activation scope region footprint before (input :: rest) [] before .exhausted

/-- Success is the complete specialization of the one outcome-indexed fold.
An exhausted derivation retains every earlier whole-pending readiness guard. -/
abbrev BindsInputsFor (program : RuntimeProgram) (recipient : ClaimCustody)
    (activation scope region : Identity) (footprint : List Address)
    (before : World) (inputs : List InvocationInput) (bindings : Environment) (after : World) : Prop :=
  BindsInputsAttemptFor program recipient activation scope region footprint before inputs bindings after .complete

/-- Eliminate the complete index of the actual attempt relation. This is a
derived proof rule, not a second successful binder or a failure-erasing cast. -/
@[elab_as_elim] theorem BindsInputsFor.inductionOn {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {footprint : List Address}
    {motive : ∀ before inputs bindings after,
      BindsInputsFor program recipient activation scope region footprint before inputs bindings after → Prop}
    {before : World} {inputs : List InvocationInput} {bindings : Environment} {after : World}
    (bound : BindsInputsFor program recipient activation scope region footprint before inputs bindings after)
    (nil : ∀ world, motive world [] [] world .nil)
    (cons : ∀ {before input rest binding bindings middle after},
      ∀ (ready : InvocationInputsReadyFor program before footprint (input :: rest))
        (head : BindsInputAt program recipient activation scope region before input binding middle)
        (tail : BindsInputsFor program recipient activation scope region footprint middle rest bindings after),
      motive middle rest bindings after tail →
        motive before (input :: rest) (binding :: bindings) after (.cons ready head tail)) :
    motive before inputs bindings after bound := by
  have complete : ∀ {before inputs bindings after outcome},
      ∀ (attempted : BindsInputsAttemptFor program recipient activation scope region footprint before inputs bindings after outcome)
        (done : outcome = .complete), motive before inputs bindings after (by cases done; exact attempted) := by
    intro before inputs bindings after outcome attempted
    induction attempted with
    | nil => intro _; exact nil _
    | cons ready head tail ih =>
      intro done
      cases done
      exact cons ready head tail (ih rfl)
    | exhausted => intro impossible; cases impossible
  exact complete bound rfl

/-- The successful public fold fixes the original clear footprint once.
Its recursive derivation and every successful prefix use that same footprint. -/
abbrev BindsInputsAt (program : RuntimeProgram) (recipient : ClaimCustody)
    (activation scope region : Identity) (before : World) (inputs : List InvocationInput)
    (bindings : Environment) (after : World) : Prop :=
  BindsInputsFor program recipient activation scope region
    (inputs.flatMap InvocationInput.clearedStorage) before inputs bindings after

abbrev BindsInputs (program : RuntimeProgram) (activation scope region : Identity) :=
  BindsInputsAt program (.activation activation) activation scope region

/-- The actual fold, including captures, supplies whole-batch readiness at
its source world. Earlier outputs are constrained by every later clear. -/
theorem BindsInputsFor.ready {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {before after : World}
    {inputs : List InvocationInput} {bindings : Environment} {footprint : List Address}
    (bound : BindsInputsFor program recipient activation scope region footprint before inputs bindings after) :
    InvocationInputsReadyFor program before footprint inputs := by
  cases bound with
  | nil => exact ⟨by simp, .nil, by intro input member; cases member⟩
  | cons ready _ _ => exact ready

theorem BindsInputsFor.resident_handoffReady {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {before after : World}
    {inputs : List InvocationInput} {bindings : Environment} {footprint : List Address}
    (bound : BindsInputsFor program recipient activation scope region footprint before inputs bindings after)
    {input : InvocationInput} {value : Value} (member : input ∈ inputs)
    (resident : input.formal.IsResident) (stored : before.Stores input.storage value) :
    value.HandoffReady program before input.access footprint :=
  ((bound.ready.2.2 input member).1.resident resident stored).2.2.1

def HomeOwnedByActivation (home : Home) (activation : Identity) : Prop :=
  (∃ scope, home = .localSlot activation scope) ∨ ∃ scope, home = .temporary activation scope

def HomeOwnedByScope (home : Home) (activation scope : Identity) : Prop :=
  home = .localSlot activation scope ∨ home = .temporary activation scope

def OwnedByActivation (root : Root) (activation : Identity) : Prop :=
  HomeOwnedByActivation root.home activation

def OwnedByScope (root : Root) (activation scope : Identity) : Prop :=
  HomeOwnedByScope root.home activation scope

def NewestFirst (world : World) (roots : List Identity) : Prop :=
  roots.Nodup ∧ ∀ (i j : Nat) a b left right, roots[i]? = some a → roots[j]? = some b →
    world.roots.get a = some left → world.roots.get b = some right → i < j → right.born ≤ left.born

/-- Cleanup selects exact roots from the one current storage table, in reverse
creation order. Scope, activation, label and handler selection specialize this
same relation; the predicate does not supply an independent ownership table. -/
def RootsWhere (world : World) (selected : Identity → Root → Prop) (roots : List Identity) : Prop :=
  NewestFirst world roots ∧ ∀ id, id ∈ roots ↔ ∃ root, world.roots.get id = some root ∧ selected id root

def ScopeRoots (world : World) (activation scope : Identity) (kept : List Identity) (roots : List Identity) : Prop :=
  RootsWhere world (fun id root => root.live = true ∧ OwnedByScope root activation scope ∧ id ∉ kept) roots

def ActivationRoots (world : World) (activation : Identity) (kept : List Identity) (roots : List Identity) : Prop :=
  RootsWhere world (fun id root => root.live = true ∧ OwnedByActivation root activation ∧ id ∉ kept) roots

theorem borrowed_capture_keeps_storage {program : RuntimeProgram} {activation scope region world input binding after}
    (borrowed : input.access ≠ .owned)
    (bound : BindsInput program activation scope region world input binding after) :
    binding.address = input.storage := by
  cases bound with
  | lent => rfl
  | owned _ owned _ _ _ _ _ => exact False.elim (borrowed owned)
  | storage => rfl
  | allocation => rfl
  | guardedAllocation => rfl
  | loan => rfl

theorem BindsInputAt.ready {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {before after : World} {input : InvocationInput} {binding : Binding}
    (bound : BindsInputAt program recipient activation scope region before input binding after) :
    input.Ready program before := by
  cases bound <;> assumption

end Glorious.Language.Kernel
