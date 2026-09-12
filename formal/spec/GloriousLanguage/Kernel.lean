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

structure Program where
  declarations : Language.Program
  functions : List Function

def Program.function (program : Program) (id : DeclId) : Option Function :=
  program.functions.find? (fun function => function.declaration == id)

/-- The body/declaration boundary, shared by specification admission and
resident typing. This is independent of execution or resource soundness. -/
def BodyInventory (program : Program) : Prop :=
  (program.functions.map (·.declaration)).Nodup ∧
  (∀ function ∈ program.functions, ∃ declaration, program.declarations.function function.declaration = some declaration ∧
    function.signature = declaration.signature ∧ function.parameters.map (·.id) = declaration.parameters ∧
    function.captures.map (·.type) = declaration.captures) ∧
  (∀ declaration anchor, program.declarations.function declaration.header.id = some declaration → declaration.origin = .source anchor →
    ∃ function ∈ program.functions, function.declaration = declaration.header.id) ∧
  (∀ function ∈ program.functions, function.Lexical)

structure Binding where
  localSlot : Identity
  address : Address
  authority : Authority
  deriving Repr, Inhabited

abbrev Environment := List Binding

/-- Ordinary places and index operands use the same unique lexical binding
selection. An ambiguous environment supplies no usable binding. -/
def Environment.Selects (environment : Environment) (localSlot : Identity) (binding : Binding) : Prop :=
  binding ∈ environment ∧ binding.localSlot = localSlot ∧
    ∀ other ∈ environment, other.localSlot = localSlot → other = binding

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

theorem ResolvesPlace.binding {world environment place address authority}
    (resolved : ResolvesPlace world environment place address authority) :
    ∃ binding ∈ environment, binding.localSlot = place.localSlot := by
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
  | receiver | capture (index : Nat) | argument (index : Nat)
  deriving DecidableEq, BEq, Repr, Inhabited

structure InvocationInput where
  origin : InvocationOrigin
  formal : Local
  storage : Address
  authority : Authority
  access : Access
  deriving Repr, Inhabited

/-- Invocation lending owns an ordinary reference handle. Its location and
loan identity are the same ones consumed by normal reference cleanup. -/
structure InvocationLease where
  handle : Address
  loan : Identity
  deriving Repr, Inhabited

/-- Captured storage, whole receivers and contextual witnesses share this
producer. A lent view creates a real child loan in the supplied activation;
it is not an authority wrapper that leaves competing parent access enabled. -/
inductive LendsResident (program : Language.Program) (activation scope region : Identity) :
    World → Address → Authority → Access → Option InvocationLease → Authority → World → Prop where
  | owned {world address authority} :
      LendsResident program activation scope region world address authority .owned none authority world
  | lent {before address authority access mode value handle allocated after layout} :
      (access = .shared ∧ mode = .shared ∨ access = .unique ∧ mode = .unique) →
      before.Stores address value →
      Allocates program before (.temporary activation scope) region
        (.reference mode (.runtimeRegion region) value.type) layout true handle allocated →
      FormsLoan program .invocation allocated authority mode region address handle after →
      LendsResident program activation scope region before address authority access
        (some ⟨handle,allocated.nextLoan⟩) (.loan allocated.nextLoan) after

/-- Captures and ordinary arguments bind through the same storage relation.
Lent capture storage remains the original object, including zero-sized fields;
the fresh reference owner is only the lifetime witness for that access. -/
inductive BindsInput (program : Language.Program) (activation scope region : Identity) :
    World → InvocationInput → Binding → World → Prop where
  | lent {before input value lease authority after} : input.access ≠ .owned →
      before.Stores input.storage value → value.Initialized → value.type = input.formal.type →
      Permitted before input.authority input.access input.storage →
      LendsResident program activation scope region before input.storage input.authority input.access lease authority after →
      BindsInput program activation scope region before input
        ⟨input.formal.id,input.storage,authority⟩ after
  | owned {before input address allocated after layout value} : input.access = .owned →
      before.Stores input.storage value → value.type = input.formal.type →
      Allocates program before (.localSlot activation scope) region input.formal.type layout input.formal.mutable address allocated →
      Transfers program allocated input.authority input.storage address after →
      BindsInput program activation scope region before input ⟨input.formal.id,address,.owner⟩ after

/-- Pattern borrowing constructs a reference value, unlike a lent invocation
input, whose formal still denotes the original resident type and storage. -/
inductive BindsPattern (program : Language.Program) (activation scope region : Identity) :
    World → Local → Address → Authority → Access → Binding → World → Prop where
  | owned {before localSlot source authority binding after} :
      BindsInput program activation scope region before
        ⟨.argument 0,localSlot,source,authority,.owned⟩ binding after →
      BindsPattern program activation scope region before localSlot source authority .owned binding after
  | borrowed {before localSlot source authority mode loanRegion value address allocated after layout} :
      before.Stores source value → localSlot.type = .reference mode (.runtimeRegion loanRegion) value.type →
      Allocates program before (.localSlot activation scope) region localSlot.type layout localSlot.mutable address allocated →
      Borrows program allocated authority mode loanRegion source address after →
      BindsPattern program activation scope region before localSlot source authority
        (if mode = .shared then .shared else .unique) ⟨localSlot.id,address,.owner⟩ after

inductive BindsInputs (program : Language.Program) (activation scope region : Identity) :
    World → List InvocationInput → Environment → World → Prop where
  | nil {world} : BindsInputs program activation scope region world [] [] world
  | cons {before input rest binding bindings middle after} : BindsInput program activation scope region before input binding middle →
      BindsInputs program activation scope region middle rest bindings after →
      BindsInputs program activation scope region before (input :: rest) (binding :: bindings) after

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

def ScopeRoots (world : World) (activation scope : Identity) (kept : List Identity) (roots : List Identity) : Prop :=
  NewestFirst world roots ∧ ∀ id, id ∈ roots ↔
    ∃ root, world.roots.get id = some root ∧ root.live = true ∧ OwnedByScope root activation scope ∧ id ∉ kept

def ActivationRoots (world : World) (activation : Identity) (kept : List Identity) (roots : List Identity) : Prop :=
  NewestFirst world roots ∧ ∀ id, id ∈ roots ↔
    ∃ root, world.roots.get id = some root ∧ root.live = true ∧ OwnedByActivation root activation ∧ id ∉ kept

theorem borrowed_capture_keeps_storage {program : Language.Program} {activation scope region world input binding after}
    (borrowed : input.access ≠ .owned)
    (bound : BindsInput program activation scope region world input binding after) :
    binding.address = input.storage := by
  cases bound with
  | lent => rfl
  | owned owned _ _ _ _ => exact False.elim (borrowed owned)

end Glorious.Language.Kernel
