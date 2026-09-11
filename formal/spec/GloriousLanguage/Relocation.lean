import GloriousLanguage.Atoms

/-! Snapshot relocation preserves holes and the alias graph. The finite
fresh maps below relocate storage identities, not source binding identities.
Unselected (in particular caller-owned borrowed) storage remains identical. -/
namespace Glorious.Language.Execution

open Kernel

structure Relocation where
  roots : List Identity
  loans : List Identity
  regions : List Identity
  activations : List Identity
  scopes : List Identity
  handlers : List Identity
  rootBase : Identity
  ownerBase : Identity
  loanBase : Identity
  regionBase : Identity
  activationBase : Identity
  scopeBase : Identity
  handlerBase : Identity
  physical : Table Nat
  deriving Repr, Inhabited

def relocateId (selected : List Identity) (base id : Identity) : Identity :=
  if id ∈ selected then base + id else id

def Relocation.root (map : Relocation) := relocateId map.roots map.rootBase
def Relocation.loan (map : Relocation) := relocateId map.loans map.loanBase
def Relocation.region (map : Relocation) := relocateId map.regions map.regionBase
def Relocation.activation (map : Relocation) := relocateId map.activations map.activationBase
def Relocation.scope (map : Relocation) := relocateId map.scopes map.scopeBase
def Relocation.handler (map : Relocation) := relocateId map.handlers map.handlerBase

def Relocation.address (map : Relocation) (address : Address) : Address :=
  { address with root := map.root address.root }

def Relocation.pointer (map : Relocation) (pointer : RawPointer) : RawPointer :=
  match pointer.allocation with
  | none => pointer
  | some root =>
    if root ∈ map.roots then
      match map.physical.get root with
      | none => pointer
      | some base => { pointer with address := base+pointer.offset, allocation := some (map.root root) }
    else pointer

def Relocation.term (map : Relocation) : Term → Term
  | .runtimeRegion id => .runtimeRegion (map.region id)
  | .tuple fields => .tuple (fields.map map.term)
  | .array a b => .array (map.term a) (map.term b)
  | .reference mode a b => .reference mode (map.term a) (map.term b)
  | .rawPointer mode a => .rawPointer mode (map.term a)
  | .nominal id arguments => .nominal id (arguments.map map.term)
  | .alias id arguments => .alias id (arguments.map map.term)
  | .callable id arguments => .callable id (arguments.map map.term)
  | .continuation a b c d q => .continuation (map.term a) (map.term b) (map.term c) (map.term d) q
  | .label a b c => .label (map.term a) (map.term b) (map.term c)
  | .environment a b => .environment (map.term a) (map.term b)
  | .available a b => .available (map.term a) (map.term b)
  | .bindings a b arguments => .bindings (map.term a) (map.term b) (arguments.map map.term)
  | .effect id arguments => .effect id (arguments.map map.term)
  | .row instances tails => .row (instances.map map.term) (tails.map map.term)
  | .projection trait member owners items kind => .projection trait member (owners.map map.term) (items.map map.term) kind
  | .constantTuple fields => .constantTuple (fields.map map.term)
  | .constantConstructor id arguments fields => .constantConstructor id (arguments.map map.term) (fields.map map.term)
  | term => term

def Relocation.constraint (map : Relocation) : Constraint → Constraint
  | .equal a b => .equal (map.term a) (map.term b)
  | .outlives a b => .outlives (map.term a) (map.term b)
  | .typeOutlives a b => .typeOutlives (map.term a) (map.term b)
  | .rowIncludes a b => .rowIncludes (map.term a) (map.term b)
  | .implements trait arguments negative => .implements trait (arguments.map map.term) negative
  | .use type quantity => .use (map.term type) quantity
  | .callable receiver arguments output effects unsafeAllowed =>
      .callable (map.term receiver) (arguments.map map.term) (map.term output) (map.term effects) unsafeAllowed
  | .runsIn receiver access arguments after unsafeAllowed =>
      .runsIn (map.term receiver) (map.term access) (arguments.map map.term) (map.term after) unsafeAllowed
  | .quantified binders requirements => .quantified binders (requirements.map map.constraint)

def Relocation.signature (map : Relocation) (signature : Signature) : Signature :=
  { signature with
    parameters := signature.parameters.map map.term
    result := map.term signature.result
    effects := map.term signature.effects
    constraints := signature.constraints.map map.constraint }

mutual
  def Relocation.code (map : Relocation) : Code → Code
    | .result value => .result value
    | .bind localSlot atom next => .bind (localSlot.mapTerms map.term) (atom.mapTerms map.term) (map.code next)
    | .evaluate localSlot value next => .evaluate (localSlot.mapTerms map.term) (map.code value) (map.code next)
    | .assign destination value next => .assign destination value (map.code next)
    | .discard value next => .discard value (map.code next)
    | .invoke localSlot call next => .invoke (localSlot.mapTerms map.term)
        { call with signature := map.signature call.signature } (map.code next)
    | .tail call => .tail { call with signature := map.signature call.signature }
    | .scope id body => .scope id (map.code body)
    | .label brand region result body => .label brand region (map.term result) (map.code body)
    | .choose subject arms => .choose subject (arms.map map.arm)
    | .handle id computation handler => .handle id (map.code computation) (map.handlerSyntax handler)
    | .test localSlot subject pattern id next => .test (localSlot.mapTerms map.term) subject (pattern.mapTerms map.term) id (map.code next)
    | .endLoan handle next => .endLoan handle (map.code next)
    | .unsafeScope body => .unsafeScope (map.code body)
    | .closeAvailable value next => .closeAvailable value (map.code next)
    | .reserve localSlot brand places next => .reserve (localSlot.mapTerms map.term) brand places (map.code next)
    | .abort => .abort

  def Relocation.arm (map : Relocation) : Arm → Arm
    | .clause pattern body => .clause (pattern.mapTerms map.term) (map.code body)

  def Relocation.operationArm (map : Relocation) : OperationArm → OperationArm
    | .clause id family item patterns continuation body => .clause id (family.map map.term) (item.map map.term)
        (patterns.map (Pattern.mapTerms map.term)) (continuation.map (Local.mapTerms map.term)) (map.code body)

  def Relocation.handlerSyntax (map : Relocation) : Handler → Handler
    | .attached result completion operations captures => .attached (map.term result) (completion.map map.arm)
        (operations.map map.operationArm) (captures.map (Capture.mapTerms map.term))
end

def Relocation.context (map : Relocation) (context : Context) : Context :=
  { context with
    environment := context.environment.map (fun binding => { binding with
      address := map.address binding.address
      authority := match binding.authority with | .owner => .owner | .loan id => .loan (map.loan id) })
    activation := map.activation context.activation
    scope := map.scope context.scope
    region := map.region context.region
    instantiation := { context.instantiation with
      regions := context.instantiation.regions.map (fun (lexical,runtime) => (lexical,map.region runtime)) } }

def Relocation.installed (map : Relocation) (handler : InstalledHandler) : InstalledHandler :=
  { handler with
    identity := map.handler handler.identity
    syntaxNode := map.handlerSyntax handler.syntaxNode
    environment := map.context handler.environment
    computation := map.context handler.computation
    outer := map.context handler.outer }

def Relocation.frame (map : Relocation) : Frame → Frame
  | .binding caller destination next => .binding (map.context caller) (map.address destination) (map.code next)
  | .activation caller activation region => .activation (map.context caller) (map.activation activation) (map.region region)
  | .scope outer scope region => .scope (map.context outer) (map.scope scope) (map.region region)
  | .label outer brand region result => .label (map.context outer) brand (map.region region) (map.term result)
  | .handler handler owns => .handler (map.installed handler) owns
  | .serviced handler owns clause continuation => .serviced (map.installed handler) owns (map.context clause) continuation
  | .completion handler owns clause => .completion (map.installed handler) owns (map.context clause)
  | .resumed caller => .resumed (map.context caller)
  | frame => frame

def Relocation.home (map : Relocation) : Home → Home
  | .localSlot activation scope => .localSlot (map.activation activation) (map.scope scope)
  | .temporary activation scope => .temporary (map.activation activation) (map.scope scope)
  | home => home

mutual
  def Relocation.value (map : Relocation) : Value → Value
    | .resident owner type head live fields => .resident (map.ownerBase + owner) (map.term type)
        (match head with
         | .reference loan => .reference (map.loan loan)
         | .callable id arguments => .callable id (arguments.map map.term)
         | .operation id arguments => .operation id (arguments.map map.term)
         | .pointer pointer => .pointer (map.pointer pointer)
         | other => other)
        live (map.values fields)

  def Relocation.values (map : Relocation) : List (Option Value) → List (Option Value)
    | [] => []
    | none :: rest => none :: map.values rest
    | some value :: rest => some (map.value value) :: map.values rest
end

def Relocation.rootValue (map : Relocation) (id : Identity) (root : Root) : Root :=
  { root with home := map.home root.home, region := map.region root.region, type := map.term root.type, value := root.value.map map.value, base := (map.physical.get id).getD root.base }

def Relocation.loanValue (map : Relocation) (loan : Loan) : Loan :=
  { loan with identity := map.loan loan.identity, parent := loan.parent.bind (fun id => if id ∈ map.loans then some (map.loan id) else none), referent := map.address loan.referent, region := map.region loan.region }

def SnapshotFrame : Frame → Prop
  | .label .. | .hook .. | .foreign .. | .hostCallback .. | .serviced .. => False
  | _ => True

def SnapshotMap (program : Kernel.Program) (before : State) (suspension : Suspension) (map : Relocation) : Prop :=
  map.roots = suspension.roots ∧ map.rootBase = before.world.nextRoot ∧ map.ownerBase = before.world.nextOwner ∧
  map.loanBase = before.world.nextLoan ∧ map.regionBase = before.world.nextRegion ∧
  map.activationBase = before.nextActivation ∧ map.handlerBase = before.nextHandler ∧
  map.scopeBase = before.world.nextRegion ∧
  (∀ id, id ∈ map.loans ↔ ∃ loan address value,
    before.world.loans.get id = some loan ∧ loan.live = true ∧ loan.referent.root ∈ map.roots ∧
    address.root ∈ map.roots ∧ before.world.Resident address value ∧ value.head = .reference id) ∧
  (∀ id, id ∈ map.regions ↔
    id ∈ suspension.frames.flatMap Frame.ownedRegions ++ [suspension.context.region,suspension.handler.computation.region] ∨
    ∃ rootId root, rootId ∈ map.roots ∧ before.world.roots.get rootId = some root ∧ root.region = id) ∧
  (∀ id ∈ map.regions, id ∈ before.world.liveRegions) ∧
  (∀ id, id ∈ map.activations ↔
    (∃ caller region, Frame.activation caller id region ∈ suspension.frames) ∨
    ∃ rootId home scope, rootId ∈ map.roots ∧ suspension.homes.get rootId = some home ∧
      (home = .localSlot id scope ∨ home = .temporary id scope)) ∧
  (∀ id, id ∈ map.scopes ↔ id = suspension.handler.computation.scope ∨
    (∃ caller region, Frame.scope caller id region ∈ suspension.frames) ∨
    ∃ rootId home activation, rootId ∈ map.roots ∧ suspension.homes.get rootId = some home ∧
      (home = .localSlot activation id ∨ home = .temporary activation id)) ∧
  (∀ id, id ∈ map.handlers ↔ ∃ handler owns, Frame.handler handler owns ∈ suspension.frames ∧ handler.identity = id) ∧
  map.physical.Unique ∧ map.physical.map Prod.fst = map.roots ∧
  (∀ id root, id ∈ map.roots → before.world.roots.get id = some root → ∃ base,
    map.physical.get id = some base ∧ 0 < base ∧ base % root.layout.alignment = 0 ∧
    base+root.layout.size < 2^program.declarations.input.target.pointerBits ∧
    DisjointStorage before.world base root.layout.size) ∧
  (∀ a b left right x y, a ∈ map.roots → b ∈ map.roots → a ≠ b →
    before.world.roots.get a = some left → before.world.roots.get b = some right →
    map.physical.get a = some x → map.physical.get b = some y →
    left.layout.size = 0 ∨ right.layout.size = 0 ∨ x+left.layout.size ≤ y ∨ y+right.layout.size ≤ x)

def Relocation.copyWorld (map : Relocation) (world : World) (homes : Table Home) : World :=
  { world with
    roots := world.roots ++ (world.roots.filter (fun entry => entry.1 ∈ map.roots)).map (fun (id,root) =>
      (map.root id, map.rootValue id { root with home := (homes.get id).getD root.home }))
    loans := world.loans ++ (world.loans.filter (fun entry => entry.1 ∈ map.loans)).map
      (fun (id,loan) => (map.loan id,map.loanValue loan))
    liveRegions := world.liveRegions ++ map.regions.map map.region
    nextRoot := map.rootBase + world.nextRoot
    nextOwner := map.ownerBase + world.nextOwner
    nextLoan := map.loanBase + world.nextLoan
    nextRegion := map.regionBase + world.nextRegion }

def CopiesSnapshot (program : Kernel.Program) (before : State) (suspension : Suspension)
    (map : Relocation) (after : State) : Prop :=
  Replayable program.declarations before.world suspension.roots ∧
  (∀ frame ∈ suspension.frames, SnapshotFrame frame) ∧ SnapshotMap program before suspension map ∧
  map.roots.Nodup ∧ map.loans.Nodup ∧ map.regions.Nodup ∧ map.activations.Nodup ∧ map.scopes.Nodup ∧ map.handlers.Nodup ∧
  after = { before with
    world := map.copyWorld before.world suspension.homes
    nextActivation := map.activationBase + before.nextActivation
    nextHandler := map.handlerBase + before.nextHandler } ∧
  after.world.WellFormed

theorem relocation_preserves_holes (map : Relocation) (value : Value) :
    (map.value value).fields.map Option.isSome = value.fields.map Option.isSome := by
  have fields (values : List (Option Value)) : (map.values values).map Option.isSome = values.map Option.isSome := by
    induction values with
    | nil => rfl
    | cons first rest ih => cases first <;> simp [Relocation.values, ih]
  cases value
  exact fields _

theorem relocation_preserves_alias (map : Relocation) {a b : Address} (same : a = b) :
    map.address a = map.address b := congrArg map.address same

end Glorious.Language.Execution
