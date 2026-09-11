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

def Relocation.term (map : Relocation) : Term → Term
  | .rigid id .region level => .rigid (map.region id) .region level
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
  | .callable receiver arguments output effects unsafe =>
      .callable (map.term receiver) (arguments.map map.term) (map.term output) (map.term effects) unsafe
  | .runsIn receiver access arguments after unsafe =>
      .runsIn (map.term receiver) (map.term access) (arguments.map map.term) (map.term after) unsafe
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
    | .bind local atom next => .bind (local.mapTerms map.term) (atom.mapTerms map.term) (map.code next)
    | .evaluate local value next => .evaluate (local.mapTerms map.term) (map.code value) (map.code next)
    | .assign destination value next => .assign destination value (map.code next)
    | .discard value next => .discard value (map.code next)
    | .invoke local call next => .invoke (local.mapTerms map.term)
        { call with signature := map.signature call.signature } (map.code next)
    | .tail call => .tail { call with signature := map.signature call.signature }
    | .scope id body => .scope id (map.code body)
    | .label brand region result body => .label brand region (map.term result) (map.code body)
    | .choose subject arms => .choose subject (arms.map map.arm)
    | .handle id computation handler => .handle id (map.code computation) (map.handlerSyntax handler)
    | .test local subject pattern id next => .test (local.mapTerms map.term) subject (pattern.mapTerms map.term) id (map.code next)
    | .endLoan handle next => .endLoan handle (map.code next)
    | .unsafeScope body => .unsafeScope (map.code body)
    | .closeAvailable value next => .closeAvailable value (map.code next)
    | .reserve local brand places next => .reserve (local.mapTerms map.term) brand places (map.code next)
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
    region := map.region context.region }

def Relocation.installed (map : Relocation) (handler : InstalledHandler) : InstalledHandler :=
  { handler with
    identity := map.handler handler.identity
    syntax := map.handlerSyntax handler.syntax
    environment := map.context handler.environment
    computation := map.context handler.computation
    outer := map.context handler.outer }

def Relocation.frame (map : Relocation) : Frame → Frame
  | .binding caller destination next => .binding (map.context caller) (map.address destination) (map.code next)
  | .activation caller activation region => .activation (map.context caller) (map.activation activation) (map.region region)
  | .scope outer scope region => .scope (map.context outer) (map.scope scope) (map.region region)
  | .label outer brand region result => .label (map.context outer) brand (map.region region) (map.term result)
  | .handler handler owns => .handler (map.installed handler) owns
  | .serviced handler continuation => .serviced (map.installed handler) continuation
  | .completion handler owns => .completion (map.installed handler) owns
  | .resumed caller => .resumed (map.context caller)
  | frame => frame

def Relocation.home (map : Relocation) : Home → Home
  | .local activation scope => .local (map.activation activation) (map.scope scope)
  | .temporary activation scope => .temporary (map.activation activation) (map.scope scope)
  | home => home

def Relocation.value (map : Relocation) : Value → Value
  | .resident owner type head live fields => .resident (map.ownerBase + owner) (map.term type)
      (match head with
       | .reference loan => .reference (map.loan loan)
       | .callable id arguments => .callable id (arguments.map map.term)
       | .operation id arguments => .operation id (arguments.map map.term)
       | other => other)
      live (fields.map (Option.map map.value))

def Relocation.rootValue (map : Relocation) (root : Root) : Root :=
  { root with home := map.home root.home, region := map.region root.region, type := map.term root.type,
    value := root.value.map map.value }

def Relocation.loanValue (map : Relocation) (loan : Loan) : Loan :=
  { loan with identity := map.loan loan.identity, parent := loan.parent.map map.loan,
    referent := map.address loan.referent, region := map.region loan.region }

def SnapshotFrame : Frame → Prop
  | .label .. | .hook .. | .foreign .. | .serviced .. => False
  | _ => True

/-- The complete used-name set, rather than every label in lexical scope,
is supplied by the structural code dependency relation in `Control`. -/
def NoCapturedLabelValue (world : World) (roots : List Identity) : Prop :=
  ∀ address value brand, address.root ∈ roots → world.Resident address value → value.head ≠ .label brand

def SnapshotMap (before : State) (suspension : Suspension) (map : Relocation) : Prop :=
  map.roots = suspension.roots ∧ map.rootBase = before.world.nextRoot ∧ map.ownerBase = before.world.nextOwner ∧
  map.loanBase = before.world.nextLoan ∧ map.regionBase = before.world.nextRegion ∧
  map.activationBase = before.nextActivation ∧ map.handlerBase = before.nextHandler ∧
  map.scopeBase = before.world.nextRegion ∧
  (∀ id, id ∈ map.loans ↔ ∃ loan, before.world.loans.get id = some loan ∧ loan.live = true ∧ loan.referent.root ∈ map.roots) ∧
  (∀ id, id ∈ map.regions ↔ ∃ rootId root, rootId ∈ map.roots ∧ before.world.roots.get rootId = some root ∧ root.region = id) ∧
  (∀ id, id ∈ map.activations ↔ ∃ rootId home scope, rootId ∈ map.roots ∧ suspension.homes.get rootId = some home ∧
    (home = .local id scope ∨ home = .temporary id scope)) ∧
  (∀ id, id ∈ map.scopes ↔ ∃ rootId home activation, rootId ∈ map.roots ∧ suspension.homes.get rootId = some home ∧
    (home = .local activation id ∨ home = .temporary activation id)) ∧
  (∀ id, id ∈ map.handlers ↔ ∃ handler owns, Frame.handler handler owns ∈ suspension.frames ∧ handler.identity = id)

def Relocation.copyWorld (map : Relocation) (world : World) (homes : Table Home) : World :=
  { world with
    roots := world.roots ++ (world.roots.filter (fun entry => entry.1 ∈ map.roots)).map (fun (id,root) =>
      (map.root id, map.rootValue { root with home := (homes.get id).getD root.home }))
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
  (∀ frame ∈ suspension.frames, SnapshotFrame frame) ∧ SnapshotMap before suspension map ∧
  map.roots.Nodup ∧ map.loans.Nodup ∧ map.regions.Nodup ∧ map.activations.Nodup ∧ map.scopes.Nodup ∧ map.handlers.Nodup ∧
  after = { before with
    world := map.copyWorld before.world suspension.homes
    nextActivation := map.activationBase + before.nextActivation
    nextHandler := map.handlerBase + before.nextHandler } ∧
  after.world.WellFormed

theorem relocation_preserves_holes (map : Relocation) (value : Value) :
    (map.value value).fields.map Option.isSome = value.fields.map Option.isSome := by
  cases value
  simp [Relocation.value, Value.fields, List.map_map]

theorem relocation_preserves_alias (map : Relocation) {a b : Address} (same : a = b) :
    map.address a = map.address b := congrArg map.address same

end Glorious.Language.Execution
