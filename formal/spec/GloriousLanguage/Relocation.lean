import GloriousLanguage.Atoms
import GloriousLanguage.ControlSupport

/-! Snapshot relocation preserves holes and the alias graph. The finite
fresh maps below relocate storage identities, not source binding identities.
Unselected (in particular caller-owned borrowed) storage remains identical. -/
namespace Glorious.Language.Execution

open Kernel

def Relocation.signature (map : Relocation) (signature : Signature) : Signature :=
  signature.mapTerms map.term

def Relocation.invocation (map : Relocation) (call : Invocation) : Invocation :=
  call.mapTerms map.term

def Relocation.code (map : Relocation) : Code → Code := Code.mapTerms map.term
def Relocation.arm (map : Relocation) : Arm → Arm := Arm.mapTerms map.term
def Relocation.operationArm (map : Relocation) : OperationArm → OperationArm := OperationArm.mapTerms map.term
def Relocation.handlerSyntax (map : Relocation) : Handler → Handler := Handler.mapTerms map.term

def Relocation.context (map : Relocation) (context : Context) : Context :=
  { context with
    environment := context.environment.map map.binding
    resourceContracts := context.resourceContracts.map (fun entry =>
      { entry with inputs := entry.inputs.map map.binding })
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

def SnapshotFrame : Frame → Prop
  | .label .. | .hook .. | .foreign .. | .hostCallback .. | .serviced .. => False
  | _ => True

structure SnapshotMap (program : Kernel.Program) (before : State) (suspension : Suspension)
    (map : Relocation) : Prop extends
    Relocation.StoragePlan program.declarations before.world suspension.controlAuthoritySupport map where
  roots : map.roots = suspension.roots
  activationBase : map.activationBase = before.nextActivation
  handlerBase : map.handlerBase = before.nextHandler
  scopeBase : map.scopeBase = before.world.nextRegion
  regions : ∀ id, id ∈ map.regions ↔
    id ∈ suspension.frames.flatMap Frame.ownedRegions ++ [suspension.context.region,suspension.handler.computation.region] ∨
    ∃ rootId root, rootId ∈ map.roots ∧ before.world.roots.get rootId = some root ∧ root.region = id
  /-- Unchanged external storage cannot acquire a renamed local type. -/
  externalReferentsScoped : ∀ address value id loan,
    address.root ∈ map.roots → before.world.Resident address value → value.head = .reference id →
    before.world.loans.get id = some loan → loan.referent.root ∉ map.roots →
    ∀ type, AddressType program.declarations before.world loan.referent type →
    ∀ region ∈ map.regions, ¬ Occurs (.runtimeRegion region) type
  activations : ∀ id, id ∈ map.activations ↔
    (∃ caller region, Frame.activation caller id region ∈ suspension.frames) ∨
    ∃ rootId home scope, rootId ∈ map.roots ∧ suspension.homes.get rootId = some home ∧
      (home = .localSlot id scope ∨ home = .temporary id scope)
  scopes : ∀ id, id ∈ map.scopes ↔ id = suspension.handler.computation.scope ∨
    (∃ caller region, Frame.scope caller id region ∈ suspension.frames) ∨
    ∃ rootId home activation, rootId ∈ map.roots ∧ suspension.homes.get rootId = some home ∧
      (home = .localSlot activation id ∨ home = .temporary activation id)
  handlers : ∀ id, id ∈ map.handlers ↔ ∃ handler owns, Frame.handler handler owns ∈ suspension.frames ∧ handler.identity = id

/-- The executable relocation contract. Its output invariant is proved in
`RelocationPreservation`, not required as permission to execute the copy. -/
structure CopiesSnapshot (program : Kernel.Program) (before : State) (suspension : Suspension)
    (map : Relocation) (after : State) : Prop where
  replayable : Replayable program before.world suspension.roots
  controlReplayable : ∀ authority ∈ suspension.controlAuthoritySupport, authority.Replayable before.world
  frames : ∀ frame ∈ suspension.frames, SnapshotFrame frame
  relocation : SnapshotMap program before suspension map
  roots : map.roots.Nodup
  owners : map.owners.Nodup
  loans : map.loans.Nodup
  regions : map.regions.Nodup
  activations : map.activations.Nodup
  scopes : map.scopes.Nodup
  handlers : map.handlers.Nodup
  result : after = { before with
    world := map.copyWorld before.world suspension.homes
    nextActivation := map.activationBase + before.nextActivation
    nextHandler := map.handlerBase + before.nextHandler }

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
