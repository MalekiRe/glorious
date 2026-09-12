import GloriousLanguage.Atoms

/-! Snapshot relocation preserves holes and the alias graph. The finite
fresh maps below relocate storage identities, not source binding identities.
Unselected (in particular caller-owned borrowed) storage remains identical. -/
namespace Glorious.Language.Execution

open Kernel

structure Relocation where
  roots : List Identity
  owners : List Identity
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
def Relocation.owner (map : Relocation) := relocateId map.owners map.ownerBase
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

def Relocation.term (map : Relocation) : Term → Term := Term.renameRuntimeRegions map.region

def Relocation.signature (map : Relocation) (signature : Signature) : Signature :=
  signature.mapTerms map.term

def Relocation.invocation (map : Relocation) (call : Invocation) : Invocation :=
  call.mapTerms map.term

def Relocation.code (map : Relocation) : Code → Code := Code.mapTerms map.term
def Relocation.arm (map : Relocation) : Arm → Arm := Arm.mapTerms map.term
def Relocation.operationArm (map : Relocation) : OperationArm → OperationArm := OperationArm.mapTerms map.term
def Relocation.handlerSyntax (map : Relocation) : Handler → Handler := Handler.mapTerms map.term

def Relocation.authority (map : Relocation) : Authority → Authority
  | .owner => .owner
  | .loan id => .loan (map.loan id)
  | .shared backing => .shared (map.authority backing)

def Relocation.context (map : Relocation) (context : Context) : Context :=
  { context with
    environment := context.environment.map (fun binding => { binding with
      address := map.address binding.address
      authority := map.authority binding.authority })
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
         | .bindings pack => .bindings { pack.mapOrigins map.owner with region := map.region pack.region }
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
  { loan with
    identity := map.loan loan.identity
    parent := loan.parent.map map.loan
    referent := map.address loan.referent
    region := map.region loan.region }

def SnapshotFrame : Frame → Prop
  | .label .. | .hook .. | .foreign .. | .hostCallback .. | .serviced .. => False
  | _ => True

/-- Captured shared handles and their shared ancestors receive fresh loans,
including handles of external storage: the handle's region may be relocated
even when its referent is not. Unique ancestors remain external and parent
edges retain them; copying a shared child cannot duplicate unique authority. -/
def SnapshotLoan (world : World) (roots : List Identity) (id : Identity) : Prop :=
  ∃ loan descendant address value,
    world.loans.get id = some loan ∧ loan.live = true ∧ loan.mode = .shared ∧
    address.root ∈ roots ∧ world.Resident address value ∧ value.head = .reference descendant ∧
    AncestorLoan world id descendant

structure SnapshotMap (program : Kernel.Program) (before : State) (suspension : Suspension) (map : Relocation) : Prop where
  roots : map.roots = suspension.roots
  rootBase : map.rootBase = before.world.nextRoot
  ownerBase : map.ownerBase = before.world.nextOwner
  loanBase : map.loanBase = before.world.nextLoan
  regionBase : map.regionBase = before.world.nextRegion
  activationBase : map.activationBase = before.nextActivation
  handlerBase : map.handlerBase = before.nextHandler
  scopeBase : map.scopeBase = before.world.nextRegion
  owners : ∀ id, id ∈ map.owners ↔ ∃ address value,
    before.world.Resident address value ∧ address.root ∈ map.roots ∧ value.owner = id
  loans : ∀ id, id ∈ map.loans ↔ SnapshotLoan before.world map.roots id
  regions : ∀ id, id ∈ map.regions ↔
    id ∈ suspension.frames.flatMap Frame.ownedRegions ++ [suspension.context.region,suspension.handler.computation.region] ∨
    ∃ rootId root, rootId ∈ map.roots ∧ before.world.roots.get rootId = some root ∧ root.region = id
  liveRegions : ∀ id ∈ map.regions, id ∈ before.world.liveRegions
  /-- A captured handle may continue to alias external storage, but that
  unchanged storage cannot acquire a renamed local type identity. This is a
  scope-closure check on the copy's inputs, not a post-copy typing premise. -/
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
  physicalUnique : map.physical.Unique
  physicalRoots : map.physical.map Prod.fst = map.roots
  physical : ∀ id root, id ∈ map.roots → before.world.roots.get id = some root → ∃ base,
    map.physical.get id = some base ∧ 0 < base ∧ base % root.layout.alignment = 0 ∧
    base+root.layout.size < 2^program.declarations.input.target.pointerBits ∧
    DisjointStorage before.world base root.layout.size
  disjoint : ∀ a b left right x y, a ∈ map.roots → b ∈ map.roots → a ≠ b →
    before.world.roots.get a = some left → before.world.roots.get b = some right →
    map.physical.get a = some x → map.physical.get b = some y →
    left.layout.size = 0 ∨ right.layout.size = 0 ∨ x+left.layout.size ≤ y ∨ y+right.layout.size ≤ x

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

/-- The executable relocation contract. Its output invariant is proved in
`RelocationPreservation`, not required as permission to execute the copy. -/
structure CopiesSnapshot (program : Kernel.Program) (before : State) (suspension : Suspension)
    (map : Relocation) (after : State) : Prop where
  replayable : Replayable program.declarations before.world suspension.roots
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
