import GloriousLanguage.Drop

/-! Unbounded small-step execution. Control holds addresses into `World`,
never hidden copies of owners. Effects and machine leaves extend these tasks
in their respective modules; the final specification takes their union. -/
namespace Glorious.Language.Execution

open Kernel

/-- One selected operation application contract for both first-class value
construction and performance. Merely finding its declaration cannot supply
generic arguments or prove the declaration's prerequisites. -/
def OperationInstance (program : Kernel.Program) (id : DeclId) (arguments : List Term)
    (operation : OperationDefinition) (signature : Signature) : Prop :=
  ∃ substitution,
    program.declarations.operation id = some operation ∧ Instantiates operation.signature.generics arguments substitution ∧
    ConstraintsHold program.declarations ⟨[],[],0,operation.header.module,false,{}⟩ substitution operation.signature.constraints ∧
    signature = operation.signature.instantiate substitution

/-- Immutable input coordinates for the selected unsafe postcondition. These
historical bindings are not an access domain: all source permissions still
resolve solely from `Context.environment`. Proper-tail entry retains the
caller contracts without retaining a runtime activation. -/
structure InvocationResources where
  declaration : DeclId
  inputs : Environment
  deriving Repr, Inhabited

structure Context where
  environment : Environment
  module : ModuleId
  activation : Identity
  scope : Identity
  region : Identity
  instantiation : ScopeInstantiation := {}
  unsafeAllowed : Bool := false
  resourceContracts : List InvocationResources := []
  deriving Repr, Inhabited

def Context.static (context : Context) : Language.Context :=
  ⟨[],[],0,context.module,context.unsafeAllowed,{}⟩

def Context.bind (context : Context) (localSlot : Local) (address : Address) (authority : Authority := .owner) : Context :=
  { context with environment := ⟨.localSlot localSlot.id,address,authority⟩ ::
      context.environment.filter (fun entry => entry.key != .localSlot localSlot.id) }

def Context.bindResource (context : Context) (identity : Identity) (place : ResolvedPlace) : Context :=
  { context with environment := ⟨.obligation identity,place.address,place.authority⟩ ::
      context.environment.filter (fun entry => entry.key != .obligation identity) }

def Context.inheritResources (outer inner : Context) : Context :=
  { outer with environment := outer.environment.inheritImplicit inner.environment }

def OutgoingResources (program : Kernel.Program) (context : Context) (world : World)
    (result : Address) (outputs : List InvocationInput) : Prop :=
  (outputs.map (fun input => input.formal.key)).Nodup ∧
  ∀ entry ∈ context.resourceContracts,
    match program.unsafeContracts entry.declaration with
    | none => outputs = []
    | some contract => contract.outputs world entry.inputs result (outputs.map InvocationInput.binding)

/-- Normal returns and local rejoins share one resource handoff. Crossing an
activation derives fresh recipient claims from actual source bindings; a local
rejoin merely keeps that same activation's already-created bindings. -/
inductive ReturnsResources (program : Kernel.Program) (source receiver : Context) :
    World → Address → Context → World → Prop where
  | localReturn {world result} : source.activation = receiver.activation →
      ReturnsResources program source receiver world result (receiver.inheritResources source) world
  | invocationReturn {before result outputs bindings handed after} :
      source.activation ≠ receiver.activation →
      ResourceInputs program.declarations before source.environment (.activation source.activation) outputs →
      OutgoingResources program source before result outputs →
      BindsInputs program receiver.activation receiver.scope receiver.region
        before outputs bindings handed →
      RelinquishesCustody handed (.activation source.activation) after →
      ReturnsResources program source receiver before result
        { receiver with environment := receiver.environment.install (bindings.map StorageBinding.asObligation) } after

def Context.bindRegion (context : Context) (lexical runtime : Identity) : Context :=
  { context with instantiation := { context.instantiation with regions := context.instantiation.regions.set lexical runtime } }

def Context.bindBrand (context : Context) (lexical : Identity) (runtime : RuntimeBrand) : Context :=
  { context with instantiation := { context.instantiation with brands := context.instantiation.brands.set lexical runtime } }

def Context.term (context : Context) := context.instantiation.term

def Context.local (context : Context) (localSlot : Local) := localSlot.mapTerms context.term

def Context.invocation (context : Context) (call : Invocation) : Invocation :=
  call.mapTerms context.term

structure InstalledHandler where
  identity : Identity
  syntaxNode : Handler
  environment : Context
  computation : Context
  outer : Context
  deriving Repr, Inhabited

/-- Immutable selected foreign invocation. Callback results are protocol
messages, never additional operands of the original call. -/
structure ForeignCall where
  context : Context
  destination : Address
  binding : RuntimeBinding
  arguments : List Term
  signature : Signature
  operands : List Address
  deriving Repr, Inhabited

structure ForeignSession where
  call : ForeignCall
  state : List Nat
  /-- Actual additional storage handed to this protocol: host allocations,
  enclosing synchronous sessions and completed callback results. Hidden
  invocation leases and arbitrary source callback allocations are not exposed. -/
  exposed : List ResolvedPlace := []
  /-- Runtime handles of actual enclosing source callbacks. This is the
  handoff's dynamic no-shutdown requirement, not another runtime inventory. -/
  heldRuntimes : List Identity := []
  deriving Repr, Inhabited

/-- The actual foreign entry remains owned by its callback frame until source
cleanup returns to the host. Its code entry and runtime are not reconstructed
from a registry that may legitimately consume a one-shot registration. -/
structure CallbackEntry where
  registration : Identity
  runtime : Identity
  entryAddress : Nat
  deriving Repr, Inhabited

/-- Receiver and per-input lending use the same ordinary reference owner. -/
abbrev ReceiverLease := InvocationLease

/-- The call selection retains its actual input recipe until the fresh callee
activation exists. Whole-receiver and witness leases therefore cannot be
accidentally owned by a caller that proper-tail entry must retire. -/
inductive EntrySource where
  | supplied (inputs : List InvocationInput)
  | resident (receiver : ResolvedPlace) (access : Access) (arguments : List InvocationInput)
  | contextual (receiver : ResolvedPlace) (receiverAccess : Access)
      (witness : ResolvedPlace) (witnessAccess : Access) (inputs : List InvocationInput)
  deriving Repr, Inhabited

def InvocationInput.lentStorage (input : InvocationInput) : List Address :=
  if input.access = .owned then [] else [input.storage]

def EntrySource.lentStorage : EntrySource → List Address
  | .supplied inputs => inputs.flatMap InvocationInput.lentStorage
  | .resident receiver access arguments =>
      (if access = .owned then [] else [receiver.address]) ++ arguments.flatMap InvocationInput.lentStorage
  | .contextual receiver receiverAccess witness witnessAccess inputs =>
      (if receiverAccess = .owned then [] else [receiver.address]) ++
      (if witnessAccess = .owned then [] else [witness.address]) ++ inputs.flatMap InvocationInput.lentStorage

/-- The shell retired after binding belongs to the actual owned receiver. -/
def EntrySource.ownedReceiver : EntrySource → Option ResolvedPlace
  | .supplied _ => none
  | .resident receiver access _ | .contextual receiver access _ _ _ =>
      if access = .owned then some receiver else none

inductive Task where
  | run (context : Context) (code : Code)
  | atom (context : Context) (destination : Address) (atom : Atom) (next : Code)
  | yield (context : Context) (value : Address)
  | apply (context : Context) (invocation : Invocation) (tail : Bool)
  | enter (context : Context) (function : Function) (source : EntrySource) (tail : Bool)
  | destroy (context : Context) (address : Address) (authority : Authority) (next : Task)
  | destroyFields (context : Context) (address : Address) (authority : Authority) (fields : List Nat) (next : Task)
  | finishShell (address : Address) (authority : Authority) (next : Task)
  | retire (root : Identity) (next : Task)
  | cleanup (context : Context) (roots : List Identity) (next : Task)
  | closeRegion (region : Identity) (next : Task)
  | closeLoan (loan : Identity) (next : Task)
  | releaseLoan (loan : Identity) (next : Task)
  | transfer (source : Address) (authority : Authority) (destination : Address) (next : Task)
  | pattern (context : Context) (actions : List PatternAction) (body : Code)
  | perform (context : Context) (operation : DeclId) (arguments : List Term) (payload : List ResolvedPlace)
  | resume (context : Context) (continuation : Identity) (argument : ResolvedPlace) (tail : Bool)
  | cancel (context : Context) (continuation : Identity) (next : Task)
  | finishClause (handler : InstalledHandler) (ownsEnvironment : Bool)
      (continuation : Option Identity) (result : Address)
  | leave (context : Context) (brand : Identity) (argument : ResolvedPlace)
  | primitive (context : Context) (destination : Address) (binding : RuntimeBinding)
      (arguments : List Term) (operands : List ResolvedPlace) (next : Code)
  | foreign (session : ForeignSession) (next : Code)
  | foreignCallbackReturned (session : ForeignSession) (entry : CallbackEntry) (result : Address) (next : Code)
  | stopped (context : Context) (result : Address)
  | fatal (reason : Fatal)
  deriving Repr, Inhabited

inductive Frame where
  | binding (caller : Context) (destination : Address) (next : Code)
  | activation (caller : Context) (activation region : Identity)
  | scope (outer : Context) (scope region : Identity)
  | label (outer : Context) (brand region : Identity) (result : Term)
  | handler (handler : InstalledHandler) (ownsEnvironment : Bool)
  | serviced (handler : InstalledHandler) (ownsEnvironment : Bool) (clause : Context)
      (continuation : Option Identity)
  | completion (handler : InstalledHandler) (ownsEnvironment : Bool) (clause : Context)
  | resumed (caller : Context)
  | tailResume (caller : Context) (continuation : Identity)
  | hook (context : Context) (address : Address) (authority : Authority)
      (handle : Address) (loan : Identity) (next : Task)
  | foreign (identity : Identity)
  | hostCallback (session : ForeignSession) (entry : CallbackEntry) (resultType : Term)
      (lease : Option ReceiverLease) (next : Code)
  deriving Repr, Inhabited

/-- Runtime obligations follow the actual callback continuation, including
its already-scheduled source destruction. Ordinary contexts add no host pin. -/
def Task.callbackRuntimes : Task → List Identity
  | .destroy _ _ _ next | .destroyFields _ _ _ _ next | .finishShell _ _ next
  | .retire _ next | .cleanup _ _ next | .closeRegion _ next | .closeLoan _ next
  | .releaseLoan _ next | .transfer _ _ _ next | .cancel _ _ next => next.callbackRuntimes
  | .foreign session _ => session.heldRuntimes
  | .foreignCallbackReturned session entry _ _ => entry.runtime :: session.heldRuntimes
  | _ => []

def Frame.callbackRuntimes : Frame → List Identity
  | .hook _ _ _ _ _ next => next.callbackRuntimes
  | .hostCallback session entry _ _ _ => entry.runtime :: session.heldRuntimes
  | _ => []

/-- A delayed foreign return is a real foreign continuation even when carried
inside a hook's pending cleanup. Capturing it would fabricate a C stack return. -/
def Task.ForeignFree : Task → Prop
  | .destroy _ _ _ next | .destroyFields _ _ _ _ next | .finishShell _ _ next
  | .retire _ next | .cleanup _ _ next | .closeRegion _ next | .closeLoan _ next
  | .releaseLoan _ next | .transfer _ _ _ next | .cancel _ _ next => next.ForeignFree
  | .foreign .. | .foreignCallbackReturned .. => False
  | _ => True

def Frame.ForeignFree : Frame → Prop
  | .foreign .. | .hostCallback .. => False
  | .hook _ _ _ _ _ next => next.ForeignFree
  | _ => True

/-- Only cleanup-owning frame roles claim homes. A saved caller context is
an access environment, not ownership of that caller's activation or scope. -/
def FrameOwnsHome (frame : Frame) (home : Home) : Prop :=
  match frame with
  | .activation _ activation _ => HomeOwnedByActivation home activation
  | .scope context scope _ => HomeOwnedByScope home context.activation scope
  | .handler handler owns =>
      HomeOwnedByScope home handler.computation.activation handler.computation.scope ∨
      (owns = true ∧ HomeOwnedByActivation home handler.environment.activation)
  | .serviced handler owns clause _ | .completion handler owns clause =>
      HomeOwnedByActivation home clause.activation ∨
      (owns = true ∧ HomeOwnedByActivation home handler.environment.activation)
  | _ => False

def CapturedHome (handler : InstalledHandler) (inner : List Frame) (home : Home) : Prop :=
  HomeOwnedByScope home handler.computation.activation handler.computation.scope ∨
    ∃ frame ∈ inner, FrameOwnsHome frame home

theorem HomeOwnedByActivation.shape {home : Home} {activation : Identity}
    (owned : HomeOwnedByActivation home activation) :
    ∃ scope, home = .localSlot activation scope ∨ home = .temporary activation scope := by
  rcases owned with ⟨scope,same⟩ | ⟨scope,same⟩
  · exact ⟨scope,Or.inl same⟩
  · exact ⟨scope,Or.inr same⟩

/-- A home that a captured frame owns is a local or temporary home; capture never
relabels allocation or exterior storage. -/
theorem CapturedHome.local_or_temporary {handler : InstalledHandler} {inner : List Frame} {home : Home}
    (owned : CapturedHome handler inner home) :
    ∃ activation scope, home = .localSlot activation scope ∨ home = .temporary activation scope := by
  rcases owned with scope | ⟨frame,member,owned⟩
  · exact ⟨_,_,scope⟩
  · cases frame with
    | activation caller activation region =>
        obtain ⟨scope,shape⟩ := HomeOwnedByActivation.shape owned
        exact ⟨activation,scope,shape⟩
    | scope caller scope region => exact ⟨_,_,owned⟩
    | handler installed owns =>
        rcases owned with owned | ⟨_,owned⟩
        · exact ⟨_,_,owned⟩
        · obtain ⟨scope,shape⟩ := HomeOwnedByActivation.shape owned
          exact ⟨_,_,shape⟩
    | serviced installed owns clause continuation =>
        rcases owned with owned | ⟨_,owned⟩
        · obtain ⟨scope,shape⟩ := HomeOwnedByActivation.shape owned
          exact ⟨_,_,shape⟩
        · obtain ⟨scope,shape⟩ := HomeOwnedByActivation.shape owned
          exact ⟨_,_,shape⟩
    | completion installed owns clause =>
        rcases owned with owned | ⟨_,owned⟩
        · obtain ⟨scope,shape⟩ := HomeOwnedByActivation.shape owned
          exact ⟨_,_,shape⟩
        · obtain ⟨scope,shape⟩ := HomeOwnedByActivation.shape owned
          exact ⟨_,_,shape⟩
    | _ => exact False.elim owned


def Frame.ownedRegions : Frame → List Identity
  | .activation _ _ region | .scope _ _ region => [region]
  | .handler installed owns => installed.computation.region :: (if owns then [installed.environment.region] else [])
  | .serviced installed owns clause _ | .completion installed owns clause =>
      clause.region :: (if owns then [installed.environment.region] else [])
  | _ => []

def CloseRegions (regions : List Identity) (next : Task) : Task := regions.eraseDups.foldr Task.closeRegion next

/-- Returning a dependent loan retries both its ordinary parent and the
carrier loans recorded by invariant opening. No root/pointer traversal is
used to recover those dependencies. -/
def ReleaseLoans (identities : List Identity) (next : Task) : Task :=
  identities.eraseDups.foldr Task.releaseLoan next

/-- Relinquishment records pending returns on the real claim nodes. Cleanup
visits those nodes once; outstanding descendants retry them when they end. -/
def ReleaseCustodyLoans (world : World) (custody : ClaimCustody) (next : Task) : Task :=
  ReleaseLoans (world.loans.filterMap fun (identity,loan) =>
    if loan.live && loan.kind == .storageBorrow && loan.returnRequested && loan.custody == some custody then
      some identity else none) next

structure Suspension where
  identity : Identity
  handler : InstalledHandler
  frames : List Frame
  context : Context
  roots : List Identity
  homes : Table Home
  /-- Immutable root-allocation frontier at actual capture, before creating
  the continuation handle. Saved identities cannot name future storage. -/
  captureRootLimit : Identity
  quantity : Quantity
  remaining : Nat
  used : Nat
  original : Bool
  active : Bool
  deriving Repr, Inhabited

structure State where
  world : World
  task : Task
  /-- Ambient external state is not part of a captured continuation. Foreign
  calls and nested callbacks thread it forward through the same execution. -/
  hostState : List Nat := []
  frames : List Frame := []
  resumptions : Table Suspension := []
  nextActivation : Identity := 0
  nextHandler : Identity := 0
  nextBrand : Identity := 0
  nextContinuation : Identity := 0
  deriving Repr, Inhabited

/-- One logical budget belongs to the suspension identity, not to each alias
of its handle. An inactive budget has been consumed or canceled, although
cancellation cleanup may still be pending. An active one retains a positive
remainder of its original finite budget. -/
structure Suspension.Accounted (suspension : Suspension) : Prop where
  original : suspension.original = true
  quantity : suspension.quantity.SurfaceResumption
  active : suspension.active = true → 0 < suspension.remaining ∧
    suspension.quantity.upper = some (suspension.remaining + suspension.used)
  settled : suspension.active = false → suspension.remaining = 0 ∧ suspension.quantity.Contains suspension.used

structure State.ResumptionsAccounted (state : State) : Prop where
  unique : state.resumptions.Unique
  identity : ∀ id suspension, state.resumptions.get id = some suspension → suspension.identity = id
  fresh : ∀ id suspension, state.resumptions.get id = some suspension → id < state.nextContinuation
  accounted : ∀ id suspension, state.resumptions.get id = some suspension → suspension.Accounted

/-- One historical capture inventory, retained after replay or cancellation.
Its roots and saved homes are the actual capture product, not independently
reconstructed permission tables. -/
structure Suspension.CaptureOrigin (suspension : Suspension) : Prop where
  roots : suspension.roots.Nodup
  bounded : ∀ root ∈ suspension.roots, root < suspension.captureRootLimit
  homes : suspension.homes.Unique
  domain : ∀ root, (∃ home, suspension.homes.get root = some home) ↔ root ∈ suspension.roots
  ownedHomes : ∀ root home, suspension.homes.get root = some home →
    CapturedHome suspension.handler suspension.frames home
  foreignFree : ∀ frame ∈ suspension.frames, frame.ForeignFree

theorem Suspension.CaptureOrigin.home_none {suspension : Suspension}
    (origin : suspension.CaptureOrigin) {root : Identity} (outside : root ∉ suspension.roots) :
    suspension.homes.get root = none := by
  cases found : suspension.homes.get root with
  | none => rfl
  | some home => exact False.elim (outside ((origin.domain root).mp ⟨home,found⟩))

/-- The executable control invariant combines the existing budget component
with capture provenance and active ownership of the current root inventory.
Historical bounds survive settlement; liveness belongs only to active roots. -/
structure State.SuspensionsWellFormed (state : State) : Prop where
  budgets : state.ResumptionsAccounted
  origin : ∀ id suspension, state.resumptions.get id = some suspension → suspension.CaptureOrigin
  frontier : ∀ id suspension, state.resumptions.get id = some suspension →
    suspension.captureRootLimit ≤ state.world.nextRoot
  active : ∀ id suspension, state.resumptions.get id = some suspension → suspension.active = true →
    ∀ rootId, rootId ∈ suspension.roots ↔ ∃ root, state.world.roots.get rootId = some root ∧
      root.live = true ∧ root.home = .suspended id
  homeFresh : ∀ rootId root id, state.world.roots.get rootId = some root →
    root.home = .suspended id → id < state.nextContinuation

inductive Event where
  | allocate (address : Address)
  | move (source destination : Address)
  | copy (source destination : Address)
  | borrow (referent : Address) (loan : Identity)
  | loanEnd (loan : Identity)
  | shellConsumed (address : Address)
  | hookEnter (address : Address) (declaration : DeclId)
  | destroy (address : Address) (owner : Identity)
  | retire (root : Identity)
  | call (declaration : DeclId) (inputs : List InvocationInput)
  | tail (fromActivation toActivation : Identity)
  | branch (pattern : Identity) (positive : Bool)
  | perform (operation : DeclId) (instanceArguments : List Term)
  | suspend (continuation : Identity)
  | replay (continuation : Identity) (last : Bool)
  | cancel (continuation : Identity)
  | leave (brand : Identity)
  | host (symbol : String) (input output : List Nat)
  | fatal (reason : Fatal)
  deriving Repr, Inhabited

def Temporary (program : Kernel.Program) (context : Context) (type : Term)
    (before : World) (address : Address) (after : World) : Prop :=
  ∃ layout, Allocates program.declarations before (.temporary context.activation context.scope)
    context.region type layout true address after

/-- A lent receiver gets a real child loan. The supplied owner context may be
a fresh callee activation for tail entry; it is not implicitly the caller's
soon-to-be-retired storage. Captures consume the resulting loan authority. -/
def LendsReceiver (program : Kernel.Program) (leaseContext : Context) :=
  LendsResident program leaseContext.activation leaseContext.scope leaseContext.region

def Protect (program : Kernel.Program) (outer : Context) (before : World)
    (source : Address) (authority : Authority) (destination : Address) (after : World) : Prop :=
  ∃ value allocated, before.Stores source value ∧ Temporary program outer value.type before destination allocated ∧
    Transfers program allocated authority source destination after

/-- The next actual by-value handoff is ready but cannot obtain its temporary
home. Earlier handoffs are retained by the common outcome-indexed fold. -/
def ProtectExhausted (program : Kernel.Program) (context : Context) (before : World)
    (source : Address) (authority : Authority) : Prop :=
  ∃ value layout, before.Stores source value ∧ value.Initialized ∧ value.MoveReady program before [source] ∧
    Permitted before authority .owned source ∧
    AllocationExhausted program.declarations before context.region value.type layout

/-- Ordered by-value handoff. Each pending batch is ready against all of its
source clears before its first transfer. Thus a later input cannot invalidate
the reference or raw-resource support already handed to the clause. Source
evaluation has already done any implicit Copy required by the expression. -/
inductive ProtectsAttemptFor (program : Kernel.Program) (context : Context) (footprint : List Address) :
    World → List ResolvedPlace → List Address → World → PreparationOutcome → Prop where
  | nil {world} : ProtectsAttemptFor program context footprint world [] [] world .complete
  | cons {before source sources destination destinations middle after outcome} :
      (∃ values, ResidentHandoffReady program before (source :: sources) values
        footprint ∧ ∀ place ∈ source :: sources, place.address ∈ footprint) →
      Protect program context before source.address source.authority destination middle →
      ProtectsAttemptFor program context footprint middle sources destinations after outcome →
      ProtectsAttemptFor program context footprint before (source :: sources) (destination :: destinations) after outcome
  | exhausted {before source sources} :
      (∃ values, ResidentHandoffReady program before (source :: sources) values
        footprint ∧ ∀ place ∈ source :: sources, place.address ∈ footprint) →
      ProtectExhausted program context before source.address source.authority →
      ProtectsAttemptFor program context footprint before (source :: sources) [] before .exhausted

abbrev ProtectsFor (program : Kernel.Program) (context : Context) (footprint : List Address)
    (before : World) (sources : List ResolvedPlace) (destinations : List Address) (after : World) : Prop :=
  ProtectsAttemptFor program context footprint before sources destinations after .complete

@[elab_as_elim] theorem ProtectsFor.inductionOn {program : Kernel.Program} {context : Context}
    {footprint : List Address}
    {motive : ∀ before sources destinations after,
      ProtectsFor program context footprint before sources destinations after → Prop}
    {before : World} {sources : List ResolvedPlace} {destinations : List Address} {after : World}
    (kept : ProtectsFor program context footprint before sources destinations after)
    (nil : ∀ world, motive world [] [] world .nil)
    (cons : ∀ {before source sources destination destinations middle after},
      ∀ (ready : ∃ values, ResidentHandoffReady program before (source :: sources) values
        footprint ∧ ∀ place ∈ source :: sources, place.address ∈ footprint)
        (head : Protect program context before source.address source.authority destination middle)
        (tail : ProtectsFor program context footprint middle sources destinations after),
      motive middle sources destinations after tail →
        motive before (source :: sources) (destination :: destinations) after (.cons ready head tail)) :
    motive before sources destinations after kept := by
  have complete : ∀ {before sources destinations after outcome},
      ∀ (attempted : ProtectsAttemptFor program context footprint before sources destinations after outcome)
        (done : outcome = .complete), motive before sources destinations after (by cases done; exact attempted) := by
    intro before sources destinations after outcome attempted
    induction attempted with
    | nil => intro _; exact nil _
    | cons ready head tail ih =>
      intro done
      cases done
      exact cons ready head tail (ih rfl)
    | exhausted => intro impossible; cases impossible
  exact complete kept rfl

abbrev Protects (program : Kernel.Program) (context : Context) (before : World)
    (sources : List ResolvedPlace) (destinations : List Address) (after : World) : Prop :=
  ProtectsFor program context (sources.map ResolvedPlace.address) before sources destinations after

theorem ProtectsFor.ready {program : Kernel.Program} {context : Context} {before after : World}
    {sources : List ResolvedPlace} {destinations footprint : List Address}
    (handoff : ProtectsFor program context footprint before sources destinations after) :
    ∃ values, ResidentHandoffReady program before sources values footprint := by
  cases handoff with
  | nil =>
      refine ⟨[],.nil,?_,.nil,?_⟩
      · intro value member; cases member
      · intro source member; cases member
  | cons ready _ _ => obtain ⟨values,ready,_⟩ := ready; exact ⟨values,ready⟩

theorem ProtectsFor.coverage {program : Kernel.Program} {context : Context} {before after : World}
    {sources : List ResolvedPlace} {destinations footprint : List Address}
    (handoff : ProtectsFor program context footprint before sources destinations after) :
    ∀ source ∈ sources, source.address ∈ footprint := by
  cases handoff with
  | nil => intro source member; cases member
  | cons ready _ _ => exact ready.choose_spec.2

def RegionCanEnd (world : World) (region : Identity) : Prop :=
  (∀ id root, world.roots.get id = some root → root.live = true → root.region ≠ region) ∧
  (∀ id loan, world.loans.get id = some loan → loan.live = true → loan.region ≠ region) ∧
  (∀ id available, world.availability.get id = some available → available.active = true → available.region ≠ region) ∧
  (∀ address value pack, world.Resident address value → value.head = .bindings pack → pack.region ≠ region)

def RegionEnds (before : World) (region : Identity) (after : World) : Prop :=
  RegionCanEnd before region ∧ after = { before with liveRegions := before.liveRegions.filter (· != region) }

def ResolvedOperands (world : World) (environment : Environment)
    (places : List Place) (operands : List ResolvedPlace) : Prop :=
  ListRel (fun place entry => ResolvesPlace world environment place entry.address entry.authority ∧
    Permitted world entry.authority .shared entry.address) places operands

inductive ArgumentInputs (world : World) (context : Context) :
    Nat → List Local → List Place → List InvocationInput → Prop where
  | nil {index} : ArgumentInputs world context index [] [] []
  | cons {index formal formals place places address authority rest} :
      ResolvesPlace world context.environment place address authority → world.Initialized address →
      ArgumentInputs world context (index+1) formals places rest →
      ArgumentInputs world context index (formal :: formals) (place :: places)
        (⟨.argument index,.resident formal,address,authority,.owned⟩ :: rest)

def ResidentCaptureInputs (receiver : Address) (authority : Authority) (access : Access)
    (formals : List Local) : List InvocationInput :=
  formals.zipIdx.map (fun (formal,index) => ⟨.capture index,formal,receiver.child index,authority,access⟩)

def CaptureInputs (world : World) (receiver : Address) (authority : Authority) (access : Access)
    (formals : List Local) (inputs : List InvocationInput) : Prop :=
  inputs = ResidentCaptureInputs receiver authority access formals ∧
  ∀ input ∈ inputs, world.Initialized input.storage ∧ Permitted world input.authority access input.storage

def EntrySource.originalInputs (function : Function) : EntrySource → List InvocationInput
  | .supplied inputs | .contextual _ _ _ _ inputs => inputs
  | .resident receiver access arguments =>
      ResidentCaptureInputs receiver.address receiver.authority access function.captures ++ arguments

def CallableReceiver (program : Kernel.Program) (world : World) (address : Address) (authority : Authority) (access : Access)
    (id : DeclId) (arguments : List Term) : Prop :=
  ∃ value, world.Stores address value ∧ value.Initialized ∧ value.head = .callable id arguments ∧
    value.ResourcesAccessible program world access ∧ Permitted world authority access address

inductive ConsumesReceiver : World → Address → Authority → Access → World → Prop where
  | lent {world address authority access} : access ≠ .owned → ConsumesReceiver world address authority access world
  | owned {before address authority value after} : before.Stores address value → value.shellLive = true →
      (∃ id arguments, value.head = .callable id arguments) → Permitted before authority .owned address →
      before.write address (some (.resident value.owner value.type value.head false value.fields value.resources)) = some after →
      ConsumesReceiver before address authority .owned after


/-- The frozen reservation ledger supplies both storage and its exact resident
type product. Invocation cannot recover a different capture shape from an
independent environment declaration or an unrelated subtype view. -/
def ReservationInputs (world : World) (available : Availability) (access : Access)
    (formals : List Local) (inputs : List InvocationInput) : Prop :=
  available.reserved.length = formals.length ∧ formals.map (·.type) = available.residents ∧
  inputs = (formals.zip available.reserved).zipIdx.map
    (fun (entry,index) => ⟨.capture index,entry.1,entry.2.address,entry.2.authority,access⟩) ∧
  ∀ input ∈ inputs, Permitted world input.authority access input.storage ∧
    ∃ value, world.Stores input.storage value ∧ value.Initialized ∧ value.type = input.formal.type

inductive ConsumesAvailability : World → Address → Authority → Identity → Access → World → Prop where
  | lent {world address authority id access} : access ≠ .owned →
      ConsumesAvailability world address authority id access world
  | owned {before address authority id value available cleared} :
      before.Stores address value → value.Initialized → value.head = .available id →
      before.availability.get id = some available → available.active = true →
      Permitted before authority .owned address →
      before.write address none = some cleared →
      ConsumesAvailability before address authority id .owned
        { cleared with availability := cleared.availability.set id { available with active := false } }


/-- Readiness uses the actual stored witness and its live reservation ledger.
This remains meaningful for an empty capture list: neither the witness nor
the receiver can disappear merely because no ordinary input exposes it. -/
def ContextualWitness (world : World) (witness : ResolvedPlace) (access : Access)
    (available : Availability) : Prop :=
  ∃ value identity, world.Stores witness.address value ∧ value.Initialized ∧
    value.head = .available identity ∧ world.availability.get identity = some available ∧
    available.identity = identity ∧ available.active = true ∧ available.region ∈ world.liveRegions ∧
    value.type = .available available.brand (.runtimeRegion available.region) available.residents ∧
    Permitted world witness.authority access witness.address

/-- Original entry readiness is a fact about this actual stored recipe.
Supplied inputs are checked individually; resident/contextual entries also
retain the whole receiver and selected witness independently of capture count. -/
def EntrySource.Ready (program : Kernel.Program) (world : World) (function : Function) : EntrySource → Prop
  | .supplied _ => True
  | .resident receiver access _ => ∃ identity arguments,
      CallableReceiver program world receiver.address receiver.authority access identity arguments ∧
      Instance program identity arguments function
  | .contextual receiver access witness witnessAccess inputs =>
      ∃ identity arguments available captures parameters,
        CallableReceiver program world receiver.address receiver.authority access identity arguments ∧
        Instance program identity arguments function ∧ ContextualWitness world witness witnessAccess available ∧
        ReservationInputs world available witnessAccess function.captures captures ∧ inputs = captures ++ parameters ∧
        ∃ shell, world.Stores receiver.address shell ∧ shell.fields = []

/-- Every real source of invocation inputs is prepared under the same fresh
callee lifetime. Resident captures project the newly lent receiver authority;
contextual inputs keep the actual frozen reservation product and obtain their
own child loans when the common input binder consumes them. -/
inductive PreparesEntryAttempt (program : Kernel.Program) (callee : Context) (function : Function) :
    World → EntrySource → List InvocationInput → World → PreparationOutcome → Prop where
  | supplied {world inputs} : PreparesEntryAttempt program callee function world (.supplied inputs) inputs world .complete
  | resident {before receiver access arguments id instanceArguments lease authority lent captures after} :
      CallableReceiver program before receiver.address receiver.authority access id instanceArguments →
      Instance program id instanceArguments function →
      LendsReceiver program callee before receiver.address receiver.authority access lease authority lent →
      CaptureInputs lent receiver.address authority access function.captures captures →
      ConsumesReceiver lent receiver.address authority access after →
      PreparesEntryAttempt program callee function before (.resident receiver access arguments) (captures ++ arguments) after .complete
  | contextual {before receiver receiverAccess witness witnessAccess captures arguments id instanceArguments
      available receiverLease receiverAuthority middle witnessLease witnessAuthority lent consumed after} :
      CallableReceiver program before receiver.address receiver.authority receiverAccess id instanceArguments →
      Instance program id instanceArguments function →
      ContextualWitness before witness witnessAccess available →
      ReservationInputs before available witnessAccess function.captures captures →
      LendsReceiver program callee before receiver.address receiver.authority receiverAccess receiverLease receiverAuthority middle →
      LendsReceiver program callee middle witness.address witness.authority witnessAccess witnessLease witnessAuthority lent →
      ReservationInputs lent available witnessAccess function.captures captures →
      ConsumesReceiver lent receiver.address receiverAuthority receiverAccess consumed →
      ConsumesAvailability consumed witness.address witnessAuthority available.identity witnessAccess after →
      PreparesEntryAttempt program callee function before
        (.contextual receiver receiverAccess witness witnessAccess (captures ++ arguments)) (captures ++ arguments) after .complete
  | residentExhausted {before receiver access arguments id instanceArguments} :
      CallableReceiver program before receiver.address receiver.authority access id instanceArguments →
      Instance program id instanceArguments function →
      LendsResidentExhausted program callee.region before receiver.address receiver.authority access →
      PreparesEntryAttempt program callee function before (.resident receiver access arguments) [] before .exhausted
  | contextualReceiverExhausted {before receiver receiverAccess witness witnessAccess captures arguments id instanceArguments available} :
      CallableReceiver program before receiver.address receiver.authority receiverAccess id instanceArguments →
      Instance program id instanceArguments function →
      ContextualWitness before witness witnessAccess available →
      ReservationInputs before available witnessAccess function.captures captures →
      LendsResidentExhausted program callee.region before receiver.address receiver.authority receiverAccess →
      PreparesEntryAttempt program callee function before
        (.contextual receiver receiverAccess witness witnessAccess (captures ++ arguments)) [] before .exhausted
  | contextualWitnessExhausted {before receiver receiverAccess witness witnessAccess captures arguments id instanceArguments
      available receiverLease receiverAuthority middle} :
      CallableReceiver program before receiver.address receiver.authority receiverAccess id instanceArguments →
      Instance program id instanceArguments function →
      ContextualWitness before witness witnessAccess available →
      ReservationInputs before available witnessAccess function.captures captures →
      LendsReceiver program callee before receiver.address receiver.authority receiverAccess receiverLease receiverAuthority middle →
      LendsResidentExhausted program callee.region middle witness.address witness.authority witnessAccess →
      PreparesEntryAttempt program callee function before
        (.contextual receiver receiverAccess witness witnessAccess (captures ++ arguments)) [] middle .exhausted

theorem PreparesEntryAttempt.exhausted_inputs {program : Kernel.Program} {callee : Context} {function : Function}
    {before after : World} {source : EntrySource} {inputs : List InvocationInput}
    (prepared : PreparesEntryAttempt program callee function before source inputs after .exhausted) : inputs = [] := by
  cases prepared <;> rfl

/-- Completed preparation is the successful specialization of the same attempt. -/
abbrev PreparesEntry (program : Kernel.Program) (callee : Context) (function : Function)
    (before : World) (source : EntrySource) (inputs : List InvocationInput) (after : World) : Prop :=
  PreparesEntryAttempt program callee function before source inputs after .complete

/-- Both successful preparation and its real exhausted prefix depend on the
callee's fresh lifetime, not on the environment the input fold later builds. -/
theorem PreparesEntryAttempt.callee_context {program : Kernel.Program} {first second : Context}
    {function : Function} {before after : World} {source : EntrySource} {inputs : List InvocationInput}
    {outcome : PreparationOutcome}
    (prepared : PreparesEntryAttempt program first function before source inputs after outcome)
    (activation : first.activation = second.activation) (scope : first.scope = second.scope)
    (region : first.region = second.region) :
    PreparesEntryAttempt program second function before source inputs after outcome := by
  cases prepared with
  | supplied => exact .supplied
  | resident callable instanceArguments lent captures consumed =>
    exact .resident callable instanceArguments
      (by simpa only [LendsReceiver,activation,scope,region] using lent) captures consumed
  | contextual callable instanceArguments witnessed reserved receiver witness captured consumed finished =>
    exact .contextual callable instanceArguments witnessed reserved
      (by simpa only [LendsReceiver,activation,scope,region] using receiver)
      (by simpa only [LendsReceiver,activation,scope,region] using witness) captured consumed finished
  | residentExhausted callable instanced failed =>
    exact .residentExhausted callable instanced (by simpa only [region] using failed)
  | contextualReceiverExhausted callable instanced witnessed reserved failed =>
    exact .contextualReceiverExhausted callable instanced witnessed reserved (by simpa only [region] using failed)
  | contextualWitnessExhausted callable instanced witnessed reserved lent failed =>
    exact .contextualWitnessExhausted callable instanced witnessed reserved
      (by simpa only [LendsReceiver,activation,scope,region] using lent) (by simpa only [region] using failed)


/-- Owned invocation consumes the callable shell exactly once, after the
common binder has transferred its captures. The receiver is not an implicit
second owner retained by the host or a soon-to-be-retired tail caller. -/
inductive FinishesReceiver : World → ResolvedPlace → Access → World → Prop where
  | lent {world receiver access} : access ≠ .owned → FinishesReceiver world receiver access world
  | owned {before receiver value after} : before.Stores receiver.address value →
      value.shellLive = false → (∃ identity arguments, value.head = .callable identity arguments) →
      (∀ field ∈ value.fields, field = none) → value.resources = [] →
      Permitted before receiver.authority .owned receiver.address →
      before.write receiver.address none = some after →
      FinishesReceiver before receiver .owned after

inductive FinishesEntry : World → EntrySource → World → Prop where
  | supplied {world inputs} : FinishesEntry world (.supplied inputs) world
  | resident {before receiver access arguments after} : FinishesReceiver before receiver access after →
      FinishesEntry before (.resident receiver access arguments) after
  | contextual {before receiver access witness witnessAccess inputs after} : FinishesReceiver before receiver access after →
      FinishesEntry before (.contextual receiver access witness witnessAccess inputs) after

/-- Input contracts observe the original invocation, before fresh-region
creation or receiver/witness mutation. Both physical failure phases require
that same admission and retain their actual successful prefix. -/
inductive EnterWorldAttempt (program : Kernel.Program) (before : State) (caller : Context)
    (function : Function) (source : EntrySource) (context : Context) : World → PreparationOutcome → Prop where
  | inputs {withRegion prepared inputs environment declaration bound after outcome} :
      program.declarations.function function.declaration = some declaration →
      FreshRegion before.world before.world.nextRegion withRegion →
      PreparesEntry program context function withRegion source inputs prepared →
      IncomingResources program function before.world (source.originalInputs function) →
      BindsInputsAttemptFor program (.activation before.nextActivation)
        before.nextActivation before.world.nextRegion before.world.nextRegion
        (inputs.flatMap InvocationInput.clearedStorage) prepared inputs environment bound outcome →
      (match outcome with
        | .complete => FinishesEntry bound source after
        | .exhausted => after = bound) →
      context = ⟨environment,declaration.header.module,before.nextActivation,before.world.nextRegion,before.world.nextRegion,
        function.entryScope before.world.nextRegion before.nextBrand,false,[⟨function.declaration,environment⟩]⟩ →
      (function.signature.unsafeAllowed = true → caller.unsafeAllowed = true) →
      EnterWorldAttempt program before caller function source context after outcome
  | preparationExhausted {withRegion after declaration} :
      program.declarations.function function.declaration = some declaration →
      FreshRegion before.world before.world.nextRegion withRegion →
      PreparesEntryAttempt program context function withRegion source [] after .exhausted →
      IncomingResources program function before.world (source.originalInputs function) →
      context = ⟨[],declaration.header.module,before.nextActivation,before.world.nextRegion,before.world.nextRegion,
        function.entryScope before.world.nextRegion before.nextBrand,false,[⟨function.declaration,[]⟩]⟩ →
      (function.signature.unsafeAllowed = true → caller.unsafeAllowed = true) →
      EnterWorldAttempt program before caller function source context after .exhausted

theorem EnterWorldAttempt.fresh_context {program : Kernel.Program} {before : State} {after : World}
    {caller callee : Context} {function : Function} {source : EntrySource} {outcome : PreparationOutcome}
    (attempted : EnterWorldAttempt program before caller function source callee after outcome) :
    callee.activation = before.nextActivation ∧ callee.scope = before.world.nextRegion ∧
      callee.region = before.world.nextRegion := by
  cases attempted with
  | inputs _ _ _ _ _ _ contextEq _ | preparationExhausted _ _ _ _ contextEq _ =>
    subst callee
    exact ⟨rfl,rfl,rfl⟩

/-- Resource preconditions belong to the original call on every entry outcome,
including exhaustion before any ordinary input was bound. -/
theorem EnterWorldAttempt.incomingResources {program : Kernel.Program} {before : State} {after : World}
    {caller callee : Context} {function : Function} {source : EntrySource} {outcome : PreparationOutcome}
    (attempted : EnterWorldAttempt program before caller function source callee after outcome) :
    IncomingResources program function before.world (source.originalInputs function) := by
  cases attempted with
  | inputs _ _ _ incoming _ _ _ _ | preparationExhausted _ _ _ incoming _ _ => exact incoming


abbrev EnterWorld (program : Kernel.Program) (before : State) (caller : Context)
    (function : Function) (source : EntrySource) (context : Context) (after : World) : Prop :=
  EnterWorldAttempt program before caller function source context after .complete

/-- Complete entry necessarily crossed preparation and binding successfully.
The phase-indexed constructor, not an extra certificate, excludes earlier failure. -/
theorem EnterWorld.prepared {program : Kernel.Program} {before : State} {caller : Context}
    {function : Function} {source : EntrySource} {context : Context} {after : World}
    (entered : EnterWorld program before caller function source context after) :
    ∃ withRegion prepared inputs environment declaration bound,
      program.declarations.function function.declaration = some declaration ∧
      FreshRegion before.world before.world.nextRegion withRegion ∧
      PreparesEntry program context function withRegion source inputs prepared ∧
      IncomingResources program function before.world (source.originalInputs function) ∧
      BindsInputsAttemptFor program (.activation before.nextActivation)
        before.nextActivation before.world.nextRegion before.world.nextRegion
        (inputs.flatMap InvocationInput.clearedStorage) prepared inputs environment bound .complete ∧
      FinishesEntry bound source after ∧
      context = ⟨environment,declaration.header.module,before.nextActivation,before.world.nextRegion,before.world.nextRegion,
        function.entryScope before.world.nextRegion before.nextBrand,false,[⟨function.declaration,environment⟩]⟩ ∧
      (function.signature.unsafeAllowed = true → caller.unsafeAllowed = true) := by
  cases entered with
  | inputs selected fresh prepared incoming bound finished contextEq unsafeOk =>
    exact ⟨_,_,_,_,_,_,selected,fresh,prepared,incoming,bound,finished,contextEq,unsafeOk⟩


def FreshNamedFrame (function : Function) (caller : Context) (brand region : Identity) : List Frame :=
  match function.namedExit with
  | none => []
  | some _ => [.label caller brand region function.signature.result]

/-- A proper-tail destination has no outstanding result transformation or
dynamic delimiter. More permissive structural fusion requires a separate
equivalence proof in the target contract, not a retained old activation. -/
inductive TailFrames : List Frame → Identity → Context → List Identity → List Frame → Prop where
  | activation {caller activation region rest} : TailFrames (.activation caller activation region :: rest) activation caller [region] rest
  | scope {outer scope region rest activation caller regions finish} :
      TailFrames rest activation caller regions finish →
      TailFrames (.scope outer scope region :: rest) activation caller (region :: regions) finish
  | label {outer brand region result rest activation caller regions finish} :
      TailFrames rest activation caller regions finish →
      TailFrames (.label outer brand region result :: rest) activation caller regions finish

def ScheduledPattern (actions : PatternActions) : List PatternAction :=
  actions.shells ++ actions.bindings ++ actions.cleanup

inductive LocalStep (program : Kernel.Program) : State → Option Event → State → Prop where
  | evaluateExhausted {before context lexical localSlot value next layout} :
      before.task = .run context (.evaluate lexical value next) → localSlot = context.local lexical →
      AllocationExhausted program.declarations before.world context.region localSlot.type layout →
      LocalStep program before (some (.fatal .resource)) { before with task := .fatal .resource }
  | bindExhausted {before context lexical localSlot atom next layout} :
      before.task = .run context (.bind lexical atom next) → localSlot = context.local lexical →
      AllocationExhausted program.declarations before.world context.region localSlot.type layout →
      LocalStep program before (some (.fatal .resource)) { before with task := .fatal .resource }
  | invokeExhausted {before context lexical result call next layout} :
      before.task = .run context (.invoke lexical call next) → result = context.local lexical →
      AllocationExhausted program.declarations before.world context.region result.type layout →
      LocalStep program before (some (.fatal .resource)) { before with task := .fatal .resource }
  | enterExhausted {before caller function source tail context after} :
      before.task = .enter caller function source tail →
      EnterWorldAttempt program before caller function source context after .exhausted →
      LocalStep program before (some (.fatal .resource)) { before with
        world := after, task := .fatal .resource,
        nextActivation := before.nextActivation+1, nextBrand := before.nextBrand+1 }
  | resultExhausted {before context place address authority value} :
      before.task = .run context (.result place) →
      ResolvesPlace before.world context.environment place address authority → before.world.Stores address value →
      ProtectExhausted program context before.world address authority →
      LocalStep program before (some (.fatal .resource)) { before with task := .fatal .resource }
  | activationReturnExhausted {before context value outer activation region rest} :
      before.task = .yield context value → before.frames = .activation outer activation region :: rest →
      context.activation = activation → ProtectExhausted program outer before.world value .owner →
      LocalStep program before (some (.fatal .resource)) { before with task := .fatal .resource }
  | scopeReturnExhausted {before context value outer scope region rest} :
      before.task = .yield context value → before.frames = .scope outer scope region :: rest →
      ProtectExhausted program outer before.world value .owner →
      LocalStep program before (some (.fatal .resource)) { before with task := .fatal .resource }
  | evaluate {before context lexical localSlot value next address allocated layout} :
      before.task = .run context (.evaluate lexical value next) → localSlot = context.local lexical →
      Allocates program.declarations before.world (.localSlot context.activation context.scope) context.region
        localSlot.type layout localSlot.mutable address allocated →
      LocalStep program before (some (.allocate address))
        { before with world := allocated, task := .run context value, frames := .binding (context.bind localSlot address) address next :: before.frames }
  | bind {before context lexical localSlot atom next address allocated layout} :
      before.task = .run context (.bind lexical atom next) → localSlot = context.local lexical →
      Allocates program.declarations before.world (.localSlot context.activation context.scope) context.region
        localSlot.type layout localSlot.mutable address allocated →
      LocalStep program before (some (.allocate address))
        { before with world := allocated, task := .atom (context.bind localSlot address) address (atom.mapTerms context.term) next }
  | result {before context place address authority value kept after} : before.task = .run context (.result place) →
      ResolvesPlace before.world context.environment place address authority → before.world.Stores address value →
      Protect program context before.world address authority kept after →
      LocalStep program before (some (.move address kept))
        { before with world := after, task := .yield context kept }
  | discard {before context place next address authority} : before.task = .run context (.discard place next) →
      ResolvesPlace before.world context.environment place address authority →
      LocalStep program before none { before with task := .destroy context address authority (.run context next) }
  | assign {before context destination source next target permission value authority} :
      before.task = .run context (.assign destination source next) →
      ResolvesPlace before.world context.environment destination target permission →
      ResolvesPlace before.world context.environment source value authority →
      Permitted before.world permission .unique target → ¬ target.Overlaps value →
      LocalStep program before none { before with task := .destroy context target permission (.transfer value authority target (.run context next)) }
  | transfer {before source authority destination next after} : before.task = .transfer source authority destination next →
      Transfers program before.world authority source destination after →
      LocalStep program before (some (.move source destination)) { before with world := after, task := next }
  | invoke {before context lexical result call next destination allocated layout} :
      before.task = .run context (.invoke lexical call next) → result = context.local lexical →
      Allocates program.declarations before.world (.localSlot context.activation context.scope) context.region
        result.type layout result.mutable destination allocated →
      LocalStep program before (some (.allocate destination)) { before with world := allocated, task := .apply context (context.invocation call) false, frames := .binding (context.bind result destination) destination next :: before.frames }
  | tailRequest {before context call} : before.task = .run context (.tail call) →
      LocalStep program before none { before with task := .apply context (context.invocation call) true }
  | call {before context call tail receiver authority id arguments function captures inputs resources} :
      before.task = .apply context call tail → call.environment = none →
      ResolvesPlace before.world context.environment call.callee receiver authority →
      CallableReceiver program before.world receiver authority call.receiver id arguments → Instance program id arguments function →
      function.signature = call.signature → CaptureInputs before.world receiver authority call.receiver function.captures captures →
      ArgumentInputs before.world context 0 function.parameters call.arguments inputs →
      ResourceInputs program.declarations before.world context.environment (.activation context.activation) resources →
      LocalStep program before (some (.call id (captures ++ inputs ++ resources)))
        { before with task := .enter context function (.resident ⟨receiver,authority⟩ call.receiver (inputs ++ resources)) tail }
  | enter {before caller function source context after} : before.task = .enter caller function source false →
      EnterWorld program before caller function source context after →
      LocalStep program before none { before with world := after, task := .run context function.body, frames := FreshNamedFrame function context before.nextBrand context.region ++ .activation caller context.activation context.region :: before.frames, nextActivation := before.nextActivation+1, nextBrand := before.nextBrand+1 }
  | enterTail {before caller function source context entered after outer regions rest roots} :
      before.task = .enter caller function source true → EnterWorld program before caller function source context entered →
      RelinquishesCustody entered (.activation caller.activation) after →
      TailFrames before.frames caller.activation outer regions rest →
      ActivationRoots after caller.activation [] roots → Suspensible program after roots →
      (∀ address ∈ source.lentStorage, address.root ∉ roots) →
      LocalStep program before (some (.tail caller.activation context.activation)) { before with
        world := after
        task := ReleaseCustodyLoans after (.activation caller.activation)
          (.cleanup caller roots (CloseRegions regions (.run
            { context with resourceContracts := context.resourceContracts ++ caller.resourceContracts } function.body))),
        frames := FreshNamedFrame function
          { context with resourceContracts := context.resourceContracts ++ caller.resourceContracts }
          before.nextBrand context.region ++ .activation outer context.activation context.region :: rest,
        nextActivation := before.nextActivation+1, nextBrand := before.nextBrand+1 }
  | bindReturn {before context value caller destination next rest transferred returned after} : before.task = .yield context value →
      before.frames = .binding caller destination next :: rest → Transfers program before.world .owner value destination transferred →
      ReturnsResources program context caller transferred destination returned after →
      LocalStep program before (some (.move value destination))
        { before with
          world := after
          task := ReleaseCustodyLoans after (.activation context.activation) (.retire value.root (.run returned next))
          frames := rest }
  | activationReturn {before context value outer activation region rest kept keptWorld returned after roots} :
      before.task = .yield context value → before.frames = .activation outer activation region :: rest →
      context.activation = activation → Protect program outer before.world value .owner kept keptWorld →
      ReturnsResources program context outer keptWorld kept returned after →
      ActivationRoots after activation [] roots → Suspensible program after roots →
      LocalStep program before none { before with
        world := after
        task := ReleaseCustodyLoans after (.activation context.activation)
          (.cleanup context roots (.closeRegion region (.yield returned kept))), frames := rest }
  | topReturn {before context value} : before.task = .yield context value → before.frames = [] →
      LocalStep program before none { before with task := .stopped context value }
  | scope {before context identity body after inner} : before.task = .run context (.scope identity body) →
      FreshRegion before.world before.world.nextRegion after →
      inner = { context.bindRegion identity before.world.nextRegion with scope := before.world.nextRegion, region := before.world.nextRegion } →
      LocalStep program before none { before with world := after, task := .run inner body, frames := .scope context inner.scope inner.region :: before.frames }
  | scopeReturn {before context value outer scope region rest kept keptWorld returned after roots} : before.task = .yield context value →
      before.frames = .scope outer scope region :: rest → Protect program outer before.world value .owner kept keptWorld →
      ReturnsResources program context outer keptWorld kept returned after →
      ScopeRoots after outer.activation scope [] roots → Suspensible program after roots →
      LocalStep program before none { before with
        world := after
        task := ReleaseCustodyLoans after (.activation context.activation)
          (.cleanup context roots (.closeRegion region (.yield returned kept))), frames := rest }
  | label {before context lexical region result body inner selectedRegion} : before.task = .run context (.label lexical region result body) →
      context.instantiation.regions.get region = some selectedRegion →
      inner = context.bindBrand lexical (.label before.nextBrand) →
      LocalStep program before none { before with task := .run inner body, frames := .label context before.nextBrand selectedRegion (inner.term result) :: before.frames, nextBrand := before.nextBrand+1 }
  | labelReturn {before context value outer brand region result rest returned after} : before.task = .yield context value →
      before.frames = .label outer brand region result :: rest →
      ReturnsResources program context outer before.world value returned after →
      LocalStep program before none { before with
        world := after
        task := ReleaseCustodyLoans after (.activation context.activation) (.yield returned value), frames := rest }
  | choose {before context subject arms address authority arm actions} : before.task = .run context (.choose subject arms) →
      ResolvesPlace before.world context.environment subject address authority →
      FirstArm program.declarations before.world address arms arm →
      PatternPlan program.declarations before.world address authority .owned (arm.pattern.mapTerms context.term) actions →
      LocalStep program before none { before with task := .pattern context (ScheduledPattern actions) arm.body }
  | patternDone {before context body} : before.task = .pattern context [] body →
      LocalStep program before none { before with task := .run context body }
  | patternBind {before context localSlot address authority access rest body binding after} :
      before.task = .pattern context (.bind localSlot address authority access :: rest) body →
      BindsPattern program context.activation context.scope context.region before.world
        localSlot address authority access binding after →
      LocalStep program before none { before with world := after, task := .pattern (context.bind localSlot binding.address binding.authority) rest body }
  | patternShell {before context address authority rest body after} :
      before.task = .pattern context (.consumeShell address authority :: rest) body →
      Deconstructs program context.static before.world authority address after →
      LocalStep program before (some (.shellConsumed address))
        { before with world := after, task := .pattern context rest body }
  | patternDispose {before context address authority rest body} :
      before.task = .pattern context (.dispose address authority :: rest) body →
      LocalStep program before none { before with task := .destroy context address authority (.pattern context rest body) }
  | unsafeAllowed {before context body} : before.task = .run context (.unsafeScope body) →
      LocalStep program before none { before with task := .run { context with unsafeAllowed := true } body }
  | cleanupDone {before context next} : before.task = .cleanup context [] next →
      LocalStep program before none { before with task := next }
  | cleanupRoot {before context id roots next root} : before.task = .cleanup context (id :: roots) next →
      before.world.roots.get id = some root → root.live = true →
      LocalStep program before none { before with task := .destroy context ⟨id,root.generation,[]⟩ .owner (.retire id (.cleanup context roots next)) }
  | destroyVacant {before context address authority next} : before.task = .destroy context address authority next →
      before.world.Vacant address → LocalStep program before none { before with task := next }
  | destroyHook {before context address authority next value hook function withHandle handle after loan} :
      before.task = .destroy context address authority next → before.world.Stores address value → value.shellLive = true →
      MayDispose program.declarations value →
      DropInstance program value.type (.runtimeRegion context.region) hook function →
      Temporary program context (.reference .unique (.runtimeRegion context.region) value.type) before.world handle withHandle →
      FormsLoan program .destructor withHandle authority .unique context.region address handle after → loan = withHandle.nextLoan →
      LocalStep program before (some (.hookEnter address hook)) { before with world := after, task := .enter { context with unsafeAllowed := false } function (.supplied [⟨.argument 0,function.parameters.head!,handle,.owner,.owned⟩]) false, frames := .hook context address authority handle loan next :: before.frames }
  | hookReturned {before context result outer address authority handle loan next rest receiver} : before.task = .yield context result →
      before.frames = .hook outer address authority handle loan next :: rest →
      before.world.Stores address receiver →
      LocalStep program before none { before with frames := rest, task := .destroy outer result .owner (.retire result.root (.retire handle.root (.closeLoan loan (.destroyFields outer address authority (List.range receiver.fields.length).reverse next)))) }
  | destroyStructural {before context address authority next value} : before.task = .destroy context address authority next →
      before.world.Stores address value → MayDispose program.declarations value → Permitted before.world authority .owned address →
      (value.shellLive = false ∨ DropHook program.declarations value.type none) →
      (∀ id, value.head ≠ .continuation id) → (∀ id, value.head ≠ .reference id) →
      (∀ id, value.head ≠ .available id) →
      LocalStep program before none { before with task := .destroyFields context address authority (List.range value.fields.length).reverse next }
  | destroyReference {before context address authority next value id cleared} :
      before.task = .destroy context address authority next → before.world.Stores address value → value.head = .reference id →
      MayDispose program.declarations value → Permitted before.world authority .owned address →
      before.world.write address none = some cleared →
      LocalStep program before (some (.destroy address value.owner))
        { before with world := cleared, task := .releaseLoan id next }
  | fieldsDone {before context address authority next} : before.task = .destroyFields context address authority [] next →
      LocalStep program before none { before with task := .finishShell address authority next }
  | fieldNext {before context address authority field fields next} :
      before.task = .destroyFields context address authority (field :: fields) next →
      LocalStep program before none { before with task := .destroy context (address.child field) authority (.destroyFields context address authority fields next) }
  | shellDone {before address authority next value relinquished after} : before.task = .finishShell address authority next →
      before.world.Stores address value → (∀ field ∈ value.fields, field = none) →
      Permitted before.world authority .owned address →
      RelinquishesCustody before.world (.resident value.owner) relinquished →
      relinquished.write address none = some after →
      LocalStep program before (some (.destroy address value.owner))
        { before with world := after, task := ReleaseCustodyLoans after (.resident value.owner) next }
  | retire {before id next after} : before.task = .retire id next → Retires before.world id after →
      LocalStep program before (some (.retire id)) { before with world := after, task := next }
  | regionEnd {before region next after} : before.task = .closeRegion region next → RegionEnds before.world region after →
      LocalStep program before none { before with world := after, task := next }
  | loanEnd {before id next after} : before.task = .closeLoan id next → EndsLoan program before.world id after →
      LocalStep program before (some (.loanEnd id)) { before with world := after, task := next }
  | loanAlreadyEnded {before id next loan} : before.task = .closeLoan id next →
      before.world.loans.get id = some loan → loan.live = false →
      LocalStep program before none { before with task := next }
  | releaseReferenced {before id next} : before.task = .releaseLoan id next → before.world.References id →
      LocalStep program before none { before with task := next }
  | releaseResourceHeld {before id next} : before.task = .releaseLoan id next → before.world.ResourceReferences id →
      LocalStep program before none { before with task := next }
  | releaseBorrowed {before id next child} : before.task = .releaseLoan id next →
      ¬ before.world.References id → before.world.loans.get child.identity = some child →
      (child.parent = some id ∨ id ∈ child.guards) → child.live = true →
      LocalStep program before none { before with task := next }
  | releaseOwnedClaim {before id next loan} : before.task = .releaseLoan id next →
      before.world.loans.get id = some loan → loan.kind = .owning →
      LocalStep program before none { before with task := next }
  | releaseStorageRetained {before id next loan} : before.task = .releaseLoan id next →
      before.world.loans.get id = some loan → loan.kind = .storageBorrow → loan.returnRequested = false →
      LocalStep program before none { before with task := next }
  | releaseStorageReturned {before id next loan after} : before.task = .releaseLoan id next →
      before.world.loans.get id = some loan → ReturnsStorageLoan before.world id after →
      LocalStep program before (some (.loanEnd id))
        { before with world := after, task := ReleaseLoans (loan.parent.toList ++ loan.guards) next }
  | releaseRoot {before id next loan after} : before.task = .releaseLoan id next →
      before.world.loans.get id = some loan → loan.parent = none → EndsLoan program before.world id after →
      LocalStep program before (some (.loanEnd id))
        { before with world := after, task := ReleaseLoans loan.guards next }
  | releaseChild {before id next loan parent after} : before.task = .releaseLoan id next →
      before.world.loans.get id = some loan → loan.parent = some parent → EndsLoan program before.world id after →
      LocalStep program before (some (.loanEnd id))
        { before with world := after, task := ReleaseLoans (parent :: loan.guards) next }
  | releaseAlreadyEnded {before id next loan} : before.task = .releaseLoan id next →
      before.world.loans.get id = some loan → loan.live = false →
      LocalStep program before none { before with task := next }
  | endLoan {before context handle next address authority value id} : before.task = .run context (.endLoan handle next) →
      ResolvesPlace before.world context.environment handle address authority → before.world.Stores address value →
      value.head = .reference id →
      LocalStep program before none { before with task := .destroy context address authority (.closeLoan id (.run context next)) }
  | abort {before context} : before.task = .run context .abort →
      LocalStep program before (some (.fatal .abort)) { before with task := .fatal .abort }

end Glorious.Language.Execution
