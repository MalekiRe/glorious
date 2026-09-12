import GloriousLanguage.Typing
import GloriousLanguage.ControlOrigin
import GloriousLanguage.InvocationInputs
import GloriousLanguage.LabelBoundary
import GloriousLanguage.ForeignRuntimeSupport

/-! Checked interfaces are abstractions of execution, not trusted annotations.
The meaning below is intentionally semantic; it does not claim that an
arbitrary exact control contract has a decidable inference procedure. -/
namespace Glorious.Language.Contracts

open Kernel Execution

inductive Outcome where
  | normal (result : Address)
  | label (brand : Identity) (result : ResolvedPlace)
  | operation (id : DeclId) (arguments : List Term) (payload : List ResolvedPlace)
  | fault (reason : Fatal)
  | divergent
  | unknown
  deriving Repr, Inhabited

inductive Guard where
  | always
  | constructor (origin : Identity) (path : List Nat) (variant : DeclId)
  | pattern (origin pattern : Identity) (positive : Bool)
  | and (left right : Guard)
  | or (left right : Guard)
  deriving Repr, Inhabited

def Guard.Holds (world : World) : Guard → Prop
  | .always => True
  | .constructor origin path variant => ∃ address value selected,
      world.Resident address value ∧ value.owner = origin ∧ value.atPath path = some selected ∧ selected.head = .constructor variant
  | .pattern origin patternId positive => ∃ address value pack,
      world.Resident address value ∧ value.shellLive = true ∧ value.head = .bindings pack ∧
      ⟨origin,patternId,positive⟩ ∈ pack.facts
  | .and left right => left.Holds world ∧ right.Holds world
  | .or left right => left.Holds world ∨ right.Holds world

structure Observation where
  input : List InvocationInput
  before : World
  events : List Event
  after : World
  outcome : Outcome

def InputsTyped (program : Kernel.Program) (inputs : List InvocationInput) (world : World) : Prop :=
  Typing.WorldTyped program world ∧
  (inputs.map (fun input => input.formal.id)).Nodup ∧
  (∀ input ∈ inputs, ∃ value, world.Stores input.storage value ∧ value.Initialized ∧ value.type = input.formal.type ∧
    Permitted world input.authority input.access input.storage) ∧
  (∀ left ∈ inputs, ∀ right ∈ inputs, left ≠ right → left.storage.Overlaps right.storage →
    left.access = .shared ∧ right.access = .shared)

def FunctionInputs (function : Function) (inputs : List InvocationInput) : Prop :=
  inputs.map (·.formal) = function.captures ++ function.parameters ∧
  (∀ index input, inputs[index]? = some input →
    (index < function.captures.length ∧ input.origin = .capture index) ∨
      (function.captures.length ≤ index ∧ input.origin = .argument (index-function.captures.length) ∧
        input.access = .owned))

/-- Admission is at the actual `enter` task, before fresh-region creation,
receiver lending and ordinary input binding. Original storage/access coordinates
come from the same capture projection used by that preparation, not a fabricated
supplied-input execution. No successful entry or after-state safety is assumed. -/
def InvocationStart (program : Kernel.Program) (host : Foreign.Model) (function : Function)
    (inputs : List InvocationInput) (boundary : InvocationBoundary) (state : State) : Prop :=
  InputsTyped program inputs state.world ∧ FunctionInputs function inputs ∧ state.ControlWellFormed ∧
  host.AuthoritiesRecorded state.world state.hostState ∧ host.CallbacksWellFormed state ∧
  ∃ caller source tail, state.task = .enter caller function source tail ∧
    source.originalInputs function = inputs ∧ boundary.Entry state caller source inputs tail ∧
    caller.region ∈ state.world.liveRegions ∧
    (function.signature.unsafeAllowed = true → caller.unsafeAllowed = true)

/-- Whole-program invocation is the isolated specialization of the same
admission relation. It retains the original supplied-input entry convention. -/
abbrev InitialInvocation (program : Kernel.Program) (host : Foreign.Model) (function : Function)
    (inputs : List InvocationInput) (state : State) : Prop :=
  InvocationStart program host function inputs .isolated state

theorem InvocationStart.isolated {program : Kernel.Program} {host : Foreign.Model} {function : Function}
    {inputs : List InvocationInput} {state : State} {caller : Execution.Context}
    (typed : InputsTyped program inputs state.world) (formals : FunctionInputs function inputs)
    (control : state.ControlWellFormed) (registry : host.AuthoritiesRecorded state.world state.hostState)
    (task : state.task = .enter caller function (.supplied inputs) false) (frames : state.frames = [])
    (region : caller.region ∈ state.world.liveRegions)
    (allowed : function.signature.unsafeAllowed = true → caller.unsafeAllowed = true) :
    InitialInvocation program host function inputs state := by
  refine ⟨typed,formals,control,registry,?_,caller,.supplied inputs,false,task,rfl,⟨rfl,frames,rfl⟩,region,allowed⟩
  constructor
  · simp only [State.CallbackControl,task,frames,Task.CallbackCovers,FramesCallbackCovers,and_self]
  · intro runtime member
    simp only [State.callbackRuntimes,task,frames,Task.callbackRuntimes,
      Foreign.AmbientRuntimes.nil,List.nil_append,List.not_mem_nil] at member

/-- The real prepared input binder consumes the same ordered formal/origin
contract as admission, even when receiver lending changes its authorities. -/
theorem FunctionInputs.prepared {program : Kernel.Program} {context : Execution.Context} {function : Function}
    {before after : World} {source : EntrySource} {inputs : List InvocationInput}
    (original : FunctionInputs function (source.originalInputs function))
    (prepared : PreparesEntry program context function before source inputs after) : FunctionInputs function inputs := by
  refine ⟨prepared.input_formals.trans original.1,?_⟩
  intro index input selected
  have same := congrArg (fun coordinates => coordinates[index]?)
    (prepared.map_inputs (fun input => (input.origin,input.access)) (by intros; rfl))
  simp only [List.getElem?_map,selected,Option.map_some] at same
  obtain ⟨old,present,equal⟩ := Option.map_eq_some_iff.mp same.symm
  have origin := original.2 index old present
  have sameOrigin : old.origin = input.origin := congrArg Prod.fst equal
  have sameAccess : old.access = input.access := congrArg Prod.snd equal
  simpa only [sameOrigin,sameAccess] using origin

theorem InvocationStart.prepared_inputs {program : Kernel.Program} {host : Foreign.Model} {function : Function}
    {original inputs : List InvocationInput} {boundary : InvocationBoundary} {state : State}
    {caller callee : Execution.Context} {source : EntrySource} {tail : Bool} {before after : World}
    (initial : InvocationStart program host function original boundary state)
    (task : state.task = .enter caller function source tail)
    (prepared : PreparesEntry program callee function before source inputs after) : FunctionInputs function inputs := by
  obtain ⟨_,actual,_,entry,coordinates,_⟩ := initial.2.2.2.2.2
  have same := (Task.enter.inj (entry.symm.trans task)).2.2.1
  subst actual
  apply FunctionInputs.prepared _ prepared
  simpa only [coordinates] using initial.2.1

theorem InvocationStart.inside {program : Kernel.Program} {host : Foreign.Model} {function : Function}
    {inputs : List InvocationInput} {boundary : InvocationBoundary} {state : State}
    (initial : InvocationStart program host function inputs boundary state) : boundary.Inside program state := by
  obtain ⟨caller,source,tail,task,_,entry,_⟩ := initial.2.2.2.2.2
  cases boundary with
  | isolated => trivial
  | caller returnTo ambient =>
    refine ⟨?_,?_,?_,?_⟩
    · rcases entry with ⟨_,_,rfl⟩ | ⟨_,regions,tailFrames⟩
      · exact ⟨[],rfl⟩
      · exact tailFrames_suffix tailFrames
    · rintro ⟨context,result,pending,_⟩
      simp only [task,reduceCtorEq] at pending
    · intro context id arguments payload pending
      simp only [task,reduceCtorEq] at pending
    · intro context brand result pending
      simp only [task,reduceCtorEq] at pending

/-- Finite invocation outcomes stop at the invocation boundary. Internal
continuation creation/cancellation are trace events, not exits of the helper
which contains them. Escaped continuation lifecycle observations below retain
the actual outward request which created that continuation. -/
def AtOutcome (program : Kernel.Program) (boundary : InvocationBoundary) (state : State) : Outcome → Prop
  | .normal result => boundary.Normal state result
  | .label brand result => boundary.OutwardLabel state brand result
  | .operation id arguments payload => boundary.OutwardOperation program state id arguments payload
  | .fault reason => state.task = .fatal reason
  | .divergent | .unknown => False

def ObservationAt (program : Kernel.Program) (host : Foreign.Model) (function : Function)
    (boundary : InvocationBoundary) (start finish : State) (observation : Observation) : Prop :=
  InvocationStart program host function observation.input boundary start ∧ start.world = observation.before ∧
  InvocationRun program host boundary start observation.events finish ∧ finish.world = observation.after ∧
  AtOutcome program boundary finish observation.outcome

def Observes (program : Kernel.Program) (host : Foreign.Model) (function : Function) (observation : Observation) : Prop :=
  ∃ boundary start finish, ObservationAt program host function boundary start finish observation

/-- Cancellation initiation settles the continuation's authority and starts
its cleanup. It does not assert completion of arbitrary user destructors. -/
inductive ContinuationOutcome where
  | suspended
  | cancellationStarted
  deriving Repr, Inhabited

/-- The request trace belongs to the invocation. Lifecycle events occur in
the original caller execution and are deliberately recorded separately. -/
structure LifecycleObservation where
  request : Observation
  continuation : Identity
  callerEvents : List Event
  after : World
  outcome : ContinuationOutcome

/-- The capture is the real next step at the SAME outward request, including
the original ambient handler and foreign barriers. A fresh unrelated table
entry or an internal suspension cannot establish this product. -/
def EscapedCapture (program : Kernel.Program) (host : Foreign.Model) (function : Function)
    (request : Observation) (continuation : Identity) (captured : State) : Prop :=
  ∃ boundary start pending operation arguments payload,
    ObservationAt program host function boundary start pending request ∧
    request.outcome = .operation operation arguments payload ∧
    EffectStep program pending (some (.suspend continuation)) captured

def LifecycleAt (program : Kernel.Program) (host : Foreign.Model) (captured : State)
    (observation : LifecycleObservation) : Prop :=
  match observation.outcome with
  | .suspended => observation.callerEvents = [.suspend observation.continuation] ∧ observation.after = captured.world
  | .cancellationStarted => ∃ events canceling finish,
      observation.callerEvents = .suspend observation.continuation :: events ++ [.cancel observation.continuation] ∧
      Run program host captured events canceling ∧
      EffectStep program canceling (some (.cancel observation.continuation)) finish ∧ observation.after = finish.world

def LifecycleObserves (program : Kernel.Program) (host : Foreign.Model) (function : Function)
    (observation : LifecycleObservation) : Prop :=
  ∃ captured, EscapedCapture program host function observation.request observation.continuation captured ∧
    LifecycleAt program host captured observation

def Diverges (program : Kernel.Program) (host : Foreign.Model) (function : Function) (inputs : List InvocationInput)
    (states : Nat → State) (events : Nat → Option Event) : Prop :=
  ∃ boundary, InvocationStart program host function inputs boundary (states 0) ∧
    ∀ n, InvocationStep program host boundary (states n) (events n) (states (n+1))

structure Interface where
  finite : Observation → Prop
  infinite : List InvocationInput → (Nat → State) → (Nat → Option Event) → Prop
  lifecycle : LifecycleObservation → Prop

def Derived (program : Kernel.Program) (function : Function) (interface : Interface) : Prop :=
  (∀ host observation, Foreign.Model.Lawful program host →
    Observes program host function observation → interface.finite observation) ∧
  (∀ host inputs states events, Foreign.Model.Lawful program host →
    Diverges program host function inputs states events → interface.infinite inputs states events) ∧
  (∀ host observation, Foreign.Model.Lawful program host →
    LifecycleObserves program host function observation → interface.lifecycle observation)

def ExactInterface (program : Kernel.Program) (function : Function) : Interface :=
  ⟨fun observation => ∃ host, Foreign.Model.Lawful program host ∧ Observes program host function observation,
   fun inputs states events => ∃ host, Foreign.Model.Lawful program host ∧ Diverges program host function inputs states events,
   fun observation => ∃ host, Foreign.Model.Lawful program host ∧ LifecycleObserves program host function observation⟩

/-- An outward request has an actual ordered payload preparation and the
selected operation's permission on its callee-owned post-payload remainder.
The same permission composes with the accepting caller's residual ownership;
the caller's resources are not preemptively charged to the callee. -/
def MayAwait (program : Kernel.Program) (function : Function) (state : State)
    (boundary : InvocationBoundary := .isolated) : Prop :=
  ∃ context id arguments payload operation signature,
    state.task = .perform context id arguments payload ∧ OperationInstance program id arguments operation signature ∧
    RowSubset program.declarations context.static signature.effects function.signature.effects ∧
    (∀ source ∈ payload, state.world.Initialized source.address ∧
      Permitted state.world source.authority .owned source.address) ∧
    (¬ boundary.InternalOperation program state id arguments payload) ∧
    ∃ disposition, OperationDisposition.Matches operation disposition ∧
      boundary.OperationReady program state payload disposition

/-- The outward predicate retains the disposition of the actual selected
operation instance, rather than a mode inferred independently at its consumer. -/
theorem MayAwait.operation_ready {program : Kernel.Program} {function : Function} {state : State}
    {boundary : InvocationBoundary} {context : Execution.Context} {id : DeclId}
    {arguments : List Term} {payload : List ResolvedPlace} {operation : OperationDefinition} {signature : Signature}
    (awaiting : MayAwait program function state boundary)
    (pending : state.task = .perform context id arguments payload)
    (selected : OperationInstance program id arguments operation signature) :
    ∃ disposition, OperationDisposition.Matches operation disposition ∧
      boundary.OperationReady program state payload disposition := by
  obtain ⟨_,_,_,_,actual,_,task,actualInstance,_,_,_,permission⟩ := awaiting
  obtain ⟨rfl,rfl,rfl,rfl⟩ := Task.perform.inj (task.symm.trans pending)
  have same := actualInstance.definition_eq selected
  subst actual
  exact permission

theorem MayAwait.outward {program : Kernel.Program} {function : Function} {state : State}
    {boundary : InvocationBoundary} {context : Execution.Context} {id : DeclId}
    {arguments : List Term} {payload : List ResolvedPlace}
    (awaiting : MayAwait program function state boundary)
    (pending : state.task = .perform context id arguments payload) :
    ¬ boundary.InternalOperation program state id arguments payload := by
  obtain ⟨_,_,_,_,_,_,task,_,_,_,outside,_⟩ := awaiting
  obtain ⟨rfl,rfl,rfl,rfl⟩ := Task.perform.inj (task.symm.trans pending)
  exact outside

theorem MayAwait.foreign_free {program : Kernel.Program} {function : Function} {state : State}
    {boundary : InvocationBoundary} (awaiting : MayAwait program function state boundary) :
    ∃ inner, state.frames = inner ++ boundary.ambient ∧ ∀ frame ∈ inner, frame.ForeignFree := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,disposition,_,ready⟩ := awaiting
  exact ready.foreign_free

/-- Admission produces ordered payload protection for the actual clause home.
This is the preparation part of handler execution, not an assumed effect step. -/
theorem MayAwait.prepare {program : Kernel.Program} {function : Function} {state : State}
    {boundary : InvocationBoundary} {context clause : Execution.Context} {id : DeclId}
    {arguments : List Term} {payload : List ResolvedPlace} {operation : OperationDefinition}
    {signature : Signature} {disposition : OperationDisposition} {withRegion : World}
    (awaiting : MayAwait program function state boundary)
    (pending : state.task = .perform context id arguments payload)
    (selected : OperationInstance program id arguments operation signature)
    (matched : OperationDisposition.Matches operation disposition)
    (home : OperationPayloadContext state clause withRegion) :
    ∃ kept moved, Protects program clause withRegion payload kept moved ∧
      ∃ inner roots, state.frames = inner ++ boundary.ambient ∧
        (∀ frame ∈ inner, frame.ForeignFree) ∧
        AbandonedRoots moved inner (kept.map Address.root) roots ∧
        OperationDisposition.Permits program moved roots inner disposition := by
  obtain ⟨actual,actualMode,ready⟩ := awaiting.operation_ready pending selected
  have same := actualMode.functional matched
  subst actual
  exact ready.prepare home

/-- For any actual outward route and actual payload preparation, the caller's
share supplies precisely the remaining permission of the real terminal or
resumptive rule. The callee's permission is obtained from admission. -/
theorem MayAwait.caller_permission {program : Kernel.Program} {function : Function} {state : State}
    {boundary : InvocationBoundary} {context clause : Execution.Context} {id : DeclId}
    {arguments : List Term} {payload : List ResolvedPlace} {operation : OperationDefinition}
    {signature : Signature} {disposition : OperationDisposition} {kept : List Address} {moved : World}
    {abandoned outer : List Frame} {handler : InstalledHandler} {owns : Bool} {arm : OperationArm}
    {all : List Identity}
    (awaiting : MayAwait program function state boundary)
    (pending : state.task = .perform context id arguments payload)
    (selectedOperation : OperationInstance program id arguments operation signature)
    (matched : OperationDisposition.Matches operation disposition)
    (route : Routes program state id arguments payload abandoned handler owns arm outer)
    (prepared : PreparedOperationPayload program state payload clause kept moved)
    (selectedRoots : DelimitedRoots moved handler abandoned (kept.map Address.root) all) :
    ∃ caller, boundary.ambient = caller ++ .handler handler owns :: outer ∧
      ∀ callerRoots, DelimitedRoots moved handler caller (kept.map Address.root) callerRoots →
        (OperationDisposition.Permits program moved callerRoots caller disposition ↔
          OperationDisposition.Permits program moved all abandoned disposition) := by
  obtain ⟨actual,actualMode,ready⟩ := awaiting.operation_ready pending selectedOperation
  have same := actualMode.functional matched
  subst actual
  exact ready.caller_permission (awaiting.outward pending) route prepared selectedRoots

/-- An outward label retains an actual destination and payload preparation,
with permission on its callee-owned post-payload remainder. The caller supplies
its own residual cleanup share when consuming this request. Missing routing or
impossible protection is not permission for an invalid destination. -/
def MayTransfer (program : Kernel.Program) (state : State)
    (boundary : InvocationBoundary) : Prop :=
  ∃ brand result, boundary.OutwardLabel state brand result ∧ boundary.LabelReady program state brand result

theorem MayTransfer.isolated_false {program : Kernel.Program} {state : State} :
    ¬ MayTransfer program state .isolated := by
  rintro ⟨brand,argument,outward,ready⟩
  obtain ⟨abandoned,context,region,type,outer,_,_,route,_⟩ := ready.prepared
  exact outward.2 ⟨abandoned,context,region,type,outer,by simpa only [InvocationBoundary.ambient,List.append_nil] using route⟩

theorem MayTransfer.foreign_free {program : Kernel.Program} {state : State} {boundary : InvocationBoundary}
    (transfer : MayTransfer program state boundary) :
    ∃ callee, state.frames = callee ++ boundary.ambient ∧ ∀ frame ∈ callee, frame.ForeignFree := by
  obtain ⟨_,_,outward,ready⟩ := transfer
  exact ready.foreign_free outward.2

theorem MayTransfer.execute {program : Kernel.Program} {state : State} {boundary : InvocationBoundary}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program state.world) (transfer : MayTransfer program state boundary)
    (caller : ∀ brand argument, boundary.OutwardLabel state brand argument →
      boundary.LabelCallerPermission program state brand argument) :
    ∃ after, ControlStep program state none after ∧ Typing.WorldTyped program after.world := by
  obtain ⟨brand,argument,outward,ready⟩ := transfer
  obtain ⟨context,pending⟩ := outward.1
  exact ready.execute valid inventory typed outward.2 pending (caller brand argument outward)

def StateProgress (program : Kernel.Program) (host : Foreign.Model) (function : Function) (state : State)
    (boundary : InvocationBoundary := .isolated) : Prop :=
  (∃ result, boundary.Normal state result) ∨ (∃ reason, state.task = .fatal reason) ∨
    MayAwait program function state boundary ∨ MayTransfer program state boundary ∨
    ∃ event after, InvocationStep program host boundary state event after

/-- A caller handoff cannot be mistaken for a valid return with the wrong
saved context. Progress admission has no continuation step across the boundary. -/
theorem StateProgress.handoff_normal {program : Kernel.Program} {host : Foreign.Model}
    {function : Function} {state : State} {boundary : InvocationBoundary}
    (progress : StateProgress program host function state boundary)
    (handoff : boundary.Handoff state) : ∃ result, boundary.Normal state result := by
  cases boundary with
  | isolated => exact handoff
  | caller returnTo ambient =>
    obtain ⟨context,result,task,frames⟩ := handoff
    rcases progress with normal | ⟨reason,fatal⟩ | awaiting | transfer | ⟨event,after,step⟩
    · exact normal
    · simp only [task,reduceCtorEq] at fatal
    · obtain ⟨_,_,_,_,_,_,pending,_⟩ := awaiting
      simp only [task,reduceCtorEq] at pending
    · obtain ⟨_,_,⟨⟨_,pending⟩,_⟩,_⟩ := transfer
      simp only [task,reduceCtorEq] at pending
    · exact False.elim (step.not_handoff ⟨context,result,task,frames⟩)

/-- The remaining path-sensitive obligations. Storage typing is not a second
admission premise: `SemanticPreservation` derives it for every execution from
well-formed declarations, the body inventory and the host's actual laws. -/
def ResourceAdmissionAt (program : Kernel.Program) (function : Function) (access : Access) : Prop :=
  ∀ host inputs boundary start trace finish,
    Foreign.Model.Lawful program host → InvocationStart program host function inputs boundary start →
    (∀ input ∈ inputs, (∃ index, input.origin = .capture index) → input.access = access) →
    InvocationRun program host boundary start trace finish →
    StateProgress program host function finish boundary ∧
    (∀ result value, boundary.Normal finish result → finish.world.Stores result value →
      Subtype program.declarations ⟨[],[],0,default,false,{}⟩ value.type function.signature.result) ∧
    (∀ result, boundary.Normal finish result →
      ∀ id root, finish.world.roots.get id = some root → root.live = true →
        (∃ old, start.world.roots.get id = some old) ∨ result.root = id ∨
        (∃ domain, root.home = .allocation domain ∨ root.home = .external domain))

def ResourceAdmission (program : Kernel.Program) (function : Function) : Prop := ResourceAdmissionAt program function .owned

def OriginalInputSurvives (before after : World) (input : InvocationInput) : Prop :=
  ∀ value, before.Stores input.storage value →
    ∃ current, after.Stores input.storage current ∧ current.owner = value.owner ∧ current.type = value.type ∧ current.Initialized

def ReceiverAccess (receiver : Term) (type : Term) (access : Access) : Prop :=
  (receiver = type ∧ access = .owned) ∨
  (∃ region, receiver = .reference .shared region type ∧ access = .shared) ∨
  (∃ region, receiver = .reference .unique region type ∧ access = .unique)

def RelationHolds (program : Kernel.Program) (function : Function) (relation : InvocationRelation) : Prop :=
  relation.arguments = function.signature.parameters ∧ relation.result = function.signature.result ∧
  relation.effects = function.signature.effects ∧ relation.unsafeAllowed = function.signature.unsafeAllowed ∧
  ∃ arguments access,
    ReceiverAccess relation.receiver (.callable function.declaration arguments) access ∧
    (∀ host observation, Foreign.Model.Lawful program host → Observes program host function observation →
      (∀ input ∈ observation.input, (∃ index, input.origin = .capture index) → input.access = access) →
      (∀ result, observation.outcome = .normal result →
        access ≠ .owned → relation.after = relation.access ∧
          ∀ input ∈ observation.input, (∃ index, input.origin = .capture index) → OriginalInputSurvives observation.before observation.after input)) ∧
    ResourceAdmissionAt program function access

def CheckedInterfaces (program : Kernel.Program) : Prop :=
  ∀ declaration, program.declarations.function declaration.header.id = some declaration →
    ∀ arguments function substitution relation,
      Instance program declaration.header.id arguments function → Instantiates declaration.signature.generics arguments substitution →
      relation ∈ declaration.invocations →
      RelationHolds program function
        ⟨relation.receiver.substitute substitution,relation.access.substitute substitution,
          relation.arguments.map (Term.substitute substitution),relation.result.substitute substitution,
          relation.effects.substitute substitution,relation.after.substitute substitution,relation.unsafeAllowed⟩

def PlainBoundary (world : World) (values : List Address) : Prop :=
  ∀ id available, world.availability.get id = some available → available.active = true →
    ∀ address ∈ values, ∀ value path resident, world.Stores address value → ResidentAt value path resident → resident.head ≠ .available id

def ClosedResult (observation : Observation) : Prop :=
  ∀ result, observation.outcome = .normal result → PlainBoundary observation.after [result] ∧
    ∀ id available, observation.after.availability.get id = some available → available.active = true →
      ∃ original, observation.before.availability.get id = some original ∧ original = available

def DropTraceSafe (before : World) (inputs : List InvocationInput) (events : List Event) : Prop :=
    (∀ event ∈ events,
      (∀ brand, event ≠ .leave brand) ∧ (∀ id, event ≠ .suspend id) ∧
      (∀ id last, event ≠ .replay id last)) ∧
    (∀ input ∈ inputs, ∀ value id loan, before.Stores input.storage value → value.head = .reference id →
      before.loans.get id = some loan →
      ∀ source destination, Event.move source destination ∈ events → ¬ source.Overlaps loan.referent)

/-- Normal Drop completion ends the original loan and restores initialized
borrowing storage. Source reassignment may install a new Self owner. This
does not grant an arbitrary ancestor authority: ordinary release can also end
an unreferenced parent, while retained caller authority is a frame obligation. -/
def DropBorrowReturned (self : Term) (after : World) (id : Identity) (original : Loan) : Prop :=
  after.loans.get id = some { original with live := false } ∧
    ∃ current, after.Stores original.referent current ∧ current.type = self ∧ current.Initialized

/-- Destructor restrictions are safety properties of every actual execution
prefix, including a hook that subsequently diverges and has no final outcome. -/
def DropContract (program : Kernel.Program) (self region : Term) (function : Function) : Prop :=
  DropFunction self region function ∧
  (∀ host inputs boundary start events finish, Foreign.Model.Lawful program host →
    InvocationStart program host function inputs boundary start → InvocationRun program host boundary start events finish →
    DropTraceSafe start.world inputs events ∧
      ∀ operation arguments payload, ¬ boundary.OutwardOperation program finish operation arguments payload) ∧
  (∀ host observation, Foreign.Model.Lawful program host → Observes program host function observation →
    ∀ result, observation.outcome = .normal result →
    ∀ input ∈ observation.input, ∀ value id original, observation.before.Stores input.storage value →
      value.head = .reference id → observation.before.loans.get id = some original →
      DropBorrowReturned self observation.after id original) ∧
  ResourceAdmission program function

theorem exact_interface_is_derived (program : Kernel.Program) (function : Function) :
    Derived program function (ExactInterface program function) := by
  constructor
  · intro host observation lawful observed
    exact ⟨host,lawful,observed⟩
  · constructor
    · intro host inputs states events lawful infinite
      exact ⟨host,lawful,infinite⟩
    · intro host observation lawful lifecycle
      exact ⟨host,lawful,lifecycle⟩

theorem unknown_is_not_normal {program : Kernel.Program} {boundary : InvocationBoundary}
    {state : State} : ¬ AtOutcome program boundary state .unknown := by
  intro impossible
  exact impossible

end Glorious.Language.Contracts
