import GloriousLanguage.ControlForeignOrigin
import GloriousLanguage.ControlAuthorityForeign
import GloriousLanguage.ActivationPreservation

/-! Whole-machine provenance of actual current and saved control. Complete
ownership is preserved along non-resource-fatal execution. Fatal endpoints
remain actual terminals; historical saved metadata never gains future roots,
loans or activations, even through an interrupted final step.

`Step.taskFrameInvariant` states the complete live task/frame invariant as one
predicate and proves it from the actual per-family control and authority
producers; `State.ControlWellFormed` extends it with the saved-control
invariant, and `Specification.WellFormed.no_invalid_reachable` feeds that
invariant to the public safety chain. The remaining gaps are honest scope
limits, each because no producer exists rather than because the statement is
hard: (1) liveness and progress of the destructor bodies and foreign hook
bodies that a retained task or frame still names -- only the historical root
bound and the recorded authorities of those control products are claimed; (2) a
structural lockstep relation between the task continuation chain and the frame
stack -- the machine maintains no such producer and none is claimed; (3) the
initialized-return obligation is still discharged only from the assumed
`Contracts.ResourceAdmissionAt`, never from this invariant. -/
namespace Glorious.Language

namespace Execution

/-- The complete invariant of the live task and its retained frames, composed
from the actual per-family control and authority producers. Effect transitions
consume the saved-control component of the pre-state because replay re-installs
a saved task and frame stack; every other family consumes only its own live
task/frame facts. -/
theorem Step.taskFrameInvariant {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (control : before.ControlWellFormed) (step : Step program host before event after) :
    after.TaskFrameInvariant := by
  have support :
      (RootSupport.Below after.task.rootSupport after.world.nextRoot ∧
        RootSupport.Below (after.frames.flatMap Frame.rootSupport) after.world.nextRoot) ∧
      (AuthoritySupport.Recorded after.task.authoritySupport after.world.loans ∧
        AuthoritySupport.Recorded (after.frames.flatMap Frame.authoritySupport) after.world.loans) := by
    rcases step with localStep | atom | effect | branch | primitive | foreign
    · exact ⟨localStep.control_support valid inventory typed control.task control.frames,
        localStep.authority_support typed control.taskAuthorities control.frameAuthorities⟩
    · exact ⟨atom.control_support typed.1 control.task control.frames,
        atom.authority_support control.taskAuthorities control.frameAuthorities⟩
    · exact ⟨effect.control_support valid inventory typed control,
        effect.authority_support valid inventory typed control.suspensions
          control.taskAuthorities control.frameAuthorities control.savedAuthorities⟩
    · exact ⟨branch.control_support valid inventory typed control.task control.frames,
        branch.authority_support typed.1 control.taskAuthorities control.frameAuthorities⟩
    · exact ⟨primitive.control_support control.task control.frames,
        primitive.authority_support control.taskAuthorities control.frameAuthorities⟩
    · exact ⟨foreign.control_support valid inventory lawful typed control.task control.frames,
        foreign.authority_support lawful typed.1 control.taskAuthorities control.frameAuthorities⟩
  exact ⟨support.1.1,support.1.2,support.2.1,support.2.2⟩

theorem Step.controlWellFormed {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (control : before.ControlWellFormed) (step : Step program host before event after)
    (notFatal : event ≠ some (.fatal .resource)) :
    after.ControlWellFormed := by
  exact ⟨step.taskFrameInvariant valid inventory lawful typed control,
    step.suspensions valid inventory lawful typed control.suspensions notFatal,
    step.saved_control_origin control,
    step.saved_authority_origin valid inventory lawful typed control.suspensions
      control.taskAuthorities control.frameAuthorities control.savedAuthorities,
    step.activationsWellFormed lawful typed.1 control.suspensions control.activations⟩

theorem Run.controlWellFormed {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (control : before.ControlWellFormed) (run : Run program host before trace after) (safe : run.NonFatal) :
    after.ControlWellFormed := by
  induction safe with
  | refl => exact control
  | silent step tail tailPred ih =>
    exact ih (step.worldTyped valid inventory lawful typed)
      (step.controlWellFormed valid inventory lawful typed control (by intro impossible; cases impossible))
  | visible step neutral tail tailPred ih =>
    exact ih (step.worldTyped valid inventory lawful typed)
      (step.controlWellFormed valid inventory lawful typed control neutral)

theorem Run.controlWellFormed_or_fatal {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (control : before.ControlWellFormed) (run : Run program host before trace after) :
    after.ControlWellFormed ∨ after.task = .fatal .resource := by
  by_cases fatal : after.task = .fatal .resource
  · exact Or.inr fatal
  · exact Or.inl (run.controlWellFormed valid inventory lawful typed control (run.nonFatal_of_final fatal))

/-- The live task/frame invariant follows along the same non-resource-fatal runs
through the actual control producers. Replay re-installs saved control, so the
complete pre-state control invariant remains the hypothesis of the run. -/
theorem Run.taskFrameInvariant {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (control : before.ControlWellFormed) (run : Run program host before trace after) (safe : run.NonFatal) :
    after.TaskFrameInvariant :=
  (run.controlWellFormed valid inventory lawful typed control safe).toTaskFrameInvariant

theorem Run.taskFrameInvariant_or_fatal {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (control : before.ControlWellFormed) (run : Run program host before trace after) :
    after.TaskFrameInvariant ∨ after.task = .fatal .resource := by
  by_cases fatal : after.task = .fatal .resource
  · exact Or.inr fatal
  · exact Or.inl (run.taskFrameInvariant valid inventory lawful typed control (run.nonFatal_of_final fatal))


/-- An old suspension cannot acquire an address of storage allocated after
that suspension was admitted, even after arbitrary execution and settlement.
The actual immutable control metadata suffices, including at a fatal endpoint. -/
theorem Run.old_saved_control_excludes_future_root {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event} {id root : Identity} {original current : Suspension}
    (control : before.ControlWellFormed) (run : Run program host before trace after)
    (beforeAt : before.resumptions.get id = some original) (afterAt : after.resumptions.get id = some current)
    (future : before.world.nextRoot ≤ root) : root ∉ current.controlRootSupport := by
  obtain ⟨retained,present,_,_,_,_,context,handler,frames,_⟩ := run.retains_metadata control.suspensions.budgets beforeAt
  have same := Option.some.inj (present.symm.trans afterAt)
  subst retained
  have support : current.controlRootSupport = original.controlRootSupport := by
    simp only [Suspension.controlRootSupport,context,handler,frames]
  rw [support]
  exact control.no_future_saved beforeAt future


/-- Capture metadata is immutable through arbitrary execution. Consequently
an old context, frame, callback lease or pending cleanup cannot acquire a
later-created loan identity merely because that identity eventually exists. -/
theorem Run.old_saved_authority_excludes_future_loan {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event} {id loan : Identity} {original current : Suspension}
    (well : before.world.WellFormed) (control : before.ControlWellFormed)
    (run : Run program host before trace after)
    (beforeAt : before.resumptions.get id = some original) (afterAt : after.resumptions.get id = some current)
    (future : before.world.nextLoan ≤ loan) :
    ∀ authority ∈ current.controlAuthoritySupport, authority.parentLoan ≠ some loan := by
  obtain ⟨retained,present,_,_,_,_,context,handler,frames,_⟩ := run.retains_metadata control.suspensions.budgets beforeAt
  have same := Option.some.inj (present.symm.trans afterAt)
  subst retained
  have support : current.controlAuthoritySupport = original.controlAuthoritySupport := by
    simp only [Suspension.controlAuthoritySupport,context,handler,frames]
  rw [support]
  exact control.no_future_saved_authority well beforeAt future

/-- Replay and settlement cannot insert a later activation into old saved
control. This includes pending cleanup contexts and explicit frame owners. -/
theorem Run.old_saved_control_excludes_future_activation {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event} {id activation : Identity} {original current : Suspension}
    (control : before.ControlWellFormed) (run : Run program host before trace after)
    (beforeAt : before.resumptions.get id = some original) (afterAt : after.resumptions.get id = some current)
    (future : before.nextActivation ≤ activation) : activation ∉ current.controlActivationSupport := by
  obtain ⟨retained,present,_,_,_,_,context,handler,frames,_⟩ := run.retains_metadata control.suspensions.budgets beforeAt
  have same := Option.some.inj (present.symm.trans afterAt)
  subst retained
  have support : current.controlActivationSupport = original.controlActivationSupport := by
    simp only [Suspension.controlActivationSupport,context,handler,frames]
  rw [support]
  intro member
  exact Nat.not_lt_of_ge future (control.activations.saved id original beforeAt activation member)

/-- A home saved before an activation was created cannot later be restored as
that activation's storage. This follows the real immutable restoration map. -/
theorem Run.old_saved_home_excludes_future_activation {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event} {id activation root : Identity}
    {original current : Suspension} {home : Home}
    (control : before.ControlWellFormed) (run : Run program host before trace after)
    (beforeAt : before.resumptions.get id = some original) (afterAt : after.resumptions.get id = some current)
    (future : before.nextActivation ≤ activation) (found : current.homes.get root = some home) :
    ¬ Kernel.HomeOwnedByActivation home activation := by
  obtain ⟨retained,present,_,_,homes,_⟩ := run.retains_metadata control.suspensions.budgets beforeAt
  have same := Option.some.inj (present.symm.trans afterAt)
  subst retained
  rw [homes] at found
  exact fun owned => Nat.not_lt_of_ge future
    ((control.suspensions.origin id original beforeAt).homes_activationsBelow
      (control.activations.saved id original beforeAt) found activation owned)

end Execution

namespace Contracts

theorem InvocationStart.control {program : Kernel.Program} {host : Foreign.Model} {function : Kernel.Function}
    {inputs : List Kernel.InvocationInput} {state : Execution.State}
    {boundary : InvocationBoundary} (initial : InvocationStart program host function inputs boundary state) : state.ControlWellFormed := initial.2.2.1

theorem InvocationStart.run_control {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput} {start finish : Execution.State}
    {trace : List Execution.Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) {boundary : InvocationBoundary} (initial : InvocationStart program host function inputs boundary start)
    (run : Execution.Run program host start trace finish) (safe : run.NonFatal) : finish.ControlWellFormed :=
  run.controlWellFormed valid inventory lawful initial.1.1 initial.control safe

theorem Observes.control {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {observation : Observation}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (observed : Observes program host function observation) :
    ∃ boundary start finish, InvocationStart program host function observation.input boundary start ∧
      start.world = observation.before ∧ Execution.Run program host start observation.events finish ∧
      finish.world = observation.after ∧ AtOutcome program boundary finish observation.outcome ∧
      start.ControlWellFormed ∧ (finish.ControlWellFormed ∨ finish.task = .fatal .resource) := by
  obtain ⟨boundary,start,finish,initial,before,run,after,outcome⟩ := observed
  exact ⟨boundary,start,finish,initial,before,run.execution,after,outcome,initial.control,
    run.execution.controlWellFormed_or_fatal valid inventory lawful initial.1.1 initial.control⟩

theorem Diverges.control {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput}
    {states : Nat → Execution.State} {events : Nat → Option Execution.Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (infinite : Diverges program host function inputs states events) :
    ∀ n, (states n).ControlWellFormed := by
  obtain ⟨boundary,initial,steps⟩ := infinite
  intro n
  exact initial.run_control valid inventory lawful (InvocationRun.prefix steps n).execution
    ((InvocationRun.prefix steps n).execution.nonFatal_of_final (steps n).2.task_not_fatal)

end Contracts

namespace Specification

/-- Every reachable public state retains complete control provenance, except at
the resource-exhaustion terminal, which is a legitimate endpoint rather than an
ill-formed state. -/
theorem reachable_control {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput} {state : Execution.State}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (reachable : (Semantics program host function inputs).Reachable state) :
    state.ControlWellFormed ∨ state.task = .fatal .resource := by
  obtain ⟨start,trace,initial,run⟩ := reachable_execution_iff.mp reachable
  exact run.controlWellFormed_or_fatal valid inventory lawful initial.1.1 initial.control

/-- The same reachable states retain the live task/frame invariant. This is the
part of control provenance the public safety chain exposes directly. -/
theorem reachable_taskFrameInvariant {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput} {state : Execution.State}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (reachable : (Semantics program host function inputs).Reachable state) :
    state.TaskFrameInvariant ∨ state.task = .fatal .resource := by
  rcases reachable_control valid inventory lawful reachable with control | fatal
  · exact Or.inl control.toTaskFrameInvariant
  · exact Or.inr fatal

/-- The strengthened public invalidity predicate is unreachable: storage typing
always holds, and control provenance holds except at the resource-exhaustion
terminal. `FunctionsAdmitted` therefore need not assume either. -/
theorem WellFormed.no_invalid_reachable {program : Kernel.Program} (well : WellFormed program)
    {host : Foreign.Model} {function : Kernel.Function} {inputs : List Kernel.InvocationInput}
    (lawful : host.Lawful program) (state : Execution.State)
    (reachable : (Semantics program host function inputs).Reachable state) :
    ¬ (Semantics program host function inputs).invalid state := by
  intro invalid
  exact invalid ⟨reachable_worldTyped well.declarations well.inventory lawful reachable,
    reachable_control well.declarations well.inventory lawful reachable⟩

end Specification
end Glorious.Language
