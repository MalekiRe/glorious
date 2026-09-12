import GloriousLanguage.ControlForeignOrigin
import GloriousLanguage.ControlAuthorityForeign
import GloriousLanguage.ActivationPreservation

/-! Whole-machine provenance of actual current and saved control. The
canonical invocation contract supplies this invariant; all finite and
infinite execution consumers obtain it by preservation, not admission. -/
namespace Glorious.Language

namespace Execution

theorem Step.controlWellFormed {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (control : before.ControlWellFormed) (step : Step program host before event after) :
    after.ControlWellFormed := by
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
  exact ⟨step.suspensions valid inventory lawful typed control.suspensions,
    support.1.1,support.1.2,step.saved_control_origin control,support.2.1,support.2.2,
    step.saved_authority_origin valid inventory lawful typed control.suspensions
      control.taskAuthorities control.frameAuthorities control.savedAuthorities,
    step.activationsWellFormed lawful typed.1 control.suspensions control.activations⟩

theorem Run.controlWellFormed {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (control : before.ControlWellFormed) (run : Run program host before trace after) :
    after.ControlWellFormed := by
  induction run with
  | refl => exact control
  | silent step _ ih | visible step _ ih =>
    exact ih (step.worldTyped valid inventory lawful typed) (step.controlWellFormed valid inventory lawful typed control)

/-- An old suspension cannot acquire an address of storage allocated after
that suspension was admitted, even after arbitrary execution and settlement.
This consumes the actual retained metadata and complete control invariant. -/
theorem Run.old_saved_control_excludes_future_root {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event} {id root : Identity} {original current : Suspension}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (control : before.ControlWellFormed) (run : Run program host before trace after)
    (beforeAt : before.resumptions.get id = some original) (afterAt : after.resumptions.get id = some current)
    (future : before.world.nextRoot ≤ root) : root ∉ current.controlRootSupport := by
  obtain ⟨retained,present,_,_,_,limit,_⟩ := run.retains_metadata control.suspensions.budgets beforeAt
  have same := Option.some.inj (present.symm.trans afterAt)
  subst retained
  have finish := run.controlWellFormed valid inventory lawful typed control
  intro member
  have below := finish.saved id current afterAt root member
  rw [limit] at below
  exact Nat.not_lt_of_ge future (Nat.lt_of_lt_of_le below (control.suspensions.frontier id original beforeAt))

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

theorem InitialInvocation.control {program : Kernel.Program} {host : Foreign.Model} {function : Kernel.Function}
    {inputs : List Kernel.InvocationInput} {state : Execution.State}
    (initial : InitialInvocation program host function inputs state) : state.ControlWellFormed := initial.2.2.1

theorem InitialInvocation.caller_activation_bound {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput} {state : Execution.State}
    {caller : Execution.Context}
    (initial : InitialInvocation program host function inputs state)
    (task : state.task = .enter caller function (.supplied inputs) false) : caller.activation < state.nextActivation := by
  have bounded := initial.control.activations.task
  simpa only [task,Execution.Task.activationSupport,RootSupport.below_cons,RootSupport.below_nil,and_true] using bounded

theorem InitialInvocation.run_control {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput} {start finish : Execution.State}
    {trace : List Execution.Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (initial : InitialInvocation program host function inputs start)
    (run : Execution.Run program host start trace finish) : finish.ControlWellFormed :=
  run.controlWellFormed valid inventory lawful initial.1.1 initial.control

theorem Observes.control {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {observation : Observation}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (observed : Observes program host function observation) :
    ∃ start finish, InitialInvocation program host function observation.input start ∧
      start.world = observation.before ∧ Execution.Run program host start observation.events finish ∧
      finish.world = observation.after ∧ AtOutcome finish observation.outcome ∧
      start.ControlWellFormed ∧ finish.ControlWellFormed := by
  obtain ⟨start,finish,initial,before,run,after,outcome⟩ := observed
  exact ⟨start,finish,initial,before,run,after,outcome,initial.control,
    initial.run_control valid inventory lawful run⟩

theorem Diverges.control {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput}
    {states : Nat → Execution.State} {events : Nat → Option Execution.Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (infinite : Diverges program host function inputs states events) :
    ∀ n, (states n).ControlWellFormed := by
  intro n
  exact infinite.1.run_control valid inventory lawful (Execution.Run.prefix infinite.2 n)

end Contracts

namespace Specification

theorem reachable_control {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput} {state : Execution.State}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (reachable : (Semantics program host function inputs).Reachable state) :
    state.ControlWellFormed := by
  obtain ⟨start,trace,initial,run⟩ := reachable_execution_iff.mp reachable
  exact initial.run_control valid inventory lawful run

end Specification
end Glorious.Language
