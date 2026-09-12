import GloriousLanguage.ControlForeignOrigin

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
  have support : RootSupport.Below after.task.rootSupport after.world.nextRoot ∧
      RootSupport.Below (after.frames.flatMap Frame.rootSupport) after.world.nextRoot := by
    rcases step with localStep | atom | effect | branch | primitive | foreign
    · exact localStep.control_support valid inventory typed control.task control.frames
    · exact atom.control_support typed.1 control.task control.frames
    · exact effect.control_support valid inventory typed control
    · exact branch.control_support valid inventory typed control.task control.frames
    · exact primitive.control_support control.task control.frames
    · exact foreign.control_support valid inventory lawful typed control.task control.frames
  exact ⟨step.suspensions valid inventory lawful typed control.suspensions,
    support.1,support.2,step.saved_control_origin control⟩

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

end Execution

namespace Contracts

theorem InitialInvocation.control {program : Kernel.Program} {function : Kernel.Function}
    {inputs : List Kernel.InvocationInput} {state : Execution.State}
    (initial : InitialInvocation program function inputs state) : state.ControlWellFormed := initial.2.2.1

theorem InitialInvocation.run_control {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput} {start finish : Execution.State}
    {trace : List Execution.Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (initial : InitialInvocation program function inputs start)
    (run : Execution.Run program host start trace finish) : finish.ControlWellFormed :=
  run.controlWellFormed valid inventory lawful initial.1.1 initial.control

theorem Observes.control {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {observation : Observation}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (observed : Observes program host function observation) :
    ∃ start finish, InitialInvocation program function observation.input start ∧
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
