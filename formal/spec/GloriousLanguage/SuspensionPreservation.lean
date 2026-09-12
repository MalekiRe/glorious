import GloriousLanguage.SuspensionSource
import GloriousLanguage.ForeignSuspensionOwnership
import GloriousLanguage.PrimitiveSuspensionOwnership
import GloriousLanguage.SemanticPreservation

/-! Whole-machine suspension provenance follows from every real transition.
Budget accounting, immutable capture bounds and current suspended ownership
are one invariant, including arbitrary host mutations and copied replay. -/
namespace Glorious.Language

namespace Execution

theorem Step.suspensions {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (suspensions : before.SuspensionsWellFormed)
    (step : Step program host before event after) : after.SuspensionsWellFormed := by
  rcases step with localStep | atom | effect | control | primitive | foreign
  · exact localStep.suspensions suspensions typed.1
  · exact atom.suspensions suspensions typed.1
  · exact effect.suspensions valid inventory suspensions typed
  · exact control.suspensions suspensions typed.1
  · exact primitive.suspensions typed.1 suspensions
  · exact foreign.suspensions lawful typed.1 suspensions

/-- Every finite prefix retains the same complete suspension invariant;
arbitrary body execution is included, not restricted to cleanup tasks. -/
theorem Run.suspensions {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (suspensions : before.SuspensionsWellFormed)
    (run : Run program host before trace after) : after.SuspensionsWellFormed := by
  induction run with
  | refl => exact suspensions
  | silent step _ ih | visible step _ ih =>
    exact ih (step.worldTyped valid inventory lawful typed) (step.suspensions valid inventory lawful typed suspensions)

theorem State.SuspensionsWellFormed.root_bound {state : State} (valid : state.SuspensionsWellFormed)
    {id root : Identity} {suspension : Suspension} (found : state.resumptions.get id = some suspension)
    (member : root ∈ suspension.roots) : root < state.world.nextRoot :=
  Nat.lt_of_lt_of_le ((valid.origin id suspension found).bounded root member) (valid.frontier id suspension found)

/-- Even inactive historical inventories exclude future storage. Otherwise
a later cancellation could name a newly allocated private handle. -/
theorem State.SuspensionsWellFormed.excludes_future_root {state : State} (valid : state.SuspensionsWellFormed)
    {id root : Identity} {suspension : Suspension} (found : state.resumptions.get id = some suspension)
    (future : state.world.nextRoot ≤ root) : root ∉ suspension.roots :=
  fun member => Nat.not_lt_of_ge future (valid.root_bound found member)

end Execution

namespace Contracts

theorem InitialInvocation.suspensions {program : Kernel.Program} {function : Kernel.Function}
    {inputs : List Kernel.InvocationInput} {state : Execution.State}
    (initial : InitialInvocation program function inputs state) : state.SuspensionsWellFormed := initial.2.2.1

theorem InitialInvocation.run_suspensions {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput} {start finish : Execution.State}
    {trace : List Execution.Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (initial : InitialInvocation program function inputs start)
    (run : Execution.Run program host start trace finish) : finish.SuspensionsWellFormed :=
  run.suspensions valid inventory lawful initial.1.1 initial.suspensions

/-- Observations retain the actual witnessed control states and their
inventories. No independent abstract-world table is reconstructed. -/
theorem Observes.suspensions {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {observation : Observation}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (observed : Observes program host function observation) :
    ∃ start finish, InitialInvocation program function observation.input start ∧
      start.world = observation.before ∧ Execution.Run program host start observation.events finish ∧
      finish.world = observation.after ∧ AtOutcome finish observation.outcome ∧
      start.SuspensionsWellFormed ∧ finish.SuspensionsWellFormed := by
  obtain ⟨start,finish,initial,before,run,after,outcome⟩ := observed
  exact ⟨start,finish,initial,before,run,after,outcome,initial.suspensions,
    initial.run_suspensions valid inventory lawful run⟩

theorem Diverges.suspensions {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput}
    {states : Nat → Execution.State} {events : Nat → Option Execution.Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (infinite : Diverges program host function inputs states events) :
    ∀ n, (states n).SuspensionsWellFormed := by
  intro n
  exact infinite.1.run_suspensions valid inventory lawful (Execution.Run.prefix infinite.2 n)

end Contracts

namespace Specification

theorem reachable_suspensions {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput} {state : Execution.State}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (reachable : (Semantics program host function inputs).Reachable state) :
    state.SuspensionsWellFormed := by
  obtain ⟨start,trace,initial,run⟩ := reachable_execution_iff.mp reachable
  exact initial.run_suspensions valid inventory lawful run

end Specification
end Glorious.Language
