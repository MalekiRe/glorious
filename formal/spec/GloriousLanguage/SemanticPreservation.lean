import GloriousLanguage.Specification
import GloriousLanguage.ExecutionPreservation

/-! The public transition system consumes preservation of the actual executable
relation. Its finite traces are exactly the public projections of internal
executions, including internal events which become silent public steps.
Storage safety is derived independently of semantic resource admission; this
does not establish the still-open task/frame progress invariant. -/
namespace Glorious.Language

namespace Contracts

theorem InitialInvocation.run_worldTyped {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput} {start finish : Execution.State}
    {trace : List Execution.Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (initial : InitialInvocation program function inputs start)
    (run : Execution.Run program host start trace finish) : Typing.WorldTyped program finish.world :=
  run.worldTyped valid inventory lawful initial.1.1

theorem Observes.worldTyped {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {observation : Observation}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (observed : Observes program host function observation) :
    Typing.WorldTyped program observation.before ∧ Typing.WorldTyped program observation.after := by
  obtain ⟨start,finish,initial,before,run,after,_⟩ := observed
  exact ⟨before ▸ initial.1.1,after ▸ initial.run_worldTyped valid inventory lawful run⟩

theorem Diverges.worldTyped {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput}
    {states : Nat → Execution.State} {events : Nat → Option Execution.Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (infinite : Diverges program host function inputs states events) :
    ∀ n, Typing.WorldTyped program (states n).world := by
  intro n
  induction n with
  | zero => exact infinite.1.1.1
  | succ n ih => exact (infinite.2 n).worldTyped valid inventory lawful ih

end Contracts

namespace Specification

theorem execution_publicSteps {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput}
    {start finish : Execution.State} {trace : List Execution.Event}
    (run : Execution.Run program host start trace finish) :
    (Semantics program host function inputs).Steps start (trace.filterMap publicEvent) finish := by
  induction run with
  | refl => exact .refl
  | silent step _ ih => exact .silent ⟨none,step,rfl⟩ ih
  | @visible start middle finish event trace step run ih =>
    cases projected : publicEvent event with
    | none =>
      have transition : (Semantics program host function inputs).step start none middle :=
        ⟨some event,step,by simp [projected]⟩
      simpa only [List.filterMap_cons,projected] using
        (TransitionSystem.Steps.silent transition ih)
    | some visibleEvent =>
      have transition : (Semantics program host function inputs).step start (some visibleEvent) middle :=
        ⟨some event,step,by simp [projected]⟩
      simpa only [List.filterMap_cons,projected] using
        (TransitionSystem.Steps.visible transition ih)

theorem publicSteps_execution {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput}
    {start finish : Execution.State} {trace : List PublicEvent}
    (steps : (Semantics program host function inputs).Steps start trace finish) :
    ∃ internal, Execution.Run program host start internal finish ∧ internal.filterMap publicEvent = trace := by
  refine TransitionSystem.Steps.rec
    (motive := fun start trace finish _ => ∃ internal,
      Execution.Run program host start internal finish ∧ internal.filterMap publicEvent = trace)
    ?_ ?_ ?_ steps
  · intro state
    exact ⟨[],.refl,rfl⟩
  · intro start middle finish trace step rest ih
    obtain ⟨internal,run,projected⟩ := ih
    obtain ⟨event,step,hidden⟩ := step
    cases event with
    | none => exact ⟨internal,.silent step run,projected⟩
    | some event =>
      refine ⟨event :: internal,.visible step run,?_⟩
      simp only [Option.bind_some] at hidden
      simpa only [List.filterMap_cons,← hidden] using projected
  · intro start middle finish event trace step rest ih
    obtain ⟨internal,run,projected⟩ := ih
    obtain ⟨event,step,visible⟩ := step
    cases event with
    | none => cases visible
    | some event =>
      refine ⟨event :: internal,.visible step run,?_⟩
      simp only [Option.bind_some] at visible
      simp only [List.filterMap_cons,← visible,projected]

/-- Erasing private events neither introduces nor removes reachable machine
states. This connects public safety to the very same execution relation used
by resource and observation contracts. -/
theorem reachable_execution_iff {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput} {state : Execution.State} :
    (Semantics program host function inputs).Reachable state ↔
      ∃ start trace, Contracts.InitialInvocation program function inputs start ∧
        Execution.Run program host start trace state := by
  constructor
  · rintro ⟨start,trace,initial,steps⟩
    obtain ⟨internal,run,_⟩ := publicSteps_execution steps
    exact ⟨start,internal,initial,run⟩
  · rintro ⟨start,trace,initial,run⟩
    exact ⟨start,trace.filterMap publicEvent,initial,execution_publicSteps run⟩

/-- Reachable public states cannot violate storage typing. In particular,
`FunctionsAdmitted` need not assume this already-proved postcondition. -/
theorem reachable_worldTyped {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput} {state : Execution.State}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (reachable : (Semantics program host function inputs).Reachable state) :
    Typing.WorldTyped program state.world := by
  obtain ⟨start,trace,initial,run⟩ := reachable_execution_iff.mp reachable
  exact initial.run_worldTyped valid inventory lawful run

theorem WellFormed.no_invalid_reachable {program : Kernel.Program} (well : WellFormed program)
    {host : Foreign.Model} {function : Kernel.Function} {inputs : List Kernel.InvocationInput}
    (lawful : host.Lawful program) (state : Execution.State)
    (reachable : (Semantics program host function inputs).Reachable state) :
    ¬ (Semantics program host function inputs).invalid state := by
  exact fun invalid => invalid (reachable_worldTyped well.declarations well.inventory lawful reachable)

end Specification
end Glorious.Language
