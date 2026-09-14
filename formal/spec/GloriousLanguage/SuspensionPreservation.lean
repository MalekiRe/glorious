import GloriousLanguage.SuspensionSource
import GloriousLanguage.ForeignSuspensionOwnership
import GloriousLanguage.PrimitiveSuspensionOwnership
import GloriousLanguage.SemanticPreservation

/-! Whole-machine suspension provenance follows from every real transition.
Budget accounting, immutable capture bounds and current suspended ownership
are one invariant, including arbitrary host mutations and copied replay. -/
namespace Glorious.Language

namespace Execution

theorem Step.suspension_storage {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (suspensions : before.SuspensionsWellFormed)
    (step : Step program host before event after) (notFatal : event ≠ some (.fatal .resource)) :
    after.SuspensionsWellFormed ∧
      ∀ (authority : Authority), authority.Recorded before.world.loans → authority.Recorded after.world.loans := by
  rcases step with localStep | atom | effect | control | primitive | foreign
  · exact ⟨localStep.suspensions suspensions typed.1,localStep.suspensionExtension.recorded⟩
  · exact ⟨atom.suspensions suspensions typed.1,atom.suspensionExtension.recorded⟩
  · exact effect.suspension_storage valid inventory suspensions typed notFatal
  · exact ⟨control.suspensions suspensions typed.1,control.suspensionExtension.recorded⟩
  · exact ⟨primitive.suspensions typed.1 suspensions,primitive.suspensionExtension.recorded⟩
  · exact ⟨foreign.suspensions lawful typed.1 suspensions,(foreign.suspensionExtension lawful typed.1).recorded⟩

/-- Historical authority recording survives every actual step, including
physical exhaustion. It does not assert completed suspension ownership at a
fatal partial-copy endpoint. -/
theorem Step.recorded {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (suspensions : before.SuspensionsWellFormed) (step : Step program host before event after) :
    ∀ authority : Authority, authority.Recorded before.world.loans → authority.Recorded after.world.loans := by
  rcases step with localStep | atom | effect | control | primitive | foreign
  · exact localStep.suspensionExtension.recorded
  · exact atom.suspensionExtension.recorded
  · exact effect.recorded valid inventory suspensions typed
  · exact control.suspensionExtension.recorded
  · exact primitive.suspensionExtension.recorded
  · exact (foreign.suspensionExtension lawful typed.1).recorded


theorem Step.suspensions {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (suspensions : before.SuspensionsWellFormed)
    (step : Step program host before event after) (notFatal : event ≠ some (.fatal .resource)) :
    after.SuspensionsWellFormed :=
  (step.suspension_storage valid inventory lawful typed suspensions notFatal).1

/-- A run none of whose steps fails on resource exhaustion. The machine's fatal
states are absorbing (`task := .fatal ...`), so the suspension invariant is
retained along exactly these runs; the failing relocation steps are the ones
that publish a fatal state and are handled as terminals, not as transitions. -/
inductive Run.NonFatal {program : Kernel.Program} {host : Foreign.Model} :
    {before : State} → {trace : List Event} → {after : State} → Run program host before trace after → Prop where
  | refl {state} : Run.NonFatal (.refl (program := program) (host := host) (state := state))
  | silent {before middle after trace} (step : Step program host before none middle)
      (tail : Run program host middle trace after) (tailPred : Run.NonFatal tail) :
      Run.NonFatal (.silent step tail)
  | visible {before middle after event trace} (step : Step program host before (some event) middle)
      (neutral : some event ≠ some (.fatal .resource)) (tail : Run program host middle trace after)
      (tailPred : Run.NonFatal tail) : Run.NonFatal (.visible step tail)

/-- Every effect instruction starts from a non-fatal task: a failing step
publishes the fatal task, so a fatal task has no effect successor. -/
theorem EffectStep.task_not_fatal {program : Kernel.Program} {before after : State} {event : Option Event}
    (step : EffectStep program before event after) {reason : Fatal} : before.task ≠ .fatal reason := by
  cases step <;> intro h <;> simp_all

/-- Fatal tasks have no successor in the actual union of machine rules. -/
theorem Step.task_not_fatal {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {event : Option Event} (step : Step program host before event after)
    {reason : Fatal} : before.task ≠ .fatal reason := by
  rcases step with step | step | step | step | step | step <;>
    cases step <;> intro impossible <;> simp_all only [reduceCtorEq]

/-- Every published fatal event names the actual terminal task. -/
theorem Step.fatal_task {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {reason : Fatal} (step : Step program host before (some (.fatal reason)) after) :
    after.task = .fatal reason := by
  generalize eventAt : some (Event.fatal reason) = event at step
  rcases step with step | step | step | step | step | step <;> cases step <;> simp_all
  all_goals split at eventAt <;> simp_all
  all_goals split at eventAt <;> simp_all

/-- A run starting at an actual fatal task cannot execute another step. -/
theorem Run.after_eq_of_fatal {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event} (run : Run program host before trace after)
    {reason : Fatal} (fatal : before.task = .fatal reason) : after = before := by
  cases run with
  | refl => rfl
  | silent step _ | visible step _ => exact False.elim (step.task_not_fatal fatal)


theorem Run.task_not_fatal_of_final {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event} (run : Run program host before trace after)
    {reason : Fatal} (final : after.task ≠ .fatal reason) : before.task ≠ .fatal reason := by
  cases run with
  | refl => exact final
  | silent step _ | visible step _ => exact step.task_not_fatal

/-- A real non-resource-fatal endpoint rules out an earlier exhaustion event:
that event would have produced a terminal task with no following step. -/
theorem Run.nonFatal_of_final {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event} (run : Run program host before trace after)
    (final : after.task ≠ .fatal .resource) : run.NonFatal := by
  induction run with
  | refl => exact .refl
  | silent step tail ih => exact .silent step tail (ih final)
  | visible step tail ih =>
    refine .visible step ?_ tail (ih final)
    intro equal
    cases equal
    exact (tail.task_not_fatal_of_final final) step.fatal_task


/-- A run whose every recorded event avoids resource exhaustion is non-fatal. -/
theorem Run.nonFatal_of_trace {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event} (run : Run program host before trace after)
    (safe : ∀ event ∈ trace, event ≠ .fatal .resource) : run.NonFatal := by
  induction run with
  | refl => exact .refl
  | silent step tail ih => exact .silent step tail (ih safe)
  | visible step tail ih =>
    exact .visible step (by
      intro h
      exact safe _ List.mem_cons_self (Option.some.inj h)) tail
      (ih (fun event member => safe event (List.mem_cons_of_mem _ member)))

/-- Every finite prefix retains the same complete suspension invariant;
arbitrary body execution is included, not restricted to cleanup tasks. -/
theorem Run.suspension_storage {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (suspensions : before.SuspensionsWellFormed)
    (run : Run program host before trace after) (safe : run.NonFatal) : after.SuspensionsWellFormed ∧
      ∀ (authority : Authority), authority.Recorded before.world.loans → authority.Recorded after.world.loans := by
  induction safe with
  | refl => exact ⟨suspensions,fun _ recorded => recorded⟩
  | silent step tail tailPred ih =>
    have silentStep : (none : Option Event) ≠ some (.fatal .resource) := by intro h; cases h
    have first := step.suspension_storage valid inventory lawful typed suspensions silentStep
    have last := ih (step.worldTyped valid inventory lawful typed) first.1
    exact ⟨last.1,fun authority recorded => last.2 authority (first.2 authority recorded)⟩
  | visible step neutral tail tailPred ih =>
    have first := step.suspension_storage valid inventory lawful typed suspensions neutral
    have last := ih (step.worldTyped valid inventory lawful typed) first.1
    exact ⟨last.1,fun authority recorded => last.2 authority (first.2 authority recorded)⟩

theorem Run.suspensions {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (suspensions : before.SuspensionsWellFormed)
    (run : Run program host before trace after) (safe : run.NonFatal) : after.SuspensionsWellFormed :=
  (run.suspension_storage valid inventory lawful typed suspensions safe).1

/-- Complete ownership is retained at a running endpoint. Exhaustion instead
retains its actual terminal partial world, whose historical records are handled
by the unconditional recording theorem. -/
theorem Run.suspensions_or_fatal {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (suspensions : before.SuspensionsWellFormed) (run : Run program host before trace after) :
    after.SuspensionsWellFormed ∨ after.task = .fatal .resource := by
  by_cases fatal : after.task = .fatal .resource
  · exact Or.inr fatal
  · exact Or.inl (run.suspensions valid inventory lawful typed suspensions (run.nonFatal_of_final fatal))


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

/-- Later replay or settlement cannot add newly allocated storage to an old
inventory. This consumes the same immutable metadata theorem as budgets. -/
theorem Run.old_inventory_excludes_future_root {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event} {id root : Identity} {original current : Suspension}
    (valid : before.SuspensionsWellFormed) (run : Run program host before trace after)
    (beforeAt : before.resumptions.get id = some original) (afterAt : after.resumptions.get id = some current)
    (future : before.world.nextRoot ≤ root) : root ∉ current.roots := by
  obtain ⟨retained,found,_,roots,_,_,_⟩ := run.retains_metadata valid.budgets beforeAt
  have same : retained = current := Option.some.inj (found.symm.trans afterAt)
  subst retained
  rw [roots]
  exact valid.excludes_future_root beforeAt future

/-- An actual cancellation of a pre-existing suspension cannot schedule a
freshly allocated root for destruction, even after arbitrary body execution. -/
theorem Run.cancel_old_excludes_future_root {program : Kernel.Program} {host : Foreign.Model}
    {before after canceled : State} {trace : List Event} {id root : Identity} {original : Suspension}
    (valid : before.SuspensionsWellFormed) (run : Run program host before trace after)
    (beforeAt : before.resumptions.get id = some original) (future : before.world.nextRoot ≤ root)
    (cancellation : EffectStep program after (some (.cancel id)) canceled) :
    ∀ context roots next, canceled.task = .cleanup context roots next → root ∉ roots := by
  cases cancellation with
  | cancel task currentAt active optional disposable =>
    intro context roots next scheduled
    have same := (Task.cleanup.inj scheduled).2.1
    rw [← same]
    exact run.old_inventory_excludes_future_root valid beforeAt currentAt future

end Execution

namespace Contracts

theorem InvocationStart.suspensions {program : Kernel.Program} {host : Foreign.Model} {function : Kernel.Function}
    {inputs : List Kernel.InvocationInput} {state : Execution.State}
    {boundary : InvocationBoundary} (initial : InvocationStart program host function inputs boundary state) : state.SuspensionsWellFormed := initial.2.2.1.suspensions

theorem InvocationStart.run_suspensions {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput} {start finish : Execution.State}
    {trace : List Execution.Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) {boundary : InvocationBoundary} (initial : InvocationStart program host function inputs boundary start)
    (run : Execution.Run program host start trace finish) (safe : run.NonFatal) :
    finish.SuspensionsWellFormed :=
  run.suspensions valid inventory lawful initial.1.1 initial.suspensions safe

/-- Observations retain the actual witnessed control states and their
inventories. No independent abstract-world table is reconstructed. -/
theorem Observes.suspensions {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {observation : Observation}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (observed : Observes program host function observation) :
    ∃ boundary start finish, InvocationStart program host function observation.input boundary start ∧
      start.world = observation.before ∧ Execution.Run program host start observation.events finish ∧
      finish.world = observation.after ∧ AtOutcome program boundary finish observation.outcome ∧
      start.SuspensionsWellFormed ∧ (finish.SuspensionsWellFormed ∨ finish.task = .fatal .resource) := by
  obtain ⟨boundary,start,finish,initial,before,run,after,outcome⟩ := observed
  exact ⟨boundary,start,finish,initial,before,run.execution,after,outcome,initial.suspensions,
    run.execution.suspensions_or_fatal valid inventory lawful initial.1.1 initial.suspensions⟩

theorem Diverges.suspensions {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput}
    {states : Nat → Execution.State} {events : Nat → Option Execution.Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (infinite : Diverges program host function inputs states events) :
    ∀ n, (states n).SuspensionsWellFormed := by
  obtain ⟨boundary,initial,steps⟩ := infinite
  intro n
  exact initial.run_suspensions valid inventory lawful (InvocationRun.prefix steps n).execution
    ((InvocationRun.prefix steps n).execution.nonFatal_of_final (steps n).2.task_not_fatal)

end Contracts

namespace Specification

theorem reachable_suspensions {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput} {state : Execution.State}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (reachable : (Semantics program host function inputs).Reachable state) :
    state.SuspensionsWellFormed ∨ state.task = .fatal .resource := by
  obtain ⟨start,trace,initial,run⟩ := reachable_execution_iff.mp reachable
  exact run.suspensions_or_fatal valid inventory lawful initial.1.1 initial.suspensions

end Specification
end Glorious.Language
