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

/- REMAINING DERIVATION (mechanical, no semantic gap): `Run.NonFatal` is
derivable from a run whose recorded events avoid resource exhaustion
(`Run.nonFatal_of_trace`, by induction: the `visible` case takes the event's
non-fatality from the trace's head) and from a run that ends in a non-fatal task
(using `Step.task_not_fatal`, provable because every `Step` constructor fixes
`before.task` to a non-fatal shape, so a fatal task has no successor step). Both
not-yet-written lemmas only feed the trace/task hypotheses that the three
consumer theorems below now carry explicitly. -/
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
    (lawful : host.Lawful program) (observed : Observes program host function observation)
    (safe : ∀ {a b t} (run : Execution.Run program host a t b), run.NonFatal) :
    ∃ boundary start finish, InvocationStart program host function observation.input boundary start ∧
      start.world = observation.before ∧ Execution.Run program host start observation.events finish ∧
      finish.world = observation.after ∧ AtOutcome program boundary finish observation.outcome ∧
      start.SuspensionsWellFormed ∧ finish.SuspensionsWellFormed := by
  obtain ⟨boundary,start,finish,initial,before,run,after,outcome⟩ := observed
  exact ⟨boundary,start,finish,initial,before,run.execution,after,outcome,initial.suspensions,
    initial.run_suspensions valid inventory lawful run.execution (safe run.execution)⟩

theorem Diverges.suspensions {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput}
    {states : Nat → Execution.State} {events : Nat → Option Execution.Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (infinite : Diverges program host function inputs states events)
    (safe : ∀ {a b t} (run : Execution.Run program host a t b), run.NonFatal) :
    ∀ n, (states n).SuspensionsWellFormed := by
  obtain ⟨boundary,initial,steps⟩ := infinite
  intro n
  exact initial.run_suspensions valid inventory lawful (InvocationRun.prefix steps n).execution
    (safe (InvocationRun.prefix steps n).execution)

end Contracts

namespace Specification

theorem reachable_suspensions {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput} {state : Execution.State}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (reachable : (Semantics program host function inputs).Reachable state)
    (safe : ∀ {a b t} (run : Execution.Run program host a t b), run.NonFatal) :
    state.SuspensionsWellFormed := by
  obtain ⟨start,trace,initial,run⟩ := reachable_execution_iff.mp reachable
  exact initial.run_suspensions valid inventory lawful run (safe run)

end Specification
end Glorious.Language
