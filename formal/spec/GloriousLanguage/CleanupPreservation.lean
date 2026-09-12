import GloriousLanguage.BorrowPreservation
import GloriousLanguage.LifecyclePreservation
import GloriousLanguage.RehomePreservation

/-! Preservation for the actual machine cleanup tasks, including cancellation,
reservation disposal and destructor entry. Executing a destructor's arbitrary
body still belongs to the whole-machine invocation/control invariant. -/
namespace Glorious.Language.Execution

/-- Select existing machine tasks; this is not a second cleanup interpreter. -/
def Task.Cleanup : Task → Prop
  | .destroy .. | .destroyFields .. | .finishShell .. | .retire .. | .cleanup ..
  | .closeRegion .. | .closeLoan .. | .releaseLoan .. | .transfer .. | .cancel .. => True
  | _ => False

/-- A proof view of the storage relations used by actual cleanup transitions.
The classification theorem below derives it from `Step`. -/
inductive CleanupWorldChange (program : Kernel.Program) : World → World → Prop where
  | unchanged {world} : CleanupWorldChange program world world
  | clear {before after address authority} : Permitted before authority .owned address →
      before.write address none = some after → CleanupWorldChange program before after
  /-- Returning storage-loan custody precedes the actual shell write; the
  write is performed on the relinquished world, not on the old loan table. -/
  | relinquished {before relinquished after address authority custody} :
      Permitted before authority .owned address →
      RelinquishesCustody before custody relinquished →
      relinquished.write address none = some after → CleanupWorldChange program before after
  | transfer {before after source destination authority} :
      Transfers program before authority source destination after → CleanupWorldChange program before after
  /-- Destructor entry forms the actual destructor lease, not a source borrow. -/
  | hook {before allocated after context type handle authority referent} :
      Temporary program context (.reference .unique (.runtimeRegion context.region) type) before handle allocated →
      FormsLoan program .destructor allocated authority .unique context.region referent handle after →
      CleanupWorldChange program before after
  | retire {before after id} : Retires before id after → CleanupWorldChange program before after
  | region {before after id} : RegionEnds before id after → CleanupWorldChange program before after
  | loan {before after id} : EndsLoan program before id after → CleanupWorldChange program before after
  | storageReturn {before after id} : ReturnsStorageLoan before id after →
      CleanupWorldChange program before after
  | restore {before homes} : CleanupWorldChange program before (restoreRoots before homes)
  | reservation {before cleared address authority id available} : before.availability.get id = some available →
      Permitted before authority .owned address → before.write address none = some cleared →
      CleanupWorldChange program before
        { cleared with availability := cleared.availability.set id { available with active := false } }

theorem LocalStep.cleanup_change {program : Kernel.Program} {before after : State} {event : Option Event}
    (step : LocalStep program before event after) (cleanup : before.task.Cleanup) :
    CleanupWorldChange program before.world after.world := by
  cases step <;> simp_all only [Task.Cleanup]
  case transfer moved => exact .transfer moved
  case cleanupDone => exact .unchanged
  case cleanupRoot => exact .unchanged
  case destroyVacant => exact .unchanged
  case destroyHook => apply CleanupWorldChange.hook <;> assumption
  case destroyStructural => exact .unchanged
  case destroyReference => apply CleanupWorldChange.clear <;> assumption
  case fieldsDone => exact .unchanged
  case fieldNext => exact .unchanged
  case shellDone permission relinquished written =>
    exact .relinquished permission relinquished written
  case retire retired => exact .retire retired
  case regionEnd closed => exact .region closed
  case loanEnd closed => exact .loan closed
  case loanAlreadyEnded => exact .unchanged
  case releaseReferenced => exact .unchanged
  case releaseResourceHeld => exact .unchanged
  case releaseBorrowed => exact .unchanged
  case releaseOwnedClaim => exact .unchanged
  case releaseStorageRetained => exact .unchanged
  case releaseRoot => apply CleanupWorldChange.loan; assumption
  case releaseChild => apply CleanupWorldChange.loan; assumption
  case releaseStorageReturned returned => exact .storageReturn returned
  case releaseAlreadyEnded => exact .unchanged

theorem Step.cleanup_change {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {event : Option Event} (step : Step program host before event after)
    (cleanup : before.task.Cleanup) : CleanupWorldChange program before.world after.world := by
  rcases step with localStep | atom | effect | control | primitive | foreign
  · exact localStep.cleanup_change cleanup
  · cases atom <;> simp_all only [Task.Cleanup]
  · cases effect <;> simp_all only [Task.Cleanup]
    case disposeContinuation => apply CleanupWorldChange.clear <;> assumption
    case cancel => exact .restore
  · cases control <;> simp_all only [Task.Cleanup]
    case destroyAvailable => apply CleanupWorldChange.reservation <;> assumption
    case destroySpentAvailable => apply CleanupWorldChange.clear <;> assumption
  · cases primitive <;> simp_all only [Task.Cleanup]
  · cases foreign <;> simp_all only [Task.Cleanup]

theorem CleanupWorldChange.worldTyped {program : Kernel.Program} {before after : World}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before) (changed : CleanupWorldChange program before after) :
    Typing.WorldTyped program after := by
  cases changed with
  | unchanged => exact typed
  | clear permission written => exact World.clear_worldTyped typed permission written
  | relinquished permission relinquished written =>
      exact World.clear_worldTyped (relinquished.worldTyped typed) (relinquished.permitted permission) written
  | transfer moved => exact moved.worldTyped valid inventory typed
  | hook allocated borrowed => exact borrowed.worldTyped valid inventory (allocated.worldTyped typed)
  | retire retired => exact retired.worldTyped typed
  | region closed => exact closed.worldTyped typed
  | loan closed => exact closed.worldTyped typed
  | storageReturn returned => exact returned.worldTyped typed
  | restore => exact restoreRoots.worldTyped typed
  | reservation found permission written =>
      have cleared := World.clear_worldTyped typed permission written
      have same := congrArg World.availability (World.write_rest written)
      exact World.deactivateAvailability_worldTyped cleared (by simpa only [same] using found)

/-- Every actual cleanup step preserves resident/storage typing, including
destructor handle creation and cancellation's reservation/loan/region teardown.
No safe post-state, ResourceAdmission, or cleanup-completion hypothesis is used. -/
theorem Step.cleanup_worldTyped {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world) (step : Step program host before event after)
    (cleanup : before.task.Cleanup) : Typing.WorldTyped program after.world :=
  (step.cleanup_change cleanup).worldTyped valid inventory typed

/-- A run segment consisting of cleanup transitions. This restricts the
existing Step relation; it does not replace it with a different evaluator.
Arbitrary destructor-body execution needs the full control-state theorem. -/
inductive CleanupRun (program : Kernel.Program) (host : Foreign.Model) : State → List Event → State → Prop where
  | refl {state} : CleanupRun program host state [] state
  | silent {before middle after trace} : before.task.Cleanup → Step program host before none middle →
      CleanupRun program host middle trace after → CleanupRun program host before trace after
  | visible {before middle after event trace} : before.task.Cleanup → Step program host before (some event) middle →
      CleanupRun program host middle trace after → CleanupRun program host before (event :: trace) after

theorem CleanupRun.run {program : Kernel.Program} {host : Foreign.Model} {before after : State} {trace : List Event}
    (cleanup : CleanupRun program host before trace after) : Run program host before trace after := by
  induction cleanup with
  | refl => exact .refl
  | silent _ step _ ih => exact .silent step ih
  | visible _ step _ ih => exact .visible step ih

theorem CleanupRun.worldTyped {program : Kernel.Program} {host : Foreign.Model} {before after : State} {trace : List Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world) (cleanup : CleanupRun program host before trace after) :
    Typing.WorldTyped program after.world := by
  induction cleanup with
  | refl => exact typed
  | silent task step _ ih | visible task step _ ih => exact ih (step.cleanup_worldTyped valid inventory typed task)

end Glorious.Language.Execution
