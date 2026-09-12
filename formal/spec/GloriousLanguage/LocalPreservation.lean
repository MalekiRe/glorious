import GloriousLanguage.LifecyclePreservation
import GloriousLanguage.RehomePreservation
import GloriousLanguage.ReceiverPreservation

/-! General storage typing preservation for ordinary local machine execution.
Scope entry, invocation binding and receiver/shell consumption use the same
storage relations as cleanup, without a typed post-state admission premise. -/
namespace Glorious.Language


namespace Execution

theorem Protect.worldTyped {program : Kernel.Program} {context : Context} {before after : World}
    {source destination : Address} {authority : Authority}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (kept : Protect program context before source authority destination after) :
    Typing.WorldTyped program after := by
  obtain ⟨_,_,_,allocated,moved⟩ := kept
  exact moved.worldTyped valid inventory (allocated.worldTyped typed)

theorem ProtectsAttemptFor.worldTyped {footprint : List Address} {program : Kernel.Program} {context : Context} {before after : World}
    {sources : List ResolvedPlace} {destinations : List Address}
    {outcome : Kernel.PreparationOutcome}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (kept : ProtectsAttemptFor program context footprint before sources destinations after outcome) :
    Typing.WorldTyped program after := by
  induction kept with
  | nil => exact typed
  | cons _ first _ ih => exact ih (first.worldTyped valid inventory typed)
  | exhausted => exact typed

theorem ProtectsFor.worldTyped {footprint : List Address} {program : Kernel.Program} {context : Context} {before after : World}
    {sources : List ResolvedPlace} {destinations : List Address}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (kept : ProtectsFor program context footprint before sources destinations after) :
    Typing.WorldTyped program after :=
  ProtectsAttemptFor.worldTyped valid inventory typed kept

theorem PreparesEntry.worldTyped {program : Kernel.Program} {callee : Context} {function : Kernel.Function}
    {before after : World} {source : EntrySource} {inputs : List Kernel.InvocationInput}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (prepared : PreparesEntry program callee function before source inputs after) :
    Typing.WorldTyped program after := by
  cases prepared with
  | supplied => exact typed
  | resident _ _ lent _ consumed =>
      exact consumed.worldTyped (lent.worldTyped valid inventory typed)
  | contextual _ _ _ _ receiver witness _ consumed availability =>
      exact availability.worldTyped (consumed.worldTyped
        (witness.worldTyped valid inventory (receiver.worldTyped valid inventory typed)))

theorem EnterWorldAttempt.worldTyped {program : Kernel.Program} {before : State} {after : World}
    {caller context : Context} {function : Kernel.Function} {source : EntrySource}
    {outcome : Kernel.PreparationOutcome}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (entered : EnterWorldAttempt program before caller function source context after outcome) :
    Typing.WorldTyped program after := by
  obtain ⟨_,_,_,_,_,_,_,fresh,prepared,_,bound,finished,_,_⟩ := entered
  have boundTyped := bound.worldTyped valid inventory (prepared.worldTyped valid inventory (fresh.worldTyped typed))
  cases outcome with
  | complete => exact finished.worldTyped boundTyped
  | exhausted => exact finished ▸ boundTyped

theorem EnterWorld.worldTyped {program : Kernel.Program} {before : State} {after : World}
    {caller context : Context} {function : Kernel.Function} {source : EntrySource}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (entered : EnterWorld program before caller function source context after) :
    Typing.WorldTyped program after :=
  EnterWorldAttempt.worldTyped valid inventory typed entered

theorem ReturnsResources.worldTyped {program : Kernel.Program} {before after : World}
    {source receiver returned : Context} {result : Address}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (returnedResources : ReturnsResources program source receiver before result returned after) :
    Typing.WorldTyped program after := by
  cases returnedResources with
  | localReturn => exact typed
  | invocationReturn _ _ _ bound relinquished =>
      exact relinquished.worldTyped (bound.worldTyped valid inventory typed)

/-- Every ordinary local transition preserves the world typing invariant.
This includes owned receiver consumption, fresh scope and invocation entry,
pattern binding/deconstruction and destructor handle creation. It is a storage
preservation theorem, not yet a task/frame preservation or progress theorem. -/
theorem LocalStep.worldTyped {program : Kernel.Program} {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world) (step : LocalStep program before event after) :
    Typing.WorldTyped program after.world := by
  cases step <;> try exact typed
  case evaluate allocated => exact allocated.worldTyped typed
  case bind allocated => exact allocated.worldTyped typed
  case result kept => exact kept.worldTyped valid inventory typed
  case transfer moved => exact moved.worldTyped valid inventory typed
  case invoke allocated => exact allocated.worldTyped typed
  case enterExhausted entered => exact entered.worldTyped valid inventory typed
  case enter entered => exact entered.worldTyped valid inventory typed
  case enterTail _ entered relinquished _ _ _ _ =>
    exact relinquished.worldTyped (entered.worldTyped valid inventory typed)
  case bindReturn _ _ moved returned =>
    exact returned.worldTyped valid inventory (moved.worldTyped valid inventory typed)
  case activationReturn _ _ _ kept returned _ _ =>
    exact returned.worldTyped valid inventory (kept.worldTyped valid inventory typed)
  case scope => apply FreshRegion.worldTyped typed; assumption
  case scopeReturn _ _ kept returned _ _ =>
    exact returned.worldTyped valid inventory (kept.worldTyped valid inventory typed)
  case labelReturn _ _ returned => exact returned.worldTyped valid inventory typed
  case patternBind bound => exact bound.worldTyped valid inventory typed
  case patternShell consumed => exact consumed.worldTyped typed
  case destroyHook => apply FormsLoan.worldTyped valid inventory (program := program); apply Temporary.worldTyped typed <;> assumption; assumption
  case destroyReference => apply World.clear_worldTyped typed <;> assumption
  case shellDone permission relinquished written =>
    exact World.clear_worldTyped (relinquished.worldTyped typed) (relinquished.permitted permission) written
  case retire retired => exact retired.worldTyped typed
  case regionEnd ended => exact ended.worldTyped typed
  case loanEnd ended => exact ended.worldTyped typed
  case releaseRoot ended => exact ended.worldTyped typed
  case releaseChild ended => exact ended.worldTyped typed
  case releaseStorageReturned returned => exact returned.worldTyped typed

end Execution

end Glorious.Language
