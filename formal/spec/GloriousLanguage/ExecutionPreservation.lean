import GloriousLanguage.EffectPreservation
import GloriousLanguage.TestPreservation
import GloriousLanguage.ForeignPreservation

/-! Preservation for the sole executable transition relation, with every
local, atomic, effect, control, primitive and foreign branch included. -/
namespace Glorious.Language.Execution

theorem CopiesSnapshot.hostState {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation}
    (copied : CopiesSnapshot program before suspension map after) : after.hostState = before.hostState := by
  rw [copied.result]

/-- The host supplies its actual protocol and mutation laws, not an assumed
typed output world. No transition-family exception is needed. -/
theorem Step.worldTyped {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (step : Step program host before event after) : Typing.WorldTyped program after.world := by
  rcases step with localStep | atom | effect | control | primitive | foreign
  · exact localStep.worldTyped valid inventory typed
  · exact atom.worldTyped valid inventory typed
  · exact effect.worldTyped valid inventory typed
  · exact control.worldTyped valid inventory typed
  · exact primitive.worldTyped valid inventory typed
  · exact foreign.worldTyped valid inventory lawful typed

/-- Every finite execution prefix retains the full storage invariant,
including prefixes containing replay and host callback re-entry. -/
theorem Run.worldTyped {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (run : Run program host before trace after) : Typing.WorldTyped program after.world := by
  induction run with
  | refl => exact typed
  | silent step _ ih => exact ih (step.worldTyped valid inventory lawful typed)
  | visible step _ ih => exact ih (step.worldTyped valid inventory lawful typed)

end Glorious.Language.Execution
