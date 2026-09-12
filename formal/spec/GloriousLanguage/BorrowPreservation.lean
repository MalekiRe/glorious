import GloriousLanguage.BorrowConstructionPreservation

/-! Every ordinary resident and erased raw-resource input consumes its actual
binding constructor. Custody handoff and fresh storage claims preserve the
same world typing boundary as resident movement and invocation lending. -/
namespace Glorious.Language

theorem Kernel.LendsResident.worldTyped {program : Kernel.Program} {before after : World}
    {activation scope region address authority access lease permission}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (lent : Kernel.LendsResident program activation scope region before address authority access lease permission after) :
    Typing.WorldTyped program after := by
  cases lent with
  | owned => exact typed
  | lent _ _ _ allocated borrowed => exact borrowed.worldTyped valid inventory (allocated.worldTyped typed)

theorem Kernel.BindsInputAt.worldTyped {recipient : ClaimCustody} {program : Kernel.Program} {before after : World}
    {activation scope region input binding}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (bound : Kernel.BindsInputAt program recipient activation scope region before input binding after) :
    Typing.WorldTyped program after := by
  cases bound with
  | lent _ _ _ _ _ _ _ lent => exact lent.worldTyped valid inventory typed
  | owned _ _ _ _ _ allocated transferred => exact transferred.worldTyped valid inventory (allocated.worldTyped typed)
  | storage _ _ _ claimed => exact claimed.worldTyped typed
  | allocation _ _ _ _ transferred => exact transferred.worldTyped typed
  | guardedAllocation _ _ _ _ _ claimed => exact claimed.worldTyped typed
  | loan _ _ _ _ transferred => exact transferred.worldTyped typed

theorem Kernel.BindsPattern.worldTyped {program : Kernel.Program} {before after : World}
    {activation scope region localSlot source authority access binding}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (bound : Kernel.BindsPattern program activation scope region before localSlot source authority access binding after) :
    Typing.WorldTyped program after := by
  cases bound with
  | owned bound => exact bound.worldTyped valid inventory typed
  | borrowed _ _ allocated borrowed => exact borrowed.worldTyped valid inventory (allocated.worldTyped typed)

theorem Kernel.BindsInputsAttemptFor.worldTyped {recipient : ClaimCustody} {footprint : List Address}
    {program : Kernel.Program} {before after : World} {activation scope region inputs bindings}
    {outcome : Kernel.PreparationOutcome}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (bound : Kernel.BindsInputsAttemptFor program recipient activation scope region footprint before inputs bindings after outcome) :
    Typing.WorldTyped program after := by
  induction bound with
  | nil => exact typed
  | cons _ first _ ih => exact ih (first.worldTyped valid inventory typed)
  | exhausted => exact typed

theorem Kernel.BindsInputsFor.worldTyped {recipient : ClaimCustody} {footprint : List Address}
    {program : Kernel.Program} {before after : World} {activation scope region inputs bindings}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (bound : Kernel.BindsInputsFor program recipient activation scope region footprint before inputs bindings after) :
    Typing.WorldTyped program after :=
  Kernel.BindsInputsAttemptFor.worldTyped valid inventory typed bound

end Glorious.Language
