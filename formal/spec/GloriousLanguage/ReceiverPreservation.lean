import GloriousLanguage.BorrowPreservation

/-! The common receiver loan boundary. Every lent invocation obtains child
loan authority; returning consumes the handle before restoring its parent. -/
namespace Glorious.Language.Execution

theorem LendsReceiver.worldTyped {program : Kernel.Program} {leaseContext : Context}
    {before after : World} {receiver : Address} {authority permission : Authority}
    {access : Access} {lease : Option ReceiverLease}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (lent : LendsReceiver program leaseContext before receiver authority access lease permission after) :
    Typing.WorldTyped program after := by
  cases lent with
  | owned => exact typed
  | lent _ _ allocated borrowed => exact borrowed.worldTyped valid inventory (allocated.worldTyped typed)

theorem EndsReceiverLease.worldTyped {program : Kernel.Program} {before after : World} {lease : Option ReceiverLease}
    (typed : Typing.WorldTyped program before) (ended : EndsReceiverLease before lease after) :
    Typing.WorldTyped program after := by
  cases ended with
  | none => exact typed
  | some _ _ permitted written closed retired =>
    exact retired.worldTyped (closed.worldTyped (World.clear_worldTyped typed permitted written))

/-- Fresh child loan order rules out renewing conflicting access through the
original authority while the invocation lease remains active. -/
theorem Borrows.excludes_parent {program : Language.Program} {before after : World}
    {authority : Authority} {mode : Mutability} {region : Identity} {receiver handle : Address} {access : Access}
    (valid : before.WellFormed) (borrowed : Borrows program before authority mode region receiver handle after)
    (conflict : Conflict access mode) : ¬ Permitted after authority access receiver := by
  have parents := borrowed.loanParents valid
  cases borrowed with
  | @borrow value middle parent _ _ _ _ _ permitted _ _ _ _ =>
    intro allowed
    have found : (before.loans.set before.nextLoan
        ⟨before.nextLoan,parent,receiver,mode,region,true⟩).get before.nextLoan =
        some ⟨before.nextLoan,parent,receiver,mode,region,true⟩ := Table.get_set _ _ _
    obtain ⟨ancestor,selected,ancestry⟩ := allowed.conflicting_parent found rfl
      (Address.Prefix.refl receiver).overlaps conflict
    obtain ⟨old,oldFound,_⟩ := permitted.parentLoan selected
    exact Nat.not_lt_of_ge (ancestry.identity_le parents) (World.loanBounds valid oldFound)

theorem LendsReceiver.unique_exclusive {program : Kernel.Program} {leaseContext : Context}
    {before after : World} {receiver : Address} {authority permission : Authority}
    {lease : Option ReceiverLease} {access : Access}
    (valid : before.WellFormed)
    (lent : LendsReceiver program leaseContext before receiver authority .unique lease permission after) :
    ¬ Permitted after authority access receiver := by
  cases lent with
  | lent modes _ allocated borrowed =>
    rcases modes with ⟨impossible,_⟩ | ⟨_,rfl⟩
    · cases impossible
    obtain ⟨_,allocated⟩ := allocated
    exact Borrows.excludes_parent (allocated.wellFormed valid) borrowed (Or.inr rfl)

theorem LendsReceiver.shared_no_mutation {program : Kernel.Program} {leaseContext : Context}
    {before after : World} {receiver : Address} {authority permission : Authority}
    {lease : Option ReceiverLease} {access : Access}
    (valid : before.WellFormed) (writes : access ≠ .shared)
    (lent : LendsReceiver program leaseContext before receiver authority .shared lease permission after) :
    ¬ Permitted after authority access receiver := by
  cases lent with
  | lent modes _ allocated borrowed =>
    rcases modes with ⟨_,rfl⟩ | ⟨impossible,_⟩
    · obtain ⟨_,allocated⟩ := allocated
      exact Borrows.excludes_parent (allocated.wellFormed valid) borrowed (Or.inl writes)
    · cases impossible

end Glorious.Language.Execution
