import GloriousLanguage.ReferencePersistence
import GloriousLanguage.ScopeClosing

/-! Invocation inputs keep their declared location types while later inputs
are bound. Owned formals get whole fresh roots; lent formals are guarded by
the actual child loan created by the common invocation lending relation. -/
namespace Glorious.Language

theorem FieldOffset.roots_congr {program : Program} {before after : World}
    (roots : after.roots = before.roots) {address : Address} {container type : Term} {index offset : Nat}
    (located : FieldOffset program before address container index type offset) :
    FieldOffset program after address container index type offset :=
  located.transport (by simp only [World.read,World.root,roots])

theorem AddressOffset.roots_congr {program : Program} {before after : World}
    (roots : after.roots = before.roots) {address : Address} {type : Term} {offset : Nat}
    (located : AddressOffset program before address type offset) :
    AddressOffset program after address type offset := by
  induction located with
  | root found live => exact .root (by simpa only [roots] using found) live
  | child _ field ih => exact .child ih (field.roots_congr roots)

theorem AddressType.roots_congr {program : Program} {before after : World}
    (roots : after.roots = before.roots) {address : Address} {type : Term}
    (located : AddressType program before address type) : AddressType program after address type := by
  obtain ⟨offset,located⟩ := located
  exact ⟨offset,located.roots_congr roots⟩

theorem Allocates.addressType {program : Program} {before after : World}
    {home region type layout mutable address originBound} (valid : before.WellFormedWithOrigins originBound)
    (allocated : Allocates program before home region type layout mutable address after)
    {observed : Address} {expected : Term} (located : AddressType program before observed expected) :
    AddressType program after observed expected := by
  obtain ⟨offset,located⟩ := located
  refine ⟨offset,?_⟩
  induction located with
  | root found live => exact .root (allocated.roots valid found) live
  | child _ field ih => exact .child ih (field.transport (by rw [allocated.read valid]))

theorem Address.not_properPrefix_of_nil {first second : Address} (empty : second.fields = []) :
    ¬ first.ProperPrefix second := by
  intro included
  have bound := included.2
  rw [empty] at bound
  exact Nat.not_lt_zero _ bound

/-- Provenance of a bound invocation location, not an access permission. Its
loan case retains the real resident reference handle produced at invocation;
the existing loan-release guard cannot end that loan while the handle lives. -/
def InvocationAddress (world : World) (address : Address) : Prop :=
  address.fields = [] ∨ ∃ id loan, world.loans.get id = some loan ∧ loan.live = true ∧
    loan.referent = address ∧ world.References id

theorem InvocationAddress.allocates {program : Program} {before after : World}
    {home region type layout mutable address} (valid : before.WellFormed)
    (allocated : Allocates program before home region type layout mutable address after)
    {observed : Address} (guarded : InvocationAddress before observed) : InvocationAddress after observed := by
  rcases guarded with whole | ⟨id,loan,found,live,referent,referenced⟩
  · exact Or.inl whole
  · have loans : after.loans = before.loans := by cases allocated; rfl
    exact Or.inr ⟨id,loan,by simpa only [loans] using found,live,referent,allocated.references valid referenced⟩

theorem InvocationAddress.transfers {program : Program} {before after : World}
    {authority source destination} (transferred : Transfers program before authority source destination after)
    {observed : Address} (guarded : InvocationAddress before observed) : InvocationAddress after observed := by
  rcases guarded with whole | ⟨id,loan,found,live,referent,referenced⟩
  · exact Or.inl whole
  · exact Or.inr ⟨id,loan,by simpa only [transferred.loans] using found,live,referent,transferred.references referenced⟩

theorem InvocationAddress.formsLoan {program : Program} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent destination} (valid : before.WellFormed)
    (borrowed : FormsLoan program purpose before authority mode region referent destination after)
    {observed : Address} (guarded : InvocationAddress before observed) : InvocationAddress after observed := by
  rcases guarded with whole | ⟨id,loan,found,live,referent,referenced⟩
  · exact Or.inl whole
  · exact Or.inr ⟨id,loan,borrowed.old_loan valid found,live,referent,borrowed.references referenced⟩

theorem InvocationAddress.endsLoan {before after : World} {ending : Identity}
    (ended : EndsLoan before ending after) {address : Address} (guarded : InvocationAddress before address) :
    InvocationAddress after address := by
  rcases guarded with whole | ⟨id,loan,found,live,referent,referenced⟩
  · exact Or.inl whole
  · cases ended with
    | restored _ _ _ absent _ =>
      have different : id ≠ ending := fun same => absent (same ▸ referenced)
      exact Or.inr ⟨id,loan,by rw [Table.get_set_other _ _ _ _ different]; exact found,
        live,referent,referenced.roots_congr rfl⟩

theorem Transfers.invocation_addressType {program : Program} {before after : World}
    {authority source destination} (valid : before.WellFormed)
    (transferred : Transfers program before authority source destination after)
    {address : Address} {type : Term} (guarded : InvocationAddress before address)
    (located : AddressType program before address type) : AddressType program after address type := by
  rcases guarded with whole | ⟨id,loan,found,live,rfl,_⟩
  · exact (transferred.address_types (Address.not_properPrefix_of_nil whole)
      (Address.not_properPrefix_of_nil whole)).mp located
  · exact (transferred.address_types
      (transferred.permission.owned_no_loan_descendant (World.loanParents valid) found live)
      (transferred.destination_vacant.no_located_descendant (World.liveLoanLocations valid _ _ found live))).mp located

theorem FormsLoan.invocation_addressType {program : Program} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent destination} (valid : before.WellFormed)
    (borrowed : FormsLoan program purpose before authority mode region referent destination after)
    {address : Address} {type : Term} (guarded : InvocationAddress before address)
    (located : AddressType program before address type) : AddressType program after address type := by
  cases borrowed with
  | @borrow _ middle _ _ _ _ _ _ _ vacant _ _ written =>
    refine AddressType.roots_congr (before := middle) ?_ ?_
    · rfl
    apply (World.write_address_types written ?_).mp located
    rcases guarded with whole | ⟨id,loan,found,live,rfl,_⟩
    · exact Address.not_properPrefix_of_nil whole
    · exact vacant.no_located_descendant (World.liveLoanLocations valid _ _ found live)

theorem FormsLoan.referent_addressType {program : Program} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent destination} (borrowed : FormsLoan program purpose before authority mode region referent destination after)
    {value : Value} (stored : before.Stores referent value) : AddressType program after referent value.type := by
  cases borrowed with
  | @borrow _ middle _ actual located _ _ _ _ vacant _ _ written =>
    have same := Option.some.inj (actual.symm.trans stored)
    subst same
    refine AddressType.roots_congr (before := middle) ?_ ?_
    · rfl
    exact (World.write_address_types written (vacant.no_located_descendant (Or.inl ⟨_,stored⟩))).mp located

theorem FormsLoan.invocationAddress {program : Program} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent destination} (borrowed : FormsLoan program purpose before authority mode region referent destination after) :
    InvocationAddress after referent := by
  have referenced := borrowed.created_reference
  cases borrowed
  exact Or.inr ⟨_,_,Table.get_set _ _ _,rfl,rfl,referenced⟩

theorem Kernel.LendsResident.preserves_inputType {program : Kernel.Program} {before after : World}
    {activation scope region address authority access lease permission}
    (_valid : ProgramWellFormed program.declarations) (_inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (lent : Kernel.LendsResident program.declarations activation scope region before address authority access lease permission after)
    {observed : Address} {type : Term} (guarded : InvocationAddress before observed)
    (located : AddressType program.declarations before observed type) :
    InvocationAddress after observed ∧ AddressType program.declarations after observed type := by
  cases lent with
  | owned => exact ⟨guarded,located⟩
  | lent _ _ allocated borrowed =>
    have middle := allocated.worldTyped typed
    exact ⟨(guarded.allocates typed.1 allocated).formsLoan middle.1 borrowed,
      borrowed.invocation_addressType middle.1 (guarded.allocates typed.1 allocated) (allocated.addressType typed.1 located)⟩

theorem Kernel.BindsInput.preserves_inputType {program : Kernel.Program} {before after : World}
    {activation scope region input binding}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (bound : Kernel.BindsInput program.declarations activation scope region before input binding after)
    {observed : Address} {type : Term} (guarded : InvocationAddress before observed)
    (located : AddressType program.declarations before observed type) :
    InvocationAddress after observed ∧ AddressType program.declarations after observed type := by
  cases bound with
  | lent _ _ _ _ _ lent => exact lent.preserves_inputType valid inventory typed guarded located
  | owned _ _ _ allocated transferred =>
    exact ⟨(guarded.allocates typed.1 allocated).transfers transferred,
      transferred.invocation_addressType (allocated.worldTyped typed).1
        (guarded.allocates typed.1 allocated) (allocated.addressType typed.1 located)⟩

theorem Kernel.BindsInputs.preserves_inputType {program : Kernel.Program} {before after : World}
    {activation scope region inputs bindings}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (bound : Kernel.BindsInputs program.declarations activation scope region before inputs bindings after)
    {observed : Address} {type : Term} (guarded : InvocationAddress before observed)
    (located : AddressType program.declarations before observed type) :
    InvocationAddress after observed ∧ AddressType program.declarations after observed type := by
  induction bound with
  | nil => exact ⟨guarded,located⟩
  | cons first _ ih =>
    obtain ⟨middle,atType⟩ := first.preserves_inputType valid inventory typed guarded located
    exact ih (first.worldTyped valid inventory typed) middle atType

theorem Kernel.BindsInput.inputType {program : Kernel.Program} {before after : World}
    {activation scope region input binding} (typed : Typing.WorldTyped program before)
    (bound : Kernel.BindsInput program.declarations activation scope region before input binding after) :
    binding.localSlot = input.formal.id ∧ InvocationAddress after binding.address ∧
      AddressType program.declarations after binding.address input.formal.type := by
  cases input
  cases bound with
  | lent notOwned stored _ typeEq _ lent =>
    cases lent with
    | owned => exact False.elim (notOwned rfl)
    | lent _ _ allocated borrowed =>
      refine ⟨rfl,borrowed.invocationAddress,?_⟩
      rw [← typeEq]
      apply borrowed.referent_addressType
      simpa only [World.Stores,allocated.read typed.1] using stored
  | owned _ _ _ allocated transferred =>
    have whole := allocated.fields_nil
    exact ⟨rfl,Or.inl whole,(transferred.address_types (Address.not_properPrefix_of_nil whole)
      (Address.not_properPrefix_of_nil whole)).mp allocated.created_addressType⟩

/-- Each actual final binding is aligned with its original input recipe, and
keeps its type after the entire sequence, not merely immediately after bind. -/
theorem Kernel.BindsInputs.inputTypes {program : Kernel.Program} {before after : World}
    {activation scope region inputs bindings}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (bound : Kernel.BindsInputs program.declarations activation scope region before inputs bindings after) :
    ListRel (fun input binding => binding.localSlot = input.formal.id ∧ InvocationAddress after binding.address ∧
      AddressType program.declarations after binding.address input.formal.type) inputs bindings := by
  induction bound with
  | nil => exact .nil
  | cons first rest ih =>
    have middle := first.worldTyped valid inventory typed
    obtain ⟨identity,guarded,located⟩ := first.inputType typed
    obtain ⟨guarded,located⟩ := rest.preserves_inputType valid inventory middle guarded located
    exact .cons ⟨identity,guarded,located⟩ (ih middle)

end Glorious.Language
