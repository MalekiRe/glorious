import GloriousLanguage.ReferencePersistence
import GloriousLanguage.ScopeClosing
import GloriousLanguage.BorrowPreservation

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

theorem InvocationAddress.transfers {program : RuntimeProgram} {before after : World}
    {authority source destination} (transferred : Transfers program before authority source destination after)
    {observed : Address} (guarded : InvocationAddress before observed) : InvocationAddress after observed := by
  rcases guarded with whole | ⟨id,loan,found,live,referent,referenced⟩
  · exact Or.inl whole
  · exact Or.inr ⟨id,loan,by simpa only [transferred.loans] using found,live,referent,transferred.references referenced⟩

theorem InvocationAddress.formsLoan {program : RuntimeProgram} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent destination} (valid : before.WellFormed)
    (borrowed : FormsLoan program purpose before authority mode region referent destination after)
    {observed : Address} (guarded : InvocationAddress before observed) : InvocationAddress after observed := by
  rcases guarded with whole | ⟨id,loan,found,live,referent,referenced⟩
  · exact Or.inl whole
  · exact Or.inr ⟨id,loan,borrowed.old_loan valid found,live,referent,borrowed.references referenced⟩

theorem InvocationAddress.endsLoan {program : RuntimeProgram} {before after : World} {ending : Identity}
    (ended : EndsLoan program before ending after) {address : Address} (guarded : InvocationAddress before address) :
    InvocationAddress after address := by
  rcases guarded with whole | ⟨id,loan,found,live,referent,referenced⟩
  · exact Or.inl whole
  · cases ended with
    | restored _ _ _ _ _ absent _ _ =>
      have different : id ≠ ending := fun same => absent (same ▸ referenced)
      exact Or.inr ⟨id,loan,by rw [Table.get_set_other _ _ _ _ different]; exact found,
        live,referent,referenced.roots_congr rfl⟩

theorem InvocationAddress.retained {before after : World}
    (roots : after.roots = before.roots)
    (retained : ∀ identity original, before.loans.get identity = some original →
      ∃ current, after.loans.get identity = some current ∧ current.permissionState = original.permissionState)
    {address : Address} (guarded : InvocationAddress before address) : InvocationAddress after address := by
  rcases guarded with whole | ⟨id,loan,found,live,referent,referenced⟩
  · exact Or.inl whole
  · obtain ⟨current,selected,same⟩ := retained id loan found
    obtain ⟨_,_,place,_,_,active,_,_⟩ := Loan.permissionState_eq_iff.mp same
    exact Or.inr ⟨id,current,selected,active.trans live,place.trans referent,referenced.roots_congr roots⟩

theorem Transfers.invocation_addressType {program : RuntimeProgram} {before after : World}
    {authority source destination} (valid : before.WellFormed)
    (transferred : Transfers program before authority source destination after)
    {address : Address} {type : Term} (guarded : InvocationAddress before address)
    (located : AddressType program.declarations before address type) : AddressType program.declarations after address type := by
  rcases guarded with whole | ⟨id,loan,found,live,rfl,_⟩
  · exact (transferred.address_types (Address.not_properPrefix_of_nil whole)
      (Address.not_properPrefix_of_nil whole)).mp located
  · exact (transferred.address_types
      (transferred.permission.owned_no_loan_descendant (World.loanParents valid) found live)
      (transferred.destination_vacant.no_located_descendant (World.liveLoanLocations valid _ _ found live))).mp located

theorem FormsLoan.invocation_addressType {program : RuntimeProgram} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent destination} (valid : before.WellFormed)
    (borrowed : FormsLoan program purpose before authority mode region referent destination after)
    {address : Address} {type : Term} (guarded : InvocationAddress before address)
    (located : AddressType program.declarations before address type) : AddressType program.declarations after address type := by
  cases borrowed with
  | @borrow _ middle _ _ _ _ _ _ _ _ vacant _ _ written =>
    have outside : ¬ destination.ProperPrefix address := by
      rcases guarded with whole | ⟨id,loan,found,live,rfl,_⟩
      · exact Address.not_properPrefix_of_nil whole
      · exact vacant.no_located_descendant (World.liveLoanLocations valid _ _ found live)
    refine AddressType.roots_congr (before := middle) ?_ ((World.write_address_types written outside).mp located)
    rfl

theorem FormsLoan.referent_addressType {program : RuntimeProgram} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent destination} (borrowed : FormsLoan program purpose before authority mode region referent destination after)
    {value : Value} (stored : before.Stores referent value) : AddressType program.declarations after referent value.type := by
  cases borrowed with
  | @borrow _ middle _ actual located _ _ _ _ _ vacant _ _ written =>
    have same := Option.some.inj (actual.symm.trans stored)
    subst same
    refine AddressType.roots_congr (before := middle) ?_
      ((World.write_address_types written (vacant.no_located_descendant (Or.inl ⟨_,stored⟩))).mp located)
    rfl

theorem FormsLoan.invocationAddress {program : RuntimeProgram} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent destination} (borrowed : FormsLoan program purpose before authority mode region referent destination after) :
    InvocationAddress after referent := by
  have referenced := borrowed.created_reference
  cases borrowed
  exact Or.inr ⟨_,_,Table.get_set _ _ _,rfl,rfl,referenced⟩

theorem Kernel.LendsResident.preserves_inputType {program : Kernel.Program} {before after : World}
    {activation scope region address authority access lease permission}
    (_valid : ProgramWellFormed program.declarations) (_inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (lent : Kernel.LendsResident program activation scope region before address authority access lease permission after)
    {observed : Address} {type : Term} (guarded : InvocationAddress before observed)
    (located : AddressType program.declarations before observed type) :
    InvocationAddress after observed ∧ AddressType program.declarations after observed type := by
  cases lent with
  | owned => exact ⟨guarded,located⟩
  | lent _ _ _ allocated borrowed =>
    have middle := allocated.worldTyped typed
    exact ⟨(guarded.allocates typed.1 allocated).formsLoan middle.1 borrowed,
      borrowed.invocation_addressType middle.1 (guarded.allocates typed.1 allocated) (allocated.addressType typed.1 located)⟩

theorem Kernel.BindsInputAt.preserves_inputType {recipient : ClaimCustody} {program : Kernel.Program} {before after : World}
    {activation scope region input binding}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (bound : Kernel.BindsInputAt program recipient activation scope region before input binding after)
    {observed : Address} {type : Term} (guarded : InvocationAddress before observed)
    (located : AddressType program.declarations before observed type) :
    InvocationAddress after observed ∧ AddressType program.declarations after observed type := by
  cases bound with
  | lent _ _ _ _ _ _ _ lent => exact lent.preserves_inputType valid inventory typed guarded located
  | owned _ _ _ _ _ allocated transferred =>
    exact ⟨(guarded.allocates typed.1 allocated).transfers transferred,
      transferred.invocation_addressType (allocated.worldTyped typed).1
        (guarded.allocates typed.1 allocated) (allocated.addressType typed.1 located)⟩
  | storage _ _ _ claimed =>
    have roots : after.roots = before.roots := by cases claimed; rfl
    exact ⟨guarded.retained roots (fun _ loan found => ⟨loan,claimed.old_loan typed.1 found,rfl⟩),
      located.roots_congr roots⟩
  | allocation _ _ _ _ transferred =>
    have roots : after.roots = before.roots := by cases transferred; rfl
    exact ⟨guarded.retained roots (fun _ _ found => transferred.retained found),located.roots_congr roots⟩
  | guardedAllocation _ _ _ _ _ claimed =>
    have roots : after.roots = before.roots := by cases claimed; rfl
    exact ⟨guarded.retained roots (fun _ loan found => ⟨loan,claimed.old_loan typed.1 found,rfl⟩),
      located.roots_congr roots⟩
  | loan _ _ _ _ transferred =>
    have roots : after.roots = before.roots := by cases transferred <;> rfl
    exact ⟨guarded.retained roots (fun _ _ found => transferred.retained found),located.roots_congr roots⟩

theorem Kernel.BindsInputsFor.preserves_inputType {recipient : ClaimCustody} {footprint : List Address} {program : Kernel.Program} {before after : World}
    {activation scope region inputs bindings}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (bound : Kernel.BindsInputsFor program recipient activation scope region footprint before inputs bindings after)
    {observed : Address} {type : Term} (guarded : InvocationAddress before observed)
    (located : AddressType program.declarations before observed type) :
    InvocationAddress after observed ∧ AddressType program.declarations after observed type := by
  induction bound using Kernel.BindsInputsFor.inductionOn with
  | nil => exact ⟨guarded,located⟩
  | cons _ first _ ih =>
    obtain ⟨middle,atType⟩ := first.preserves_inputType valid inventory typed guarded located
    exact ih (first.worldTyped valid inventory typed) middle atType

theorem Kernel.BindsInputAt.inputType {recipient : ClaimCustody} {program : Kernel.Program} {before after : World}
    {activation scope region input binding} (typed : Typing.WorldTyped program before)
    (bound : Kernel.BindsInputAt program recipient activation scope region before input binding after)
    (resident : input.formal.IsResident) :
    binding.key = input.formal.key ∧ InvocationAddress after binding.address ∧
      AddressType program.declarations after binding.address input.formal.type := by
  refine ⟨bound.binding_key,?_⟩
  cases bound with
  | lent _ notOwned _ stored _ typeEq _ lent =>
    generalize accessEq : input.access = access at lent notOwned
    cases lent with
    | owned => exact False.elim (notOwned rfl)
    | lent _ _ _ allocated borrowed =>
      refine ⟨borrowed.invocationAddress,?_⟩
      rw [← typeEq]
      apply borrowed.referent_addressType
      simpa only [World.Stores,allocated.read typed.1] using stored
  | owned _ _ _ _ _ allocated transferred =>
    have whole := allocated.fields_nil
    exact ⟨Or.inl whole,(transferred.address_types (Address.not_properPrefix_of_nil whole)
      (Address.not_properPrefix_of_nil whole)).mp allocated.created_addressType⟩
  | storage _ formal _ _ => simp [formal,Kernel.InputFormal.IsResident] at resident
  | allocation _ formal _ _ _ => simp [formal,Kernel.InputFormal.IsResident] at resident
  | guardedAllocation _ formal _ _ _ _ => simp [formal,Kernel.InputFormal.IsResident] at resident
  | loan _ formal _ _ _ => simp [formal,Kernel.InputFormal.IsResident] at resident

/-- Each actual final binding is aligned with its original input recipe, and
keeps its type after the entire sequence, not merely immediately after bind. -/
theorem Kernel.BindsInputsFor.inputTypes {recipient : ClaimCustody} {footprint : List Address} {program : Kernel.Program} {before after : World}
    {activation scope region inputs bindings}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (bound : Kernel.BindsInputsFor program recipient activation scope region footprint before inputs bindings after) :
    ListRel (fun input binding => binding.key = input.formal.key ∧
      (input.formal.IsResident → InvocationAddress after binding.address ∧
        AddressType program.declarations after binding.address input.formal.type)) inputs bindings := by
  induction bound using Kernel.BindsInputsFor.inductionOn with
  | nil => exact .nil
  | cons _ first rest ih =>
    have middle := first.worldTyped valid inventory typed
    refine .cons ⟨first.binding_key,?_⟩ (ih middle)
    intro resident
    obtain ⟨_,guarded,located⟩ := first.inputType typed resident
    exact rest.preserves_inputType valid inventory middle guarded located

end Glorious.Language
