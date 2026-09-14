import GloriousLanguage.BorrowPreservation
import GloriousLanguage.ResidentMutationPreservation
import GloriousLanguage.InputLending

/-! The common receiver loan boundary. Every lent invocation obtains child
loan authority; returning consumes the handle before restoring its parent. -/
namespace Glorious.Language.Execution

theorem LendsReceiver.worldTyped {program : Kernel.Program} {leaseContext : Context}
    {before after : World} {receiver : Address} {authority permission : Authority}
    {access : Access} {lease : Option ReceiverLease}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (lent : LendsReceiver program leaseContext before receiver authority access lease permission after) :
    Typing.WorldTyped program after :=
  Kernel.LendsResident.worldTyped valid inventory typed lent

/-- Fresh child loan order rules out renewing conflicting access through the
original authority while the invocation lease remains active. -/
theorem _root_.Glorious.Language.FormsLoan.excludes_parent {purpose : LoanPurpose} {program : RuntimeProgram} {before after : World}
    {authority : Authority} {mode : Mutability} {region : Identity} {receiver handle : Address} {access : Access}
    (valid : before.WellFormed) (borrowed : FormsLoan program purpose before authority mode region receiver handle after)
    (conflict : Conflict access mode) : ¬ Permitted after authority access receiver := by
  have parents := borrowed.loanParents valid
  cases borrowed with
  | @borrow value middle parent _ _ _ _ _ _ permitted _ _ _ _ =>
    intro allowed
    have found : (before.loans.set before.nextLoan
        ⟨before.nextLoan,parent,receiver,mode,region,true,purpose.kind,authority.guardLoans before,false,none⟩).get before.nextLoan =
        some ⟨before.nextLoan,parent,receiver,mode,region,true,purpose.kind,authority.guardLoans before,false,none⟩ := Table.get_set _ _ _
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
  | lent modes _ _ allocated borrowed =>
    rcases modes with ⟨impossible,_⟩ | ⟨_,rfl⟩
    · cases impossible
    exact FormsLoan.excludes_parent (allocated.wellFormed valid) borrowed (Or.inr rfl)

theorem LendsReceiver.shared_no_mutation {program : Kernel.Program} {leaseContext : Context}
    {before after : World} {receiver : Address} {authority permission : Authority}
    {lease : Option ReceiverLease} {access : Access}
    (valid : before.WellFormed) (writes : access ≠ .shared)
    (lent : LendsReceiver program leaseContext before receiver authority .shared lease permission after) :
    ¬ Permitted after authority access receiver := by
  cases lent with
  | lent modes _ _ allocated borrowed =>
    rcases modes with ⟨_,rfl⟩ | ⟨impossible,_⟩
    · exact FormsLoan.excludes_parent (allocated.wellFormed valid) borrowed (Or.inl writes)
    · cases impossible

theorem ConsumesReceiver.worldTyped {program : Kernel.Program} {before after : World}
    {address : Address} {authority : Authority} {access : Access}
    (typed : Typing.WorldTyped program before) (consumed : ConsumesReceiver before address authority access after) :
    Typing.WorldTyped program after := by
  cases consumed with
  | lent => exact typed
  | owned stored _ _ permission written => exact World.write_shell_worldTyped typed stored permission written

/-- Consumption authenticates the exact prepared witness in its current
world. No external permission callback or typed output premise is needed. -/
theorem ConsumesAvailability.worldTyped {program : Kernel.Program} {before after : World}
    {address : Address} {authority : Authority} {id : Identity} {access : Access}
    (typed : Typing.WorldTyped program before)
    (consumed : ConsumesAvailability before address authority id access after) : Typing.WorldTyped program after := by
  cases consumed with
  | lent => exact typed
  | owned _ _ _ found _ permission written =>
      apply World.deactivateAvailability_worldTyped (World.clear_worldTyped typed permission written)
      simpa only [congrArg World.availability (World.write_rest written)] using found

theorem FinishesReceiver.worldTyped {program : Kernel.Program} {before after : World}
    {receiver : ResolvedPlace} {access : Access} (typed : Typing.WorldTyped program before)
    (finished : FinishesReceiver before receiver access after) : Typing.WorldTyped program after := by
  cases finished with
  | lent => exact typed
  | owned _ _ _ _ _ permission written => exact World.clear_worldTyped typed permission written

theorem FinishesEntry.worldTyped {program : Kernel.Program} {before after : World}
    {source : EntrySource} (typed : Typing.WorldTyped program before)
    (finished : FinishesEntry before source after) : Typing.WorldTyped program after := by
  cases finished with
  | supplied => exact typed
  | resident finished | contextual finished => exact finished.worldTyped typed

theorem ConsumesReceiver.wellFormed {before after : World} {address : Address} {authority : Authority}
    {access : Access} (consumed : ConsumesReceiver before address authority access after)
    (well : before.WellFormed) : after.WellFormed := by
  cases consumed with
  | lent => exact well
  | owned stored live callable permitted written =>
    exact World.write_wellFormed_of_origin well permitted written
      (fun _ _ found => World.write_shell_origin stored written found)

theorem ConsumesAvailability.wellFormed {before after : World} {address : Address}
    {authority : Authority} {id : Identity} {access : Access}
    (consumed : ConsumesAvailability before address authority id access after)
    (well : before.WellFormed) : after.WellFormed := by
  cases consumed with
  | lent => exact well
  | owned stored initialized head available active permitted written =>
    exact World.deactivateAvailability_wellFormed
      (World.clear_wellFormed (valid := well) (permission := permitted) (written := written))
      (by simpa only [congrArg World.availability (World.write_rest written)] using available)


theorem ConsumesReceiver.locations {before after : World} {address authority access}
    (consumed : ConsumesReceiver before address authority access after) :
    ∀ id, (after.roots.get id).map Root.location = (before.roots.get id).map Root.location := by
  cases consumed with
  | lent => intro; rfl
  | owned _ _ _ _ written => exact World.write_locations written

theorem ConsumesReceiver.loans {before after : World} {address authority access}
    (consumed : ConsumesReceiver before address authority access after) : after.loans = before.loans := by
  cases consumed with
  | lent => rfl
  | owned _ _ _ _ written => exact World.write_loans written

theorem ConsumesReceiver.read {before after : World} {receiver observed : Address}
    {authority : Authority} {access : Access} (consumed : ConsumesReceiver before receiver authority access after)
    (outside : access = .owned → ¬ observed.Prefix receiver) : after.read observed = before.read observed := by
  cases consumed with
  | lent => rfl
  | owned stored _ _ _ written => exact World.write_shell_read stored written (outside rfl)

theorem ConsumesReceiver.located {before after : World} {receiver observed : Address}
    {authority : Authority} {access : Access} (consumed : ConsumesReceiver before receiver authority access after)
    (located : before.Located observed) : after.Located observed := by
  cases consumed with
  | lent => exact located
  | owned stored _ _ _ written => exact World.write_shell_located stored written located

theorem ConsumesReceiver.addressType {program : Program} {before after : World} {receiver observed : Address}
    {authority : Authority} {access : Access} {type : Term}
    (consumed : ConsumesReceiver before receiver authority access after)
    (typed : AddressType program before observed type) : AddressType program after observed type := by
  cases consumed with
  | lent => exact typed
  | owned stored _ _ _ written => exact (World.write_shell_address_types stored written).mp typed


theorem ConsumesReceiver.stores_head {before after : World} {address : Address} {authority : Authority} {access : Access}
    (consumed : ConsumesReceiver before address authority access after)
    {observed : Address} {value : Value} (stored : before.Stores observed value) :
    ∃ changed, after.Stores observed changed ∧ changed.head = value.head := by
  cases consumed with
  | lent => exact ⟨value,stored,rfl⟩
  | owned found _ _ _ written => exact World.write_shell_stores_head found written stored

theorem ConsumesReceiver.references {before after : World} {address : Address}
    {authority : Authority} {access : Access} (consumed : ConsumesReceiver before address authority access after)
    {id : Identity} (referenced : before.References id) : after.References id := by
  cases consumed with
  | lent => exact referenced
  | owned stored _ _ _ written => exact World.write_shell_references stored written referenced

theorem ConsumesAvailability.locations {before after : World} {address : Address}
    {authority : Authority} {id : Identity} {access : Access}
    (consumed : ConsumesAvailability before address authority id access after) :
    ∀ key, (after.roots.get key).map Root.location = (before.roots.get key).map Root.location := by
  cases consumed with
  | lent => intro; rfl
  | owned _ _ _ _ _ _ written =>
    have same := World.write_locations written
    exact same

theorem ConsumesAvailability.loans {before after : World} {address : Address}
    {authority : Authority} {id : Identity} {access : Access}
    (consumed : ConsumesAvailability before address authority id access after) : after.loans = before.loans := by
  cases consumed with
  | lent => rfl
  | owned _ _ _ _ _ _ written =>
    have same := World.write_loans written
    exact same

theorem ConsumesAvailability.references {program : Kernel.Program} {before after : World} {address : Address}
    {authority : Authority} {key : Identity} {access : Access}
    (typed : Typing.WorldTyped program before)
    (consumed : ConsumesAvailability before address authority key access after)
    {id : Identity} (referenced : before.References id) : after.References id := by
  cases consumed with
  | lent => exact referenced
  | owned stored _ head _ _ _ written =>
    have fields := (World.stores_typed typed.roots stored).available_fields head
    exact (World.write_nonreference_leaf_references stored fields
      (by intro key; rw [head]; exact ValueHead.noConfusion) written referenced).roots_congr rfl

theorem FinishesReceiver.locations {before after : World} {receiver : ResolvedPlace} {access : Access}
    (finished : FinishesReceiver before receiver access after) :
    ∀ key, (after.roots.get key).map Root.location = (before.roots.get key).map Root.location := by
  cases finished with
  | lent => intro; rfl
  | owned _ _ _ _ _ _ written => exact World.write_locations written

theorem FinishesReceiver.loans {before after : World} {receiver : ResolvedPlace} {access : Access}
    (finished : FinishesReceiver before receiver access after) : after.loans = before.loans := by
  cases finished with
  | lent => rfl
  | owned _ _ _ _ _ _ written => exact World.write_loans written

theorem FinishesReceiver.references {before after : World} {receiver : ResolvedPlace} {access : Access}
    (finished : FinishesReceiver before receiver access after)
    {id : Identity} (referenced : before.References id) : after.References id := by
  cases finished with
  | lent => exact referenced
  | owned stored _ head fields _ _ written =>
    obtain ⟨identity,arguments,head⟩ := head
    exact World.write_nonreference_shell_references stored fields
      (by intro key; rw [head]; exact ValueHead.noConfusion) written referenced

theorem FinishesEntry.locations {before after : World} {source : EntrySource}
    (finished : FinishesEntry before source after) :
    ∀ key, (after.roots.get key).map Root.location = (before.roots.get key).map Root.location := by
  cases finished with
  | supplied => intro; rfl
  | resident finished | contextual finished => exact finished.locations

theorem FinishesEntry.loans {before after : World} {source : EntrySource}
    (finished : FinishesEntry before source after) : after.loans = before.loans := by
  cases finished with
  | supplied => rfl
  | resident finished | contextual finished => exact finished.loans

theorem FinishesEntry.references {before after : World} {source : EntrySource}
    (finished : FinishesEntry before source after)
    {id : Identity} (referenced : before.References id) : after.References id := by
  cases finished with
  | supplied => exact referenced
  | resident finished | contextual finished => exact finished.references referenced

theorem PreparesEntryAttempt.wellFormed {program : Kernel.Program} {callee : Context} {function : Kernel.Function}
    {before after : World} {source : EntrySource} {inputs : List Kernel.InvocationInput} {outcome : Kernel.PreparationOutcome}
    (prepared : PreparesEntryAttempt program callee function before source inputs after outcome)
    (well : before.WellFormed) : after.WellFormed := by
  cases prepared with
  | supplied => exact well
  | resident _ _ lends _ consumes =>
    exact ConsumesReceiver.wellFormed consumes (Kernel.LendsResident.wellFormed lends well)
  | contextual _ _ _ _ receiverLends witnessLends _ consumes consumesAvailability =>
    exact ConsumesAvailability.wellFormed consumesAvailability
      (ConsumesReceiver.wellFormed consumes
        (Kernel.LendsResident.wellFormed witnessLends (Kernel.LendsResident.wellFormed receiverLends well)))
  | residentExhausted | contextualReceiverExhausted => exact well
  | contextualWitnessExhausted _ _ _ _ lends _ => exact lends.wellFormed well


theorem ConsumesReceiver.nextRoot {before after : World} {address : Address} {authority : Authority} {access : Access}
    (consumed : ConsumesReceiver before address authority access after) : after.nextRoot = before.nextRoot := by
  cases consumed with
  | lent => rfl
  | owned _ _ _ _ written =>
      have same := congrArg World.nextRoot (World.write_rest written)
      exact same

theorem ConsumesAvailability.nextRoot {before after : World} {address : Address} {authority : Authority}
    {identity : Identity} {access : Access}
    (consumed : ConsumesAvailability before address authority identity access after) : after.nextRoot = before.nextRoot := by
  cases consumed with
  | lent => rfl
  | owned _ _ _ _ _ _ written =>
      have same := congrArg World.nextRoot (World.write_rest written)
      exact same

theorem PreparesEntryAttempt.nextRoot_le {program : Kernel.Program} {callee : Context} {function : Kernel.Function}
    {before after : World} {source : EntrySource} {inputs : List Kernel.InvocationInput} {outcome : Kernel.PreparationOutcome}
    (prepared : PreparesEntryAttempt program callee function before source inputs after outcome) :
    before.nextRoot ≤ after.nextRoot := by
  cases prepared with
  | supplied | residentExhausted | contextualReceiverExhausted => exact Nat.le_refl _
  | resident _ _ lends _ consumes => simpa only [consumes.nextRoot] using Kernel.LendsResident.nextRoot_le lends
  | contextual _ _ _ _ receiverLends witnessLends _ consumes consumesAvailability =>
      simpa only [consumesAvailability.nextRoot,consumes.nextRoot] using
        Nat.le_trans (Kernel.LendsResident.nextRoot_le receiverLends) (Kernel.LendsResident.nextRoot_le witnessLends)
  | contextualWitnessExhausted _ _ _ _ lends _ => exact lends.nextRoot_le

theorem ConsumesReceiver.read_shell {before after : World} {receiver observed : Address}
    {authority : Authority} {access : Access} (consumed : ConsumesReceiver before receiver authority access after)
    (outside : access = .owned → ¬ receiver.Prefix observed) :
    (after.read observed).map Value.shell = (before.read observed).map Value.shell := by
  cases consumed with
  | lent => rfl
  | owned _ _ _ _ written => exact World.write_read_shell written (outside rfl)

theorem ConsumesAvailability.read_shell {before after : World} {address observed : Address} {authority : Authority}
    {identity : Identity} {access : Access} (consumed : ConsumesAvailability before address authority identity access after)
    (outside : access = .owned → ¬ address.Prefix observed) :
    (after.read observed).map Value.shell = (before.read observed).map Value.shell := by
  cases consumed with
  | lent => rfl
  | owned _ _ _ _ _ _ written =>
      have framed := World.write_read_shell written (outside rfl)
      exact framed

theorem ConsumesAvailability.owned_cleared {before after : World} {address : Address} {authority : Authority}
    {identity : Identity} (consumed : ConsumesAvailability before address authority identity .owned after) :
    after.read address = none := by
  cases consumed with
  | lent different => exact False.elim (different rfl)
  | owned _ _ _ _ _ _ written =>
      have erased := World.write_read_inside written []
      simpa [World.read,World.root] using erased

theorem FinishesReceiver.read_shell {before after : World} {receiver : ResolvedPlace} {access : Access} {observed : Address}
    (finished : FinishesReceiver before receiver access after) (outside : access = .owned → ¬ receiver.address.Prefix observed) :
    (after.read observed).map Value.shell = (before.read observed).map Value.shell := by
  cases finished with
  | lent => rfl
  | owned _ _ _ _ _ _ written => exact World.write_read_shell written (outside rfl)

theorem FinishesReceiver.read_none {before after : World} {receiver : ResolvedPlace} {access : Access} {observed : Address}
    (finished : FinishesReceiver before receiver access after) (absent : before.read observed = none) : after.read observed = none := by
  cases finished with
  | lent => exact absent
  | owned _ _ _ _ _ _ written => exact World.clear_absent written absent

theorem FinishesReceiver.owned_cleared {before after : World} {receiver : ResolvedPlace}
    (finished : FinishesReceiver before receiver .owned after) : after.read receiver.address = none := by
  cases finished with
  | lent different => exact False.elim (different rfl)
  | owned _ _ _ _ _ _ written =>
      have erased := World.write_read_inside written []
      simpa using erased

theorem FinishesEntry.read_none {before after : World} {source : EntrySource} {observed : Address}
    (finished : FinishesEntry before source after) (absent : before.read observed = none) : after.read observed = none := by
  cases finished with
  | supplied => exact absent
  | resident finished | contextual finished => exact finished.read_none absent


theorem ConsumesAvailability.read_outside {before after : World} {address observed : Address}
    {authority : Authority} {identity : Identity} {access : Access}
    (consumed : ConsumesAvailability before address authority identity access after)
    (outside : access = .owned → ¬ address.Overlaps observed) : after.read observed = before.read observed := by
  cases consumed with
  | lent => rfl
  | owned _ _ _ _ _ _ written =>
      have same := World.write_disjoint written (outside rfl)
      exact same

theorem FinishesReceiver.read_outside {before after : World} {receiver : ResolvedPlace}
    {access : Access} {observed : Address} (finished : FinishesReceiver before receiver access after)
    (outside : access = .owned → ¬ receiver.address.Overlaps observed) : after.read observed = before.read observed := by
  cases finished with
  | lent => rfl
  | owned _ _ _ _ _ _ written => exact World.write_disjoint written (outside rfl)

theorem FinishesEntry.read_outside {before after : World} {source : EntrySource} {observed : Address}
    (finished : FinishesEntry before source after)
    (outside : ∀ receiver, source.ownedReceiver = some receiver → ¬ receiver.address.Overlaps observed) :
    after.read observed = before.read observed := by
  cases finished with
  | supplied => rfl
  | resident finished | contextual finished =>
      exact finished.read_outside (fun owned => outside _ (by simp [EntrySource.ownedReceiver,owned]))

theorem PreparesEntryAttempt.read_outside {program : Kernel.Program} {callee : Context} {function : Kernel.Function}
    {before after : World} {source : EntrySource} {inputs : List Kernel.InvocationInput}
    {outcome : Kernel.PreparationOutcome} {observed : Address}
    (prepared : PreparesEntryAttempt program callee function before source inputs after outcome)
    (valid : before.WellFormed) (frontier : observed.root < before.nextRoot)
    (outside : ∀ written ∈ source.clearedStorage function, ¬ written.Overlaps observed) :
    after.read observed = before.read observed := by
  cases prepared with
  | supplied | residentExhausted | contextualReceiverExhausted => rfl
  | resident _ _ lends _ consumes =>
      exact (consumes.read (fun owned contains => outside _ (by
        simp [EntrySource.clearedStorage,EntrySource.ownedReceiver,owned]) contains.overlaps.symm)).trans
        (Kernel.LendsResident.read lends valid frontier)
  | contextual _ _ _ _ receiverLends witnessLends _ consumes consumesAvailability =>
      have middleWell := Kernel.LendsResident.wellFormed receiverLends valid
      have middleBound := Nat.lt_of_lt_of_le frontier (Kernel.LendsResident.nextRoot_le receiverLends)
      exact ((consumesAvailability.read_outside (fun owned => outside _ (by
        simp [EntrySource.clearedStorage,owned]))).trans
        ((consumes.read (fun owned contains => outside _ (by
          simp [EntrySource.clearedStorage,EntrySource.ownedReceiver,owned]) contains.overlaps.symm)).trans
          (Kernel.LendsResident.read witnessLends middleWell middleBound))).trans
        (Kernel.LendsResident.read receiverLends valid frontier)
  | contextualWitnessExhausted _ _ _ _ lends _ => exact Kernel.LendsResident.read lends valid frontier


theorem PreparesEntryAttempt.loan_origin {program : Kernel.Program} {callee : Context} {function : Kernel.Function}
    {before after : World} {source : EntrySource} {inputs : List Kernel.InvocationInput} {outcome : Kernel.PreparationOutcome}
    {identity : Identity} {loan : Loan}
    (prepared : PreparesEntryAttempt program callee function before source inputs after outcome)
    (found : after.loans.get identity = some loan) :
    before.loans.get identity = some loan ∨ ∃ address ∈ source.lentStorage, loan.referent.root = address.root := by
  cases prepared with
  | supplied | residentExhausted | contextualReceiverExhausted => exact Or.inl found
  | resident _ _ lends _ consumes =>
      rw [consumes.loans] at found
      rcases Kernel.LendsResident.loan_origin lends found with original | ⟨borrowed,referent⟩
      · exact Or.inl original
      · refine Or.inr ⟨_,?_,congrArg Address.root referent⟩
        simp [EntrySource.lentStorage,borrowed]
  | contextual _ _ _ _ receiverLends witnessLends _ consumes consumesAvailability =>
      rw [consumesAvailability.loans,consumes.loans] at found
      rcases Kernel.LendsResident.loan_origin witnessLends found with middle | ⟨borrowed,referent⟩
      · rcases Kernel.LendsResident.loan_origin receiverLends middle with original | ⟨borrowed,referent⟩
        · exact Or.inl original
        · refine Or.inr ⟨_,?_,congrArg Address.root referent⟩
          simp [EntrySource.lentStorage,borrowed]
      · refine Or.inr ⟨_,?_,congrArg Address.root referent⟩
        simp [EntrySource.lentStorage,borrowed]
  | contextualWitnessExhausted _ _ _ _ lends _ =>
      rcases Kernel.LendsResident.loan_origin lends found with original | ⟨borrowed,referent⟩
      · exact Or.inl original
      · refine Or.inr ⟨_,?_,congrArg Address.root referent⟩
        simp [EntrySource.lentStorage,borrowed]


theorem PreparesEntryAttempt.activationRoots {program : Kernel.Program} {callee : Context} {function : Kernel.Function}
    {before after : World} {source : EntrySource} {inputs : List Kernel.InvocationInput} {outcome : Kernel.PreparationOutcome}
    {owner : Identity} {kept roots : List Identity}
    (prepared : PreparesEntryAttempt program callee function before source inputs after outcome)
    (valid : before.WellFormed) (selected : Kernel.ActivationRoots before owner kept roots) (different : callee.activation ≠ owner) :
    Kernel.ActivationRoots after owner kept roots := by
  cases prepared with
  | supplied | residentExhausted | contextualReceiverExhausted => exact selected
  | resident _ _ lends _ consumes =>
      exact (Kernel.LendsResident.activationRoots lends valid selected different).of_locations consumes.locations
  | contextual _ _ _ _ receiverLends witnessLends _ consumes consumesAvailability =>
      have initial := Kernel.LendsResident.activationRoots receiverLends valid selected different
      have middle := Kernel.LendsResident.activationRoots witnessLends (Kernel.LendsResident.wellFormed receiverLends valid) initial different
      exact (middle.of_locations consumes.locations).of_locations consumesAvailability.locations
  | contextualWitnessExhausted _ _ _ _ lends _ => exact Kernel.LendsResident.activationRoots lends valid selected different


end Glorious.Language.Execution
