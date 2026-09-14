import GloriousLanguage.BorrowPreservation
import GloriousLanguage.ReferencePersistence
import GloriousLanguage.RootSelection
import GloriousLanguage.LoanResourceRows

/-! The common input binder's actual storage, permission and lease witnesses.
Erased resources retain their real loan records through custody transfer; a
resident lease is never fabricated for a raw contract port. -/
namespace Glorious.Language

theorem AddressType.root_exists {program : Program} {world : World} {address : Address} {type : Term}
    (located : AddressType program world address type) : ∃ root, world.root address = some root := by
  obtain ⟨offset,located⟩ := located
  induction located with
  | @root _ root found live => exact ⟨root,by simp [World.root,found,live]⟩
  | child _ _ ih => exact ih

theorem Authority.guardLoans.loans_congr {before after : World} (loans : after.loans = before.loans)
    (authority : Authority) : authority.guardLoans after = authority.guardLoans before := by
  induction authority with
  | owner => rfl
  | loan => simp only [Authority.guardLoans,loans]
  | shared _ ih => exact ih
  | guarded _ _ ih => simp only [Authority.guardLoans,loans,ih]

theorem Allocates.new_root {program : Program} {before after : World} {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after) :
    ∃ root, after.root address = some root ∧ root.home = home ∧ root.region = region ∧ address.fields = [] := by
  cases allocated
  exact ⟨_,by simp [World.root,Table.get_set]; rfl,rfl,rfl,rfl⟩

/-- A newly created loan continues to exclude its parent in any later
well-formed world retaining that loan. Binding further invocation inputs is
one such transition; merely restricting the callee's own view is insufficient. -/
theorem FormsLoan.excludes_parent_retained {program : RuntimeProgram} {purpose : LoanPurpose}
    {before after later : World} {authority : Authority} {mode : Mutability}
    {region : Identity} {referent handle : Address} {access : Access}
    (valid : before.WellFormed) (future : later.WellFormed)
    (borrowed : FormsLoan program purpose before authority mode region referent handle after)
    (retained : ∀ id loan, after.loans.get id = some loan →
      ∃ current, later.loans.get id = some current ∧ current.permissionState = loan.permissionState)
    (conflict : Conflict access mode) : ¬ Permitted later authority access referent := by
  cases borrowed with
  | borrow _ _ _ _ _ _ permitted _ _ _ _ =>
    obtain ⟨current,found,shape⟩ := retained before.nextLoan _ (Table.get_set _ _ _)
    obtain ⟨_,_,atReferent,atMode,_,live,_,_⟩ := Loan.permissionState_eq_iff.mp shape
    exact Permitted.excludes_new_loan valid future permitted found live (Nat.le_refl _)
      (by rw [atReferent]; exact (Address.Prefix.refl referent).overlaps)
      (by rw [atMode]; exact conflict)

theorem ClaimsStorage.excludes_parent_retained {recipient : ClaimCustody}
    {before after later : World} {authority : Authority} {available requested : Access}
    {address : Address} {identity : Identity}
    (valid : before.WellFormed) (future : later.WellFormed)
    (claimed : ClaimsStorage recipient before authority available address identity after)
    (retained : ∀ id loan, after.loans.get id = some loan →
      ∃ current, later.loans.get id = some current ∧ current.permissionState = loan.permissionState)
    (conflict : Conflict requested (if available = .shared then .shared else .unique)) :
    ¬ Permitted later authority requested address := by
  cases claimed with
  | claim _ _ permitted =>
    obtain ⟨current,found,shape⟩ := retained before.nextLoan _ (Table.get_set _ _ _)
    obtain ⟨_,_,atReferent,atMode,_,live,_,_⟩ := Loan.permissionState_eq_iff.mp shape
    exact Permitted.excludes_new_loan valid future permitted found live (Nat.le_refl _)
      (by rw [atReferent]; exact (Address.Prefix.refl address).overlaps)
      (by rw [atMode]; exact conflict)

namespace Kernel

theorem LendsResident.wellFormed {program : RuntimeProgram} {before after : World}
    {activation scope region address authority access lease permission}
    (lent : LendsResident program activation scope region before address authority access lease permission after)
    (valid : before.WellFormed) : after.WellFormed := by
  cases lent with
  | owned => exact valid
  | lent _ _ _ allocated borrowed => exact borrowed.wellFormed (allocated.wellFormed valid)

theorem LendsResident.loan_origin {program : RuntimeProgram} {before after : World}
    {activation scope region address authority access lease result} {identity : Identity} {loan : Loan}
    (lent : LendsResident program activation scope region before address authority access lease result after)
    (found : after.loans.get identity = some loan) :
    before.loans.get identity = some loan ∨ (access ≠ .owned ∧ loan.referent = address) := by
  cases lent with
  | owned => exact Or.inl found
  | lent modes _ _ allocated formed =>
      rcases formed.loan_origin found with original | referent
      · exact Or.inl (by rw [allocated.loans] at original; exact original)
      · refine Or.inr ⟨?_,referent⟩
        rcases modes with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> simp


theorem LendsResident.result_recorded {program : RuntimeProgram} {before after : World}
    {activation scope region address authority access lease result}
    (lent : LendsResident program activation scope region before address authority access lease result after)
    (recorded : authority.Recorded before.loans) : result.Recorded after.loans := by
  cases lent with
  | owned => exact recorded
  | lent _ _ _ _ formed =>
      cases formed
      exact ⟨_,Table.get_set _ _ _⟩

theorem BindsInputAt.wellFormed {recipient : ClaimCustody} {program : RuntimeProgram} {before after : World}
    {activation scope region input binding}
    (bound : BindsInputAt program recipient activation scope region before input binding after)
    (valid : before.WellFormed) : after.WellFormed := by
  cases bound with
  | lent _ _ _ _ _ _ _ lent => exact lent.wellFormed valid
  | owned _ _ _ _ _ allocated transferred => exact transferred.wellFormed (allocated.wellFormed valid)
  | storage _ _ _ claimed => exact claimed.wellFormed valid
  | allocation _ _ _ _ transferred => exact transferred.wellFormed valid
  | guardedAllocation _ _ _ _ _ claimed => exact claimed.wellFormed valid
  | loan _ _ _ _ transferred => exact transferred.wellFormed valid

theorem BindsInputsFor.wellFormed {recipient : ClaimCustody} {footprint : List Address} {program : RuntimeProgram} {before after : World}
    {activation scope region inputs bindings}
    (bound : BindsInputsFor program recipient activation scope region footprint before inputs bindings after)
    (valid : before.WellFormed) : after.WellFormed := by
  induction bound using Kernel.BindsInputsFor.inductionOn with
  | nil => exact valid
  | cons _ first _ ih => exact ih (first.wellFormed valid)

theorem BindsPattern.wellFormed {program : RuntimeProgram} {before after : World}
    {activation scope region localSlot source authority access binding}
    (bound : BindsPattern program activation scope region before localSlot source authority access binding after)
    (valid : before.WellFormed) : after.WellFormed := by
  cases bound with
  | owned bound => exact bound.wellFormed valid
  | borrowed _ _ allocated borrowed => exact borrowed.wellFormed (allocated.wellFormed valid)

theorem LendsResident.lent_authority {program : RuntimeProgram} {before after : World}
    {activation scope region address authority access lease permission}
    (lent : LendsResident program activation scope region before address authority access lease permission after)
    (borrowed : access ≠ .owned) : ∃ loan, permission = .loan loan := by
  cases lent with
  | owned => exact False.elim (borrowed rfl)
  | lent => exact ⟨_,rfl⟩

/-- Owned entry keeps its actual authority; lent entry obtains the permission
of its freshly created receiver/reference loan. No post-world access is given. -/
theorem LendsResident.borrower_permitted {program : RuntimeProgram} {before after : World}
    {activation scope region : Identity} {address : Address} {authority permission : Authority}
    {access : Access} {lease : Option InvocationLease}
    (valid : before.WellFormed)
    (lent : LendsResident program activation scope region before address authority access lease permission after)
    (permitted : Permitted before authority access address) : Permitted after permission access address := by
  cases lent with
  | owned => exact permitted
  | lent modes _ _ allocated borrowed =>
    have received := borrowed.borrower_permitted (allocated.wellFormed valid)
    rcases modes with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> exact received

theorem BindsInputAt.lent_authority {recipient : ClaimCustody} {program : RuntimeProgram} {before after : World}
    {activation scope region input binding}
    (bound : BindsInputAt program recipient activation scope region before input binding after)
    (borrowed : input.access ≠ .owned) (resident : input.formal.IsResident) :
    ∃ loan, binding.authority = .loan loan := by
  cases bound with
  | owned _ owning _ _ _ _ _ => exact False.elim (borrowed owning)
  | lent _ _ _ _ _ _ _ lent => exact lent.lent_authority borrowed
  | storage _ formal _ _ => simp only [formal,InputFormal.IsResident] at resident
  | allocation _ formal _ _ _ => simp only [formal,InputFormal.IsResident] at resident
  | guardedAllocation _ formal _ _ _ _ => simp only [formal,InputFormal.IsResident] at resident
  | loan _ formal _ _ _ => simp only [formal,InputFormal.IsResident] at resident

theorem LendsResident.shared_no_mutation {program : RuntimeProgram} {before after : World}
    {activation scope region address authority lease permission} {requested : Access}
    (lent : LendsResident program activation scope region before address authority .shared lease permission after)
    (writes : requested ≠ .shared) : ¬ Permitted after permission requested address := by
  cases lent with
  | lent modes _ _ _ formed =>
    rcases modes with ⟨_,rfl⟩ | ⟨impossible,_⟩
    · cases formed
      intro permitted
      obtain ⟨_,active,found,_,_,_,_,mode,_⟩ := permitted
      simp only [Table.get_set,Option.some.injEq] at found
      subst active
      cases mode writes
    · cases impossible

theorem BindsInputAt.shared_no_mutation {recipient : ClaimCustody} {program : RuntimeProgram} {before after : World}
    {activation scope region input binding} {requested : Access}
    (bound : BindsInputAt program recipient activation scope region before input binding after)
    (shared : input.access = .shared) (writes : requested ≠ .shared) :
    ¬ Permitted after binding.authority requested binding.address := by
  cases bound with
  | owned _ owning _ _ _ _ _ => cases owning.symm.trans shared
  | lent _ _ _ _ _ _ _ lent => exact (shared ▸ lent).shared_no_mutation writes
  | storage _ _ _ claimed =>
      change ¬ Permitted after (ClaimedAuthority input.access _) requested input.storage
      rw [shared]
      intro permission
      exact writes permission.2.1
  | allocation _ _ owned _ _ | guardedAllocation _ _ owned _ _ _ | loan _ _ owned _ _ =>
      cases owned.symm.trans shared

theorem LendsResident.loan_retained {program : RuntimeProgram} {before after : World}
    {activation scope region address authority access lease permission}
    (valid : before.WellFormed)
    (lent : LendsResident program activation scope region before address authority access lease permission after)
    {id : Identity} {loan : Loan} (found : before.loans.get id = some loan) :
    after.loans.get id = some loan := by
  cases lent with
  | owned => exact found
  | lent _ _ _ allocated borrowed =>
    exact borrowed.old_loan (allocated.wellFormed valid) (by simpa only [allocated.loans] using found)

theorem LendsResident.excludes_parent_retained {program : RuntimeProgram} {before after later : World}
    {activation scope region address authority access lease permission} {requested : Access}
    (valid : before.WellFormed) (future : later.WellFormed)
    (lent : LendsResident program activation scope region before address authority access lease permission after)
    (borrowed : access ≠ .owned) (conflict : requested ≠ .shared ∨ access = .unique)
    (retained : ∀ id loan, after.loans.get id = some loan →
      ∃ current, later.loans.get id = some current ∧ current.permissionState = loan.permissionState) :
    ¬ Permitted later authority requested address := by
  cases lent with
  | owned => exact False.elim (borrowed rfl)
  | lent modes _ _ allocated formed =>
    apply formed.excludes_parent_retained (allocated.wellFormed valid) future retained
    rcases conflict with writes | unique
    · exact Or.inl writes
    · rcases modes with ⟨shared,_⟩ | ⟨_,mode⟩
      · cases shared.symm.trans unique
      · exact Or.inr mode

theorem BindsInputAt.loan_retained {recipient : ClaimCustody} {program : RuntimeProgram} {before after : World}
    {activation scope region input binding}
    (valid : before.WellFormed)
    (bound : BindsInputAt program recipient activation scope region before input binding after)
    {id : Identity} {loan : Loan} (found : before.loans.get id = some loan) :
    ∃ current, after.loans.get id = some current ∧ current.permissionState = loan.permissionState := by
  cases bound with
  | lent _ _ _ _ _ _ _ lent => exact ⟨loan,lent.loan_retained valid found,rfl⟩
  | owned _ _ _ _ _ allocated transferred => exact ⟨loan,by simpa only [transferred.loans,allocated.loans] using found,rfl⟩
  | storage _ _ _ claimed => exact ⟨loan,claimed.old_loan valid found,rfl⟩
  | allocation _ _ _ _ transferred => exact transferred.retained found
  | guardedAllocation _ _ _ _ _ claimed => exact ⟨loan,claimed.old_loan valid found,rfl⟩
  | loan _ _ _ _ transferred => exact transferred.retained found

theorem BindsInputsFor.loan_retained {recipient : ClaimCustody} {footprint : List Address} {program : RuntimeProgram} {before after : World}
    {activation scope region inputs bindings}
    (valid : before.WellFormed)
    (bound : BindsInputsFor program recipient activation scope region footprint before inputs bindings after)
    {id : Identity} {loan : Loan} (found : before.loans.get id = some loan) :
    ∃ current, after.loans.get id = some current ∧ current.permissionState = loan.permissionState := by
  induction bound using Kernel.BindsInputsFor.inductionOn generalizing loan with
  | nil => exact ⟨loan,found,rfl⟩
  | cons _ first _ ih =>
      obtain ⟨middle,selected,same⟩ := first.loan_retained valid found
      obtain ⟨current,present,shape⟩ := ih (loan := middle) (first.wellFormed valid) selected
      exact ⟨current,present,shape.trans same⟩

theorem BindsInputAt.excludes_parent_retained {recipient : ClaimCustody} {program : RuntimeProgram}
    {before after later : World} {activation scope region input binding} {requested : Access}
    (valid : before.WellFormed) (future : later.WellFormed)
    (bound : BindsInputAt program recipient activation scope region before input binding after)
    (borrowed : input.access ≠ .owned) (conflict : requested ≠ .shared ∨ input.access = .unique)
    (retained : ∀ id loan, after.loans.get id = some loan →
      ∃ current, later.loans.get id = some current ∧ current.permissionState = loan.permissionState) :
    ¬ Permitted later input.authority requested input.storage := by
  cases bound with
  | lent _ _ _ _ _ _ _ lent => exact lent.excludes_parent_retained valid future borrowed conflict retained
  | owned _ owning _ _ _ _ _ => exact False.elim (borrowed owning)
  | allocation _ _ owning _ _ => exact False.elim (borrowed owning)
  | guardedAllocation _ _ owning _ _ _ => exact False.elim (borrowed owning)
  | loan _ _ owning _ _ => exact False.elim (borrowed owning)
  | storage _ _ _ claimed =>
      apply claimed.excludes_parent_retained valid future retained
      rcases conflict with writes | unique
      · exact Or.inl writes
      · exact Or.inr (by simp only [unique,reduceCtorEq,if_false])

/-- Capture and argument origins make no difference to exclusivity. Every
lent input obtains its own loan, which the remaining bindings retain. -/
theorem BindsInputsFor.lent_parent_exclusive {recipient : ClaimCustody} {footprint : List Address} {program : RuntimeProgram} {before after : World}
    {activation scope region inputs bindings} {input : InvocationInput} {requested : Access}
    (valid : before.WellFormed)
    (bound : BindsInputsFor program recipient activation scope region footprint before inputs bindings after)
    (member : input ∈ inputs) (borrowed : input.access ≠ .owned)
    (conflict : requested ≠ .shared ∨ input.access = .unique) :
    ¬ Permitted after input.authority requested input.storage := by
  induction bound using Kernel.BindsInputsFor.inductionOn with
  | nil => simp at member
  | cons _ first rest ih =>
    have middleValid := first.wellFormed valid
    rcases List.mem_cons.mp member with rfl | member
    · exact first.excludes_parent_retained valid (rest.wellFormed middleValid) borrowed conflict
        (fun _ _ found => rest.loan_retained middleValid found)
    · exact ih middleValid member

/-- Lent-input exclusivity holds in any later world that retains the binder's
rows, up to their permission projection. The bound row the binder created for
the input is still present and unique there. -/
theorem BindsInputsFor.lent_parent_exclusive_retained {recipient : ClaimCustody} {footprint : List Address}
    {program : RuntimeProgram} {before after later : World}
    {activation scope region inputs bindings} {input : InvocationInput} {requested : Access}
    (valid : before.WellFormed) (future : later.WellFormed)
    (bound : BindsInputsFor program recipient activation scope region footprint before inputs bindings after)
    (member : input ∈ inputs) (borrowed : input.access ≠ .owned)
    (conflict : requested ≠ .shared ∨ input.access = .unique)
    (retained : ∀ id loan, after.loans.get id = some loan →
      ∃ current, later.loans.get id = some current ∧ current.permissionState = loan.permissionState) :
    ¬ Permitted later input.authority requested input.storage := by
  induction bound using Kernel.BindsInputsFor.inductionOn with
  | nil => simp at member
  | cons _ first rest ih =>
    have middleValid := first.wellFormed valid
    rcases List.mem_cons.mp member with rfl | member
    · refine first.excludes_parent_retained valid future borrowed conflict ?_
      intro id loan found
      obtain ⟨middleRow,atAfter,shape1⟩ := rest.loan_retained middleValid found
      obtain ⟨current,atLater,shape2⟩ := retained id middleRow atAfter
      exact ⟨current,atLater,shape2.trans shape1⟩
    · exact ih middleValid member retained

theorem LendsResident.read {program : RuntimeProgram} {before after : World}
    {activation scope region address authority access lease permission} {observed : Address}
    (lent : LendsResident program activation scope region before address authority access lease permission after)
    (valid : before.WellFormed) (frontier : observed.root < before.nextRoot) : after.read observed = before.read observed := by
  cases lent with
  | owned => rfl
  | lent _ _ _ allocated formed =>
      cases formed with
      | borrow _ _ _ _ _ _ _ _ _ _ written =>
          refine (World.write_disjoint written ?_).trans (allocated.read valid observed)
          intro overlap
          exact (Nat.ne_of_lt frontier) (overlap.1.symm.trans allocated.fresh_root.1)


theorem LendsResident.nextRoot_le {program : RuntimeProgram} {before after : World}
    {activation scope region address authority access lease permission}
    (lent : LendsResident program activation scope region before address authority access lease permission after) :
    before.nextRoot ≤ after.nextRoot := by
  cases lent with
  | owned => exact Nat.le_refl _
  | lent _ _ _ allocated formed =>
      rw [Glorious.Language.FormsLoan.nextRoot formed,allocated.fresh_root.2]
      exact Nat.le_succ _


theorem LendsResident.root_retained {program : RuntimeProgram} {before after : World}
    {activation scope region address authority access lease permission}
    (valid : before.WellFormed)
    (lent : LendsResident program activation scope region before address authority access lease permission after)
    {observed : Address} {root : Root} (found : before.root observed = some root) :
    ∃ changed, after.root observed = some changed ∧ changed.location = root.location := by
  cases lent with
  | owned => exact ⟨root,found,rfl⟩
  | lent _ _ _ allocated borrowed =>
    exact World.root_transport borrowed.locations (allocated.root valid found)

theorem BindsInputAt.root_retained {recipient : ClaimCustody} {program : RuntimeProgram} {before after : World}
    {activation scope region input binding}
    (valid : before.WellFormed)
    (bound : BindsInputAt program recipient activation scope region before input binding after)
    {observed : Address} {root : Root} (found : before.root observed = some root) :
    ∃ changed, after.root observed = some changed ∧ changed.location = root.location := by
  cases bound with
  | lent _ _ _ _ _ _ _ lent => exact lent.root_retained valid found
  | owned _ _ _ _ _ allocated transferred =>
    exact World.root_transport transferred.locations (allocated.root valid found)
  | storage _ _ _ claimed => cases claimed; exact ⟨root,found,rfl⟩
  | allocation _ _ _ _ transferred => cases transferred; exact ⟨root,found,rfl⟩
  | guardedAllocation _ _ _ _ _ claimed => cases claimed; exact ⟨root,found,rfl⟩
  | loan _ _ _ _ transferred => cases transferred <;> exact ⟨root,found,rfl⟩

theorem BindsInputsFor.root_retained {recipient : ClaimCustody} {footprint : List Address} {program : RuntimeProgram} {before after : World}
    {activation scope region inputs bindings}
    (valid : before.WellFormed)
    (bound : BindsInputsFor program recipient activation scope region footprint before inputs bindings after)
    {observed : Address} {root : Root} (found : before.root observed = some root) :
    ∃ changed, after.root observed = some changed ∧ changed.location = root.location := by
  induction bound using Kernel.BindsInputsFor.inductionOn generalizing root with
  | nil => exact ⟨root,found,rfl⟩
  | cons _ first _ ih =>
    obtain ⟨middle,selected,location⟩ := first.root_retained valid found
    obtain ⟨changed,present,equal⟩ := ih (first.wellFormed valid) selected
    exact ⟨changed,present,equal.trans location⟩

theorem BindsInputsAttemptFor.loan_retained {recipient : ClaimCustody} {footprint : List Address} {program : RuntimeProgram} {before after : World}
    {activation scope region inputs bindings} {outcome : Kernel.PreparationOutcome}
    (valid : before.WellFormed)
    (bound : Kernel.BindsInputsAttemptFor program recipient activation scope region footprint before inputs bindings after outcome)
    {id : Identity} {loan : Loan} (found : before.loans.get id = some loan) :
    ∃ current, after.loans.get id = some current ∧ current.permissionState = loan.permissionState := by
  induction bound generalizing loan with
  | nil => exact ⟨loan,found,rfl⟩
  | cons _ first _ ih =>
      obtain ⟨middle,selected,same⟩ := first.loan_retained valid found
      obtain ⟨current,present,shape⟩ := ih (first.wellFormed valid) selected
      exact ⟨current,present,shape.trans same⟩
  | exhausted => exact ⟨loan,found,rfl⟩

/-- The ordered outcome-indexed fold retains root locations on every prefix;
an exhausted attempt leaves its input world unchanged. -/
theorem BindsInputsAttemptFor.root_retained {recipient : ClaimCustody} {footprint : List Address} {program : RuntimeProgram} {before after : World}
    {activation scope region inputs bindings} {outcome : Kernel.PreparationOutcome}
    (valid : before.WellFormed)
    (bound : Kernel.BindsInputsAttemptFor program recipient activation scope region footprint before inputs bindings after outcome)
    {observed : Address} {root : Root} (found : before.root observed = some root) :
    ∃ changed, after.root observed = some changed ∧ changed.location = root.location := by
  induction bound generalizing root with
  | nil => exact ⟨root,found,rfl⟩
  | cons _ first _ ih =>
      obtain ⟨middle,selected,location⟩ := first.root_retained valid found
      obtain ⟨changed,present,equal⟩ := ih (first.wellFormed valid) selected
      exact ⟨changed,present,equal.trans location⟩
  | exhausted => exact ⟨root,found,rfl⟩

theorem BindsInputAt.binding_root {recipient : ClaimCustody} {program : RuntimeProgram} {before after : World}
    {activation scope region input binding}
    (bound : BindsInputAt program recipient activation scope region before input binding after)
    (valid : before.WellFormed) : ∃ root, after.root binding.address = some root := by
  cases bound with
  | lent _ _ _ stored _ _ _ lent =>
    obtain ⟨root,found,_⟩ := Option.bind_eq_some_iff.mp stored
    obtain ⟨changed,present,_⟩ := lent.root_retained valid found
    exact ⟨changed,present⟩
  | owned _ _ _ _ _ allocated transferred =>
    obtain ⟨root,found,_,_,_⟩ := allocated.new_root
    obtain ⟨changed,present,_⟩ := World.root_transport transferred.locations found
    exact ⟨changed,present⟩
  | storage _ _ located claimed =>
    obtain ⟨root,found⟩ := located.root_exists
    cases claimed
    exact ⟨root,found⟩
  | allocation _ _ _ located transferred =>
    obtain ⟨root,found⟩ := located.root_exists
    cases transferred
    exact ⟨root,found⟩
  | guardedAllocation _ _ _ _ located claimed =>
    obtain ⟨root,found⟩ := located.root_exists
    cases claimed
    exact ⟨root,found⟩
  | loan _ _ _ located transferred =>
    obtain ⟨root,found⟩ := located.root_exists
    cases transferred <;> exact ⟨root,found⟩

theorem BindsInputsFor.binding_roots {recipient : ClaimCustody} {footprint : List Address} {program : RuntimeProgram} {before after : World}
    {activation scope region inputs bindings}
    (bound : BindsInputsFor program recipient activation scope region footprint before inputs bindings after)
    (valid : before.WellFormed) :
    ∀ binding ∈ bindings, ∃ root, after.root binding.address = some root := by
  induction bound using Kernel.BindsInputsFor.inductionOn with
  | nil => simp
  | cons _ first rest ih =>
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨root,found⟩ := first.binding_root valid
      obtain ⟨changed,present,_⟩ := rest.root_retained (first.wellFormed valid) found
      exact ⟨changed,present⟩
    · exact ih (first.wellFormed valid) binding member

theorem BindsInputsFor.bindings_root_bound {recipient : ClaimCustody} {footprint : List Address} {program : RuntimeProgram} {before after : World}
    {activation scope region inputs bindings}
    (bound : BindsInputsFor program recipient activation scope region footprint before inputs bindings after)
    (valid : before.WellFormed) : ∀ binding ∈ bindings, binding.address.root < after.nextRoot := by
  intro binding member
  obtain ⟨root,found⟩ := bound.binding_roots valid binding member
  exact World.root_bound (bound.wellFormed valid) (World.root_found found).1

theorem BindsPattern.binding_root {program : RuntimeProgram} {before after : World}
    {activation scope region localSlot source authority access binding}
    (bound : BindsPattern program activation scope region before localSlot source authority access binding after)
    (valid : before.WellFormed) : ∃ root, after.root binding.address = some root := by
  cases bound with
  | owned bound => exact bound.binding_root valid
  | borrowed _ _ allocated borrowed =>
    obtain ⟨root,found,_,_,_⟩ := allocated.new_root
    obtain ⟨changed,present,_⟩ := World.root_transport borrowed.locations found
    exact ⟨changed,present⟩

theorem BindsPattern.root_bound {program : RuntimeProgram} {before after : World}
    {activation scope region localSlot source authority access binding}
    (bound : BindsPattern program activation scope region before localSlot source authority access binding after)
    (valid : before.WellFormed) : binding.address.root < after.nextRoot := by
  obtain ⟨root,found⟩ := bound.binding_root valid
  exact World.root_bound (bound.wellFormed valid) (World.root_found found).1

/-- The actual temporary allocation and loan formation jointly produce the
invocation guard. Its resident handle, dynamic home and returned authority
all refer to the same lease identity, not an independent ownership table. -/
theorem LendsResident.lease_origin {program : RuntimeProgram} {before after : World}
    {activation scope region address authority access lease permission}
    (lent : LendsResident program activation scope region before address authority access lease permission after)
    (borrowed : access ≠ .owned) :
    ∃ witness root owner mode type sourceRegion, lease = some witness ∧ permission = .loan witness.loan ∧
      witness.handle.fields = [] ∧ after.root witness.handle = some root ∧
      root.home = .temporary activation scope ∧ root.region = region ∧
      authority.BorrowRegion before address sourceRegion ∧
      after.Stores witness.handle (.resident owner (.reference mode (.runtimeRegion sourceRegion) type)
        (.reference witness.loan) true []) ∧
      after.loans.get witness.loan = some
        ⟨witness.loan,authority.parentLoan,address,mode,sourceRegion,true,.restoring,authority.guardLoans before,false,none⟩ := by
  cases lent with
  | owned => exact False.elim (borrowed rfl)
  | lent _ _ borrowedRegion allocated formed =>
    obtain ⟨original,selected,home,atRegion,whole⟩ := allocated.new_root
    obtain ⟨retained,found,same⟩ := World.root_transport formed.locations selected
    obtain ⟨type,stored,loan⟩ := formed.created_handle
    refine ⟨_,retained,_,_,type,_,rfl,rfl,whole,found,?_,?_,borrowedRegion,stored,?_⟩
    · have unchanged : retained.home = original.home := by
        simpa only [Root.location] using congrArg Root.home same
      exact unchanged.trans home
    · have unchanged : retained.region = original.region := by
        simpa only [Root.location] using congrArg Root.region same
      exact unchanged.trans atRegion
    · simpa only [LoanPurpose.kind,Authority.guardLoans.loans_congr allocated.loans] using loan

/-- The lifetime witness is real storage owned by the activation supplied to
the common loan producer, with the same fresh identity recorded in the loan. -/
theorem LendsResident.lease_owned {program : RuntimeProgram} {before after : World}
    {activation scope region address authority access lease permission}
    (lent : LendsResident program activation scope region before address authority access lease permission after)
    (borrowed : access ≠ .owned) :
    ∃ witness root, lease = some witness ∧ after.root witness.handle = some root ∧
      root.home = .temporary activation scope ∧ root.region = region ∧ witness.handle.fields = [] := by
  obtain ⟨witness,root,_,_,_,_,selected,_,whole,found,home,atRegion,_,_,_⟩ := lent.lease_origin borrowed
  exact ⟨witness,root,selected,found,home,atRegion,whole⟩

theorem LendsResident.activationRoots {program : RuntimeProgram} {before after : World}
    {activation scope region address authority access lease result} {owner : Identity} {kept roots : List Identity}
    (lent : LendsResident program activation scope region before address authority access lease result after)
    (valid : before.WellFormed) (selected : ActivationRoots before owner kept roots) (different : activation ≠ owner) :
    ActivationRoots after owner kept roots := by
  cases lent with
  | owned => exact selected
  | lent _ _ _ allocated formed =>
      exact (allocated.activationRoots valid selected (by simp [HomeOwnedByActivation,different])).of_locations formed.locations

theorem BindsInputAt.activationRoots {program : RuntimeProgram} {recipient : ClaimCustody} {before after : World}
    {activation scope region : Identity} {input : InvocationInput} {binding : Binding} {owner : Identity} {kept roots : List Identity}
    (bound : BindsInputAt program recipient activation scope region before input binding after)
    (valid : before.WellFormed) (selected : ActivationRoots before owner kept roots) (different : activation ≠ owner) :
    ActivationRoots after owner kept roots := by
  cases bound with
  | lent _ _ _ _ _ _ _ lent => exact lent.activationRoots valid selected different
  | owned _ _ _ _ _ allocated moved =>
      exact (allocated.activationRoots valid selected (by simp [HomeOwnedByActivation,different])).of_locations moved.locations
  | storage _ _ _ claimed => cases claimed; exact selected
  | guardedAllocation _ _ _ _ _ claimed => cases claimed; exact selected
  | allocation _ _ _ _ moved => exact selected.of_locations (fun _ => by rw [Glorious.Language.TransfersAllocation.roots_eq moved])
  | loan _ _ _ _ moved => exact selected.of_locations (fun _ => by rw [Glorious.Language.TransfersStorageLoan.roots_eq moved])

theorem BindsInputsAttemptFor.activationRoots {program : RuntimeProgram} {recipient : ClaimCustody} {before after : World}
    {activation scope region : Identity} {footprint : List Address} {inputs : List InvocationInput} {bindings : Environment}
    {outcome : PreparationOutcome} {owner : Identity} {kept roots : List Identity}
    (bound : BindsInputsAttemptFor program recipient activation scope region footprint before inputs bindings after outcome)
    (valid : before.WellFormed) (selected : ActivationRoots before owner kept roots) (different : activation ≠ owner) :
    ActivationRoots after owner kept roots := by
  induction bound with
  | nil | exhausted => exact selected
  | cons _ first _ ih => exact ih (first.wellFormed valid) (first.activationRoots valid selected different)


end Kernel


end Glorious.Language
