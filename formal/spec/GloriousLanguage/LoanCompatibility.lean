import GloriousLanguage.BorrowConstructionPreservation

/-! One actual fresh loan changes permission only through its overlap/mode
and incoming guards. Compatibility is stated entirely on the pre-world;
old ancestry and every authority carrier are read from the same loan table. -/
namespace Glorious.Language

theorem World.fresh_loan_retained {before after : World} {fresh : Loan}
    (valid : before.WellFormed) (loans : after.loans = before.loans.set before.nextLoan fresh)
    {identity : Identity} {original : Loan} (found : before.loans.get identity = some original) :
    after.loans.get identity = some original := by
  rw [loans,Table.get_set_other _ _ _ _ (Nat.ne_of_lt (World.loanBounds valid found))]
  exact found

theorem AncestorLoan.fresh_loan_reflect {before after : World} {fresh : Loan} {ancestor descendant : Identity}
    (valid : before.WellFormed) (loans : after.loans = before.loans.set before.nextLoan fresh)
    (related : AncestorLoan after ancestor descendant) (old : descendant < before.nextLoan) :
    AncestorLoan before ancestor descendant := by
  induction related with
  | refl => exact .refl
  | @parent parent child loan found link prior ih =>
      have original : before.loans.get child = some loan := by
        simpa only [loans,Table.get_set_other _ _ _ _ (Nat.ne_of_lt old)] using found
      obtain ⟨_,_,ordered,_⟩ := World.loanParents valid child loan parent original link
      exact .parent original link (ih (Nat.lt_trans ordered old))

theorem LoanPermission.fresh_loan {before after : World} {fresh : Loan} {identity : Identity}
    {requested : Access} {address : Address}
    (valid : before.WellFormed) (loans : after.loans = before.loans.set before.nextLoan fresh)
    (permission : LoanPermission before identity requested address)
    (compatible : fresh.live = true →
      (address.Overlaps fresh.referent → ¬ Conflict requested fresh.mode) ∧
      (identity ∈ fresh.guards → requested = .shared)) :
    LoanPermission after identity requested address := by
  obtain ⟨active,found,live,root,generation,path,mode,excluded,guards,dependent⟩ := permission
  have retained : ∀ id loan, before.loans.get id = some loan → after.loans.get id = some loan :=
    fun _ _ => World.fresh_loan_retained valid loans
  refine ⟨active,retained _ _ found,live,root,generation,path,mode,?_,?_,?_⟩
  · intro other loan selected alive different overlap conflict
    by_cases new : other = before.nextLoan
    · subst other
      have same : loan = fresh := Option.some.inj (selected.symm.trans (by rw [loans,Table.get_set]))
      subst loan
      exact False.elim ((compatible alive).1 overlap conflict)
    · have old : before.loans.get other = some loan := by
        simpa only [loans,Table.get_set_other _ _ _ _ new] using selected
      exact (excluded other loan old alive different overlap conflict).transport_parents
        (fun id original selected => ⟨original,retained id original selected,rfl⟩)
  · intro guard member
    obtain ⟨loan,selected,alive⟩ := guards guard member
    exact ⟨loan,retained _ _ selected,alive⟩
  · intro other loan selected alive member
    by_cases new : other = before.nextLoan
    · subst other
      have same : loan = fresh := Option.some.inj (selected.symm.trans (by rw [loans,Table.get_set]))
      subst loan
      exact (compatible alive).2 member
    · exact dependent other loan
        (by simpa only [loans,Table.get_set_other _ _ _ _ new] using selected) alive member

theorem LoanPermission.fresh_loan_compatible {before after : World} {fresh : Loan} {identity : Identity}
    {requested : Access} {address : Address}
    (valid : before.WellFormed) (loans : after.loans = before.loans.set before.nextLoan fresh)
    (permission : LoanPermission before identity requested address)
    (preserved : LoanPermission after identity requested address) (live : fresh.live = true) :
    (address.Overlaps fresh.referent → ¬ Conflict requested fresh.mode) ∧
      (identity ∈ fresh.guards → requested = .shared) := by
  obtain ⟨original,found,_⟩ := permission
  have bound := World.loanBounds valid found
  have freshFound : after.loans.get before.nextLoan = some fresh := by rw [loans,Table.get_set]
  obtain ⟨active,selected,alive,root,generation,path,mode,excluded,guards,dependent⟩ := preserved
  refine ⟨?_,dependent _ _ freshFound live⟩
  intro overlap conflict
  have ancestry := excluded _ _ freshFound live (Ne.symm (Nat.ne_of_lt bound)) overlap conflict
  have old := ancestry.fresh_loan_reflect valid loans bound
  exact Nat.not_lt_of_ge (old.identity_le (World.loanParents valid)) bound

theorem Permitted.fresh_loan {before after : World} {fresh : Loan} {authority : Authority}
    {requested : Access} {address : Address}
    (valid : before.WellFormed) (locations : before.LocationExtension after)
    (loans : after.loans = before.loans.set before.nextLoan fresh)
    (permission : Permitted before authority requested address)
    (compatible : fresh.live = true →
      authority.LoanCompatible before requested address fresh.referent fresh.mode fresh.guards) :
    Permitted after authority requested address := by
  obtain ⟨root,selected⟩ := permission.root
  obtain ⟨current,found,_⟩ := locations.root selected
  induction authority with
  | owner =>
      refine ⟨⟨current,found⟩,?_⟩
      intro identity loan selected live overlap conflict
      by_cases new : identity = before.nextLoan
      · subst identity
        have same : loan = fresh := Option.some.inj (selected.symm.trans (by rw [loans,Table.get_set]))
        subst loan
        exact compatible live overlap conflict
      · exact permission.2 identity loan
          (by simpa only [loans,Table.get_set_other _ _ _ _ new] using selected) live overlap conflict
  | loan identity => exact ⟨⟨current,found⟩,permission.2.fresh_loan valid loans compatible⟩
  | shared backing ih => exact ⟨⟨current,found⟩,permission.2.1,ih permission.2.2 compatible⟩
  | guarded backing carrier ih =>
      obtain ⟨loan,selected,allowed⟩ := permission.2.2
      exact ⟨⟨current,found⟩,ih permission.2.1 (fun live => (compatible live).1),
        loan,World.fresh_loan_retained valid loans selected,
        allowed.fresh_loan valid loans (fun live => (compatible live).2 loan selected)⟩

theorem Permitted.fresh_loan_compatible {before after : World} {fresh : Loan} {authority : Authority}
    {requested : Access} {address : Address}
    (valid : before.WellFormed) (loans : after.loans = before.loans.set before.nextLoan fresh)
    (permission : Permitted before authority requested address)
    (preserved : Permitted after authority requested address) (live : fresh.live = true) :
    authority.LoanCompatible before requested address fresh.referent fresh.mode fresh.guards := by
  induction authority with
  | owner => exact fun overlap => preserved.2 _ _ (by rw [loans,Table.get_set]) live overlap
  | loan identity => exact permission.2.fresh_loan_compatible valid loans preserved.2 live
  | shared backing ih => exact ih permission.2.2 preserved.2.2
  | guarded backing carrier ih =>
      refine ⟨ih permission.2.1 preserved.2.1,?_⟩
      intro loan selected
      obtain ⟨original,found,allowed⟩ := permission.2.2
      have same := Option.some.inj (selected.symm.trans found)
      subst original
      obtain ⟨current,afterFound,afterAllowed⟩ := preserved.2.2
      have retained := World.fresh_loan_retained valid loans selected
      have same := Option.some.inj (retained.symm.trans afterFound)
      subst current
      exact allowed.fresh_loan_compatible valid loans afterAllowed live

/-- Exact permission criterion for an actual fresh-row insertion. Pre-state
permission is the input; the right side mentions only source geometry, mode
and guards. New parent/kind/custody fields need no artificial restriction. -/
theorem Permitted.fresh_loan_iff {before after : World} {fresh : Loan} {authority : Authority}
    {requested : Access} {address : Address}
    (valid : before.WellFormed) (locations : before.LocationExtension after)
    (loans : after.loans = before.loans.set before.nextLoan fresh)
    (permission : Permitted before authority requested address) :
    Permitted after authority requested address ↔ (fresh.live = true →
      authority.LoanCompatible before requested address fresh.referent fresh.mode fresh.guards) :=
  ⟨fun preserved live => permission.fresh_loan_compatible valid loans preserved live,
    fun compatible => permission.fresh_loan valid locations loans compatible⟩

theorem FormsLoan.permitted_iff {purpose : LoanPurpose} {program : RuntimeProgram} {before after : World}
    {authority query : Authority} {mode : Mutability} {region : Identity} {referent destination address : Address}
    {requested : Access} (valid : before.WellFormed)
    (borrowed : FormsLoan program purpose before authority mode region referent destination after)
    (permission : Permitted before query requested address) :
    Permitted after query requested address ↔
      query.LoanCompatible before requested address referent mode (authority.guardLoans before) := by
  have locations := World.LocationExtension.of_locations borrowed.locations
  cases borrowed with
  | borrow _ _ _ _ _ _ _ _ _ _ written =>
      exact permission.fresh_loan_iff valid locations rfl |>.trans (by simp)

theorem FormsLoan.permitted {purpose : LoanPurpose} {program : RuntimeProgram} {before after : World}
    {authority query : Authority} {mode : Mutability} {region : Identity} {referent destination address : Address}
    {requested : Access} (valid : before.WellFormed)
    (borrowed : FormsLoan program purpose before authority mode region referent destination after)
    (permission : Permitted before query requested address)
    (compatible : query.LoanCompatible before requested address referent mode (authority.guardLoans before)) :
    Permitted after query requested address :=
  (borrowed.permitted_iff valid permission).mpr compatible

theorem ClaimsStorage.permitted_iff {custody : ClaimCustody} {before after : World}
    {authority query : Authority} {access requested : Access} {referent address : Address} {created : Identity}
    (valid : before.WellFormed) (claimed : ClaimsStorage custody before authority access referent created after)
    (permission : Permitted before query requested address) :
    Permitted after query requested address ↔
      query.LoanCompatible before requested address referent
        (if access = .shared then .shared else .unique) (authority.guardLoans before) := by
  have locations : before.LocationExtension after := .of_locations (fun _ => by cases claimed; rfl)
  cases claimed with
  | claim _ _ _ =>
      exact permission.fresh_loan_iff valid locations rfl |>.trans (by simp)

theorem ClaimsStorage.permitted {custody : ClaimCustody} {before after : World}
    {authority query : Authority} {access requested : Access} {referent address : Address} {created : Identity}
    (valid : before.WellFormed) (claimed : ClaimsStorage custody before authority access referent created after)
    (permission : Permitted before query requested address)
    (compatible : query.LoanCompatible before requested address referent
      (if access = .shared then .shared else .unique) (authority.guardLoans before)) :
    Permitted after query requested address :=
  (claimed.permitted_iff valid permission).mpr compatible

theorem ClaimsAllocation.permitted_iff {custody : ClaimCustody} {before after : World}
    {authority query : Authority} {requested : Access} {referent address : Address} {created : Identity}
    (valid : before.WellFormed) (claimed : ClaimsAllocation custody before authority referent created after)
    (permission : Permitted before query requested address) :
    Permitted after query requested address ↔
      query.LoanCompatible before requested address referent .unique (authority.guardLoans before) := by
  have locations : before.LocationExtension after := .of_locations (fun _ => by cases claimed; rfl)
  cases claimed with
  | claim _ _ _ =>
      exact permission.fresh_loan_iff valid locations rfl |>.trans (by simp)

theorem ClaimsAllocation.permitted {custody : ClaimCustody} {before after : World}
    {authority query : Authority} {requested : Access} {referent address : Address} {created : Identity}
    (valid : before.WellFormed) (claimed : ClaimsAllocation custody before authority referent created after)
    (permission : Permitted before query requested address)
    (compatible : query.LoanCompatible before requested address referent .unique (authority.guardLoans before)) :
    Permitted after query requested address :=
  (claimed.permitted_iff valid permission).mpr compatible

end Glorious.Language
