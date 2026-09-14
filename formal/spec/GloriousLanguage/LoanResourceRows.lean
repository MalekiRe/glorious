import GloriousLanguage.LoanCompatibility
import GloriousLanguage.ReferenceTransferPreservation
import GloriousLanguage.Preservation

/-! ## Producer rows

Every actual resource mutation supplies its row laws on the real loan table,
below the reachable graph. A fresh non-owning row keeps every retained row,
every claim and every custody record; a whole-place custody transfer moves
exactly one custodian and names its recipient; an owning claim replaces the
claim it enters. Consumers read these laws through `World.ResourceRowsRetained`
and `Value.BatchCompatible.of_rows`, never through the resulting world. -/
namespace Glorious.Language

/-- A real permission names only identities already present in the source loan
table, so the parent link a rule records for its fresh row stays inside the
source bound. This replaces any premise about the world after the insertion. -/
theorem Permitted.parentLoan_bound {world : World} {authority : Authority} {requested : Access} {address : Address}
    (valid : world.WellFormed) (permission : Permitted world authority requested address) :
    ∀ id, authority.parentLoan = some id → id < world.nextLoan := by
  induction authority with
  | owner => intro id parent; cases parent
  | loan identity =>
      intro id parent
      have equal : identity = id := Option.some.inj parent
      obtain ⟨active,found,_,_,_,_,_,_,_,_⟩ := permission.2
      exact equal ▸ World.loanBounds valid found
  | shared backing ih => exact ih permission.2.2
  | guarded backing carrier ih => exact ih permission.2.1

theorem LoanPurpose.kind_ne_owning (purpose : LoanPurpose) : purpose.kind ≠ .owning := by
  cases purpose <;> decide

theorem LoanKind.storageBorrow_ne_owning : LoanKind.storageBorrow ≠ .owning := by decide

/-- The claim frame of one fresh non-owning row, stated without naming the
claim's own anchor: a claim is read through its own witness, never through a
caller-chosen parent. -/
theorem AllocationClaim.fresh_loan_of_nonowning {before after : World} {fresh : Loan} {authority : Authority}
    {address : Address}
    (valid : before.WellFormed) (locations : before.LocationExtension after)
    (loans : after.loans = before.loans.set before.nextLoan fresh) (claim : AllocationClaim before authority address)
    (parentBound : ∀ p, fresh.parent = some p → p < before.nextLoan) (kind : fresh.kind ≠ .owning) :
    AllocationClaim after authority address := by
  obtain ⟨anchor,loan,root,domain,atAnchor,found,live,owning,referent,whole,selected,home,latest⟩ := claim
  exact AllocationClaim.fresh_loan_nonowning valid locations loans
    ⟨anchor,loan,root,domain,atAnchor,found,live,owning,referent,whole,selected,home,latest⟩
    atAnchor parentBound kind

/-- Rules that leave the loan table alone supply the whole row package. -/
theorem World.ResourceRowsRetained.of_loans {before after : World}
    (locations : before.LocationExtension after) (loans : after.loans = before.loans) :
    before.ResourceRowsRetained after :=
  ⟨fun _ _ found => ⟨_,by rw [loans]; exact found,rfl⟩,
   fun _ _ claim => claim.frame locations loans,
   fun _ _ held => held.same_loans loans⟩

theorem World.ResourceRowsRetained.refl (world : World) : world.ResourceRowsRetained world :=
  World.ResourceRowsRetained.of_loans (.refl world) rfl

/-- One actual fresh non-owning row keeps every retained row, every claim and
every custody record. The incoming parent link is bounded by the source
permission that admitted the rule. -/
theorem World.ResourceRowsRetained.of_fresh_loan {before after : World} {fresh : Loan}
    (valid : before.WellFormed) (locations : before.LocationExtension after)
    (loans : after.loans = before.loans.set before.nextLoan fresh)
    (parentBound : ∀ p, fresh.parent = some p → p < before.nextLoan) (kind : fresh.kind ≠ .owning) :
    before.ResourceRowsRetained after :=
  ⟨World.fresh_loan_permissionState valid loans,
   fun _ _ claim => AllocationClaim.fresh_loan_of_nonowning valid locations loans claim parentBound kind,
   fun _ _ held => Authority.Custodied.fresh_loan valid loans held⟩

theorem FormsLoan.resourceRowsRetained {purpose : LoanPurpose} {program : RuntimeProgram}
    {before after : World} {authority : Authority} {mode : Mutability} {region : Identity}
    {referent destination : Address} (valid : before.WellFormed)
    (borrowed : FormsLoan program purpose before authority mode region referent destination after) :
    before.ResourceRowsRetained after := by
  cases borrowed with
  | borrow stored referentType initialized regionLive admitted ready permitted vacant destinationType
      parentEq written =>
      rw [parentEq]
      exact World.ResourceRowsRetained.of_fresh_loan (fresh :=
          ⟨before.nextLoan,authority.parentLoan,referent,mode,region,true,purpose.kind,
            authority.guardLoans before,false,none⟩) valid
        (.of_locations (fun id => World.write_locations written id)) rfl
        (Permitted.parentLoan_bound valid permitted) (LoanPurpose.kind_ne_owning purpose)

theorem ClaimsStorage.resourceRowsRetained {custody : ClaimCustody} {before after : World}
    {authority : Authority} {access : Access} {address : Address} {created : Identity}
    (valid : before.WellFormed)
    (claimed : ClaimsStorage custody before authority access address created after) :
    before.ResourceRowsRetained after := by
  cases claimed with
  | @claim root selected located permitted =>
      exact World.ResourceRowsRetained.of_fresh_loan (fresh :=
          ⟨before.nextLoan,authority.parentLoan,address,
            (if access = .shared then .shared else .unique),root.region,true,.storageBorrow,
            authority.guardLoans before,false,some custody⟩) valid
        (.of_locations (fun _ => rfl)) rfl
        (Permitted.parentLoan_bound valid permitted) LoanKind.storageBorrow_ne_owning

/-- An actual owning claim inserts a live owning node, so it cannot retain every
claim. It still keeps every retained row and every custody record, and it
replaces exactly the claim it enters (`ClaimsAllocation.claim_replaced`). -/
theorem ClaimsAllocation.retained_rows {custody : ClaimCustody} {before after : World}
    {authority : Authority} {address : Address} {created : Identity}
    (valid : before.WellFormed) (claimed : ClaimsAllocation custody before authority address created after) :
    (∀ identity loan, before.loans.get identity = some loan →
      ∃ current, after.loans.get identity = some current ∧ current.permissionState = loan.permissionState) ∧
    (∀ (observed : Authority) (heldCustody : ClaimCustody),
      observed.Custodied before heldCustody → observed.Custodied after heldCustody) := by
  cases claimed with
  | @claim root owning permitted selected =>
      refine ⟨?_,?_⟩
      · exact World.fresh_loan_permissionState (fresh :=
          ⟨before.nextLoan,authority.parentLoan,address,.unique,root.region,true,.owning,
            authority.guardLoans before,false,some custody⟩) valid rfl
      · intro observed heldCustody held
        exact Authority.Custodied.fresh_loan (fresh :=
          ⟨before.nextLoan,authority.parentLoan,address,.unique,root.region,true,.owning,
            authority.guardLoans before,false,some custody⟩) valid rfl held

/-- A rule that changes values inside existing roots and adds no loan keeps the
whole row package; the root locations are retained by the write. -/
theorem Transfers.resourceRowsRetained {program : RuntimeProgram} {before after : World}
    {authority : Authority} {source destination : Address}
    (transfer : Transfers program before authority source destination after) :
    before.ResourceRowsRetained after :=
  World.ResourceRowsRetained.of_loans (.of_locations transfer.locations) transfer.loans

theorem Allocates.resourceRowsRetained {program : Program} {before after : World}
    {home region type layout mutable address} {originBound : Identity}
    (valid : before.WellFormedWithOrigins originBound)
    (allocated : Allocates program before home region type layout mutable address after) :
    before.ResourceRowsRetained after :=
  World.ResourceRowsRetained.of_loans (allocated.locationExtension valid) allocated.loans

/-- One real whole-place custody transfer of a single recorded row: the row keeps
its permission projection and its guards, every claim survives, custody is
retained by every observer that does not name the moved row, and the recipient
is the new custodian. The old owner's custody is genuinely gone; that absence
is the transfer itself, never a framing gap. -/
structure CustodyTransferRow (before after : World) (identity : Identity) (recipient : ClaimCustody)
    (original : Loan) : Prop where
  found : before.loans.get identity = some original
  rows : after.loans = before.loans.set identity { original with custody := some recipient }
  retained : ∀ (authority : Authority) (custody : ClaimCustody), authority.Custodied before custody →
    (authority.parentLoan ≠ some identity ∨ recipient = custody) → authority.Custodied after custody
  recipientHolds : (Authority.loan identity).Custodied after recipient
  claims : ∀ (authority : Authority) (address : Address),
    AllocationClaim before authority address → AllocationClaim after authority address

theorem TransfersAllocation.rowCustodyTransferred {recipient : ClaimCustody} {before after : World}
    {place : ResolvedPlace} (moved : TransfersAllocation recipient before place after) :
    ∃ identity original, CustodyTransferRow before after identity recipient original := by
  cases moved with
  | @transfer identity loan atPlace claim found =>
      refine ⟨identity,loan,found,rfl,?_,?_,?_⟩
      · intro authority custody held keep
        refine Authority.Custodied.of_custody_update (before := before) (identity := identity)
          (original := loan) (newCustody := recipient) (requested := loan.returnRequested) rfl ?_ held
        rcases keep with keep | keep
        · exact Or.inl keep
        · exact Or.inr (Or.inr (Or.inr keep))
      · exact ⟨{ loan with custody := some recipient },Table.get_set _ _ _,Or.inr (Or.inr rfl)⟩
      · intro authority address claim
        exact AllocationClaim.of_custody_update (before := before) (identity := identity) (original := loan)
          (newCustody := recipient) (requested := loan.returnRequested)
          (.of_locations (fun _ => rfl)) found rfl claim

theorem TransfersStorageLoan.rows {recipient : ClaimCustody} {before after : World}
    {place : ResolvedPlace} (moved : TransfersStorageLoan recipient before place after) :
    after = before ∨ ∃ identity original, CustodyTransferRow before after identity recipient original := by
  cases moved with
  | @unique identity loan atPlace found live kind mode referent =>
      refine Or.inr ⟨identity,loan,found,rfl,?_,?_,?_⟩
      · intro authority custody held keep
        refine Authority.Custodied.of_custody_update (before := before) (identity := identity)
          (original := loan) (newCustody := recipient) (requested := loan.returnRequested) rfl ?_ held
        rcases keep with keep | keep
        · exact Or.inl keep
        · exact Or.inr (Or.inr (Or.inr keep))
      · exact ⟨{ loan with custody := some recipient },Table.get_set _ _ _,Or.inr (Or.inr rfl)⟩
      · intro authority address claim
        exact AllocationClaim.of_custody_update (before := before) (identity := identity) (original := loan)
          (newCustody := recipient) (requested := loan.returnRequested)
          (.of_locations (fun _ => rfl)) found rfl claim
  | @shared backing identity loan atPlace parent found live kind mode referent =>
      exact Or.inl rfl

/-- The custody effect of an invocation input: original rows remain exact
except for transfer to its recipient. A different custody receives no new
rows and no rewritten row. This composes the real row producers below. -/
structure World.CustodyTransferFrame (before after : World) (recipient : ClaimCustody) : Prop where
  rows : ∀ id loan, before.loans.get id = some loan →
    ∃ current, after.loans.get id = some current ∧ (current = loan ∨ current = { loan with custody := some recipient })
  outside : ∀ id loan custody, recipient ≠ custody → after.loans.get id = some loan →
    loan.custody = some custody → before.loans.get id = some loan

theorem World.CustodyTransferFrame.of_loans {before after : World} {recipient : ClaimCustody}
    (loans : after.loans = before.loans) : before.CustodyTransferFrame after recipient :=
  ⟨fun _ loan found => ⟨loan,by simpa only [loans] using found,Or.inl rfl⟩,
    fun _ _ _ _ found _ => by simpa only [loans] using found⟩

theorem World.CustodyTransferFrame.trans {before middle after : World} {recipient : ClaimCustody}
    (first : before.CustodyTransferFrame middle recipient) (last : middle.CustodyTransferFrame after recipient) :
    before.CustodyTransferFrame after recipient := by
  refine ⟨?_,fun id loan custody different found held =>
    first.outside id loan custody different (last.outside id loan custody different found held) held⟩
  intro id loan found
  obtain ⟨current,selected,change⟩ := first.rows id loan found
  obtain ⟨final,atFinal,ending⟩ := last.rows id current selected
  refine ⟨final,atFinal,?_⟩
  rcases change with rfl | rfl <;> rcases ending with rfl | rfl
  · exact Or.inl rfl
  all_goals exact Or.inr rfl

/-- Reference formation has no raw custodian; fresh raw claims belong only to
the actual recipient. The original frontier proves that neither replaces a row. -/
theorem World.CustodyTransferFrame.of_fresh {before after : World} {recipient : ClaimCustody} {inserted : Loan}
    (valid : before.WellFormed) (rows : after.loans = before.loans.set before.nextLoan inserted)
    (custody : inserted.custody = none ∨ inserted.custody = some recipient) :
    before.CustodyTransferFrame after recipient := by
  refine ⟨?_,?_⟩
  · intro id loan found
    exact ⟨loan,by rw [rows,Table.get_set_other _ _ _ _ (Nat.ne_of_lt (World.loanBounds valid found))]; exact found,Or.inl rfl⟩
  · intro id loan other different found held
    by_cases same : id = before.nextLoan
    · subst id
      have equal : inserted = loan := by simpa only [rows,Table.get_set,Option.some.injEq] using found
      subst loan
      rcases custody with absent | received
      · rw [absent] at held; cases held
      · exact False.elim (different (Option.some.inj (received.symm.trans held)))
    · simpa only [rows,Table.get_set_other _ _ _ _ same] using found

theorem CustodyTransferRow.frame {before after : World} {identity : Identity} {recipient : ClaimCustody} {original : Loan}
    (transfer : CustodyTransferRow before after identity recipient original) : before.CustodyTransferFrame after recipient := by
  refine ⟨?_,?_⟩
  · intro id loan found
    by_cases same : id = identity
    · subst id
      have equal : loan = original := Option.some.inj (found.symm.trans transfer.found)
      subst loan
      exact ⟨_,by rw [transfer.rows]; exact Table.get_set _ _ _,Or.inr rfl⟩
    · exact ⟨loan,by rw [transfer.rows,Table.get_set_other _ _ _ _ same]; exact found,Or.inl rfl⟩
  · intro id loan other different found held
    by_cases same : id = identity
    · subst id
      have equal : { original with custody := some recipient } = loan := by
        simpa only [transfer.rows,Table.get_set,Option.some.injEq] using found
      subst loan
      exact False.elim (different (Option.some.inj held))
    · simpa only [transfer.rows,Table.get_set_other _ _ _ _ same] using found


theorem World.CustodyTransferFrame.retained {before after : World} {recipient : ClaimCustody} {identity : Identity} {loan : Loan}
    (frame : before.CustodyTransferFrame after recipient) (found : before.loans.get identity = some loan) :
    ∃ current, after.loans.get identity = some current ∧ current.permissionState = loan.permissionState := by
  obtain ⟨current,selected,change⟩ := frame.rows identity loan found
  refine ⟨current,selected,?_⟩
  rcases change with rfl | rfl <;> rfl

/-- An original recorded parent chain cannot gain an ancestor when entry adds
fresh descendants or transfers custody. The source parent graph supplies the
recursive row witnesses; no arbitrary post-world ancestry is trusted. -/
theorem World.CustodyTransferFrame.ancestor_before {before after : World} {recipient : ClaimCustody}
    {ancestor descendant : Identity} (frame : before.CustodyTransferFrame after recipient)
    (parents : before.LoanParents) (known : ∃ loan, before.loans.get descendant = some loan)
    (related : AncestorLoan after ancestor descendant) : AncestorLoan before ancestor descendant := by
  induction related with
  | refl => exact .refl
  | @parent parent child loan found assigned _ ih =>
      obtain ⟨original,selected⟩ := known
      obtain ⟨current,currentAt,shape⟩ := frame.retained selected
      have equal : current = loan := Option.some.inj (currentAt.symm.trans found)
      have parentEq := congrArg Loan.parent shape
      change current.parent = original.parent at parentEq
      have originalParent : original.parent = some parent := parentEq.symm.trans ((congrArg Loan.parent equal).trans assigned)
      obtain ⟨parentLoan,parentAt,_⟩ := parents child original parent selected originalParent
      exact .parent selected originalParent (ih ⟨parentLoan,parentAt⟩)


theorem World.CustodyTransferFrame.recorded {before after : World} {recipient : ClaimCustody} {authority : Authority}
    (frame : before.CustodyTransferFrame after recipient) (recorded : authority.Recorded before.loans) :
    authority.Recorded after.loans :=
  recorded.transport (fun identity loan found =>
    let ⟨current,selected,_⟩ := frame.rows identity loan found
    ⟨current,selected⟩)

theorem TransfersAllocation.roots_eq {recipient : ClaimCustody} {before after : World}
    {place : ResolvedPlace} (moved : TransfersAllocation recipient before place after) :
    after.roots = before.roots := by cases moved; rfl

theorem TransfersStorageLoan.roots_eq {recipient : ClaimCustody} {before after : World}
    {place : ResolvedPlace} (moved : TransfersStorageLoan recipient before place after) :
    after.roots = before.roots := by cases moved <;> rfl

end Glorious.Language
