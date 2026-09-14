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

/-! ## Resource and custody compatibility of one actual fresh row

`Authority.LoanCompatible` is the permission component of one fresh row's
pre-state compatibility, read at the *incoming* row's referent, mode and guard
list. The components below are stated on the same source world and the same
row: retention of one observed owning claim, retention of custody records,
retention of bindings and of pending availability permissions. Each component
is indexed by the actual observer, and none of them is derived from a
post-state permission or from a conflict-free assumption about other loans. -/

/-- Protection of one observed claim anchor `anchor`: the fresh row must not
enter that claim's own parent chain as a live owning node. Nothing is required
of unrelated owning rows, and no unobserved claim is constrained. Failure of
this criterion is exactly the replacement an actual owning claim performs. -/
def World.ClaimProtected (before : World) (kind : LoanKind) (parent : Option Identity)
    (anchor : Identity) : Prop :=
  kind ≠ .owning ∨ ∀ p, parent = some p → ¬ AncestorLoan before anchor p

/-- A claim is a property of the claimed identity, not of the authority wrapper
that names it; every consumer below reads it through this projection. -/
theorem AllocationClaim.of_loan {world : World} {authority : Authority} {address : Address} {anchor : Identity}
    (atAnchor : authority.parentLoan = some anchor) (claim : AllocationClaim world authority address) :
    AllocationClaim world (.loan anchor) address := by
  obtain ⟨identity,loan,root,domain,atIdentity,found,live,owning,referent,whole,selected,home,latest⟩ := claim
  have equal : identity = anchor := Option.some.inj (atIdentity.symm.trans atAnchor)
  rw [← equal]
  exact ⟨identity,loan,root,domain,rfl,found,live,owning,referent,whole,selected,home,latest⟩

/-- Nothing in the updated table descends from the fresh row: its parent is an
existing identity, and every retained row keeps a parent strictly below itself. -/
theorem World.no_child_of_fresh {before after : World} {fresh : Loan}
    (valid : before.WellFormed) (loans : after.loans = before.loans.set before.nextLoan fresh)
    (parentBound : ∀ identity, fresh.parent = some identity → identity < before.nextLoan) :
    ∀ id loan, after.loans.get id = some loan → loan.parent ≠ some before.nextLoan := by
  intro id loan found same
  by_cases freshKey : id = before.nextLoan
  · subst freshKey
    have equal : loan = fresh := Option.some.inj (found.symm.trans (by rw [loans,Table.get_set]))
    subst equal
    exact Nat.lt_irrefl _ (parentBound before.nextLoan same)
  · have old : before.loans.get id = some loan := by
      simpa only [loans,Table.get_set_other _ _ _ _ freshKey] using found
    obtain ⟨ancestor,atParent,_,_,_,_⟩ := World.loanParents valid id loan before.nextLoan old same
    exact Nat.lt_irrefl _ (World.loanBounds valid atParent)

/-- Nothing descends from the fresh row, so the new owning row is the current
claim of every place it names. -/
theorem AncestorLoan.fresh_leaf {before after : World}
    (leaves : ∀ id loan, after.loans.get id = some loan → loan.parent ≠ some before.nextLoan)
    {ancestor descendant : Identity} (related : AncestorLoan after ancestor descendant)
    (same : ancestor = before.nextLoan) : descendant = before.nextLoan := by
  induction related with
  | refl => exact same
  | @parent p c l f s pr ih =>
      exact False.elim (leaves c l f (s.trans (congrArg some ih)))

/-- The source-world step below any retained identity: a fresh row reached from
an old identity must have been entered through its own parent. -/
theorem AncestorLoan.fresh_step {before after : World} {fresh : Loan}
    (loans : after.loans = before.loans.set before.nextLoan fresh)
    {ancestor descendant : Identity} (related : AncestorLoan after ancestor descendant)
    (freshDesc : descendant = before.nextLoan) (notSelf : ancestor ≠ before.nextLoan) :
    ∃ anchor, fresh.parent = some anchor ∧ AncestorLoan after ancestor anchor := by
  induction related with
  | refl => exact False.elim (notSelf freshDesc)
  | @parent p c l f s pr =>
      have same : _ = fresh := Option.some.inj (f.symm.trans (by rw [freshDesc,loans,Table.get_set]))
      subst same
      exact ⟨p,s,pr⟩

/-- Exact frame of one observed allocation claim under one fresh row. The claim
survives exactly when the new row does not enter its parent chain as a live
owning node; the latest-owner clause is re-established from the source witness
and the new row's own parent, never from a permission fact. -/
theorem AllocationClaim.fresh_loan {before after : World} {fresh : Loan} {authority : Authority} {address : Address}
    {anchor : Identity}
    (valid : before.WellFormed) (locations : before.LocationExtension after)
    (loans : after.loans = before.loans.set before.nextLoan fresh)
    (claim : AllocationClaim before authority address) (atAnchor : authority.parentLoan = some anchor)
    (parentBound : ∀ p, fresh.parent = some p → p < before.nextLoan)
    (protection : before.ClaimProtected fresh.kind fresh.parent anchor) :
    AllocationClaim after authority address := by
  obtain ⟨identity,loan,root,domain,atIdentity,found,live,owning,referent,whole,selected,home,latest⟩ := claim
  obtain ⟨changed,newSelected,same⟩ := locations.root selected
  have homeEq : changed.home = root.home := by simpa only [Root.location] using congrArg Root.home same
  have equal : identity = anchor := Option.some.inj (atIdentity.symm.trans atAnchor)
  refine ⟨identity,loan,changed,domain,atIdentity,World.fresh_loan_retained valid loans found,live,owning,
    referent,whole,newSelected,by simpa only [homeEq] using home,?_⟩
  intro child successor found' live' owning' ancestry
  by_cases freshChild : child = before.nextLoan
  · subst freshChild
    have same : successor = fresh := Option.some.inj (found'.symm.trans (by rw [loans,Table.get_set]))
    subst same
    obtain ⟨carrier,parentEq,prior⟩ :=
      AncestorLoan.fresh_step loans ancestry rfl (Nat.ne_of_lt (World.loanBounds valid found))
    unfold World.ClaimProtected at protection
    rcases protection with notOwning | noAncestor
    · exact False.elim (notOwning owning')
    · exact False.elim (noAncestor carrier parentEq
        (equal ▸ prior.fresh_loan_reflect valid loans (parentBound carrier parentEq)))
  · have old : before.loans.get child = some successor := by
      simpa only [loans,Table.get_set_other _ _ _ _ freshChild] using found'
    exact latest child successor old live' owning'
      (ancestry.fresh_loan_reflect valid loans (World.loanBounds valid old))

/-- Exactly the claims on the fresh row's own parent chain are revoked: the new
owning node replaces its claimant and that claimant's owning ancestors. -/
theorem AllocationClaim.fresh_loan_revoked {before after : World} {fresh : Loan} {identity immediate : Identity}
    {address : Address}
    (valid : before.WellFormed) (loans : after.loans = before.loans.set before.nextLoan fresh)
    (claim : AllocationClaim before (.loan identity) address) (parent : fresh.parent = some immediate)
    (related : AncestorLoan before identity immediate)
    (live : fresh.live = true) (owning : fresh.kind = .owning) :
    ¬ AllocationClaim after (.loan identity) address := by
  intro revoked
  obtain ⟨claimed,_,_,_,atClaimed,_,_,_,_,_,_,_,claimedLatest⟩ := revoked
  have claimedEq : claimed = identity :=
    Option.some.inj (show (some claimed : Option Identity) = some identity from atClaimed.symm)
  obtain ⟨source,loan,_,_,atSource,found,_,_,_,_,_,_,_⟩ := claim
  have sourceEq : source = identity :=
    Option.some.inj (show (some source : Option Identity) = some identity from atSource.symm)
  have retained : ∀ key original, before.loans.get key = some original →
      ∃ current, after.loans.get key = some current ∧ current.parent = original.parent := by
    intro key original selected
    exact ⟨original,World.fresh_loan_retained valid loans selected,rfl⟩
  have next : AncestorLoan after identity before.nextLoan :=
    .parent (by rw [loans,Table.get_set]) parent (related.transport_parents retained)
  have same : before.nextLoan = claimed :=
    claimedLatest before.nextLoan fresh (by rw [loans,Table.get_set]) live owning (claimedEq.symm ▸ next)
  have sourceBound := World.loanBounds valid (sourceEq ▸ found)
  exact (Nat.not_lt_of_ge (Nat.le_of_eq (same.trans claimedEq))) sourceBound

/-- Shared storage access and a fresh shared row never conflict. This is the
admission half of the criterion: shared/shared overlap stays admitted, and an
incoming guard can only freeze an observed query to shared access, which a
shared access already is. -/
theorem Authority.LoanCompatible.shared {before : World} {authority : Authority} {referent : Address}
    {guards : List Identity} : authority.LoanCompatible before .shared referent referent .shared guards := by
  induction authority with
  | owner =>
    exact fun _ conflict => conflict.elim (fun wrong => wrong rfl) (fun unique => by cases unique)
  | loan identity =>
    exact ⟨fun _ conflict => conflict.elim (fun wrong => wrong rfl) (fun unique => by cases unique),
      fun _ => rfl⟩
  | shared backing ih => exact ih
  | guarded backing carrier ih =>
    exact ⟨ih,fun _ _ => ⟨fun _ conflict => conflict.elim (fun wrong => wrong rfl) (fun unique => by cases unique),
      fun _ => rfl⟩⟩

/-- A shared fresh row therefore preserves every shared permission of every
observed query, whatever shape that query's authority has. -/
theorem Permitted.fresh_shared {before after : World} {fresh : Loan} {query : Authority} {address : Address}
    (valid : before.WellFormed) (locations : before.LocationExtension after)
    (loans : after.loans = before.loans.set before.nextLoan fresh)
    (permission : Permitted before query .shared address) (referent : fresh.referent = address)
    (mode : fresh.mode = .shared) : Permitted after query .shared address :=
  permission.fresh_loan valid locations loans (fun _ => by
    rw [referent,mode]
    exact Authority.LoanCompatible.shared)

/-- The frame and its revocation are exact complements: for the observed anchor,
a live fresh owning row revokes the claim if and only if it lies on that
claim's parent chain. -/
theorem AllocationClaim.fresh_loan_iff {before after : World} {fresh : Loan} {authority : Authority}
    {address : Address} {anchor : Identity}
    (valid : before.WellFormed) (locations : before.LocationExtension after)
    (loans : after.loans = before.loans.set before.nextLoan fresh)
    (claim : AllocationClaim before authority address) (atAnchor : authority.parentLoan = some anchor)
    (parentBound : ∀ p, fresh.parent = some p → p < before.nextLoan) (live : fresh.live = true) :
    AllocationClaim after authority address ↔ before.ClaimProtected fresh.kind fresh.parent anchor := by
  refine ⟨fun preserved => ?_,
    fun protection => claim.fresh_loan valid locations loans atAnchor parentBound protection⟩
  by_cases owning : fresh.kind = .owning
  · refine Or.inr (fun parent parentEq related => ?_)
    exact AllocationClaim.fresh_loan_revoked valid loans (AllocationClaim.of_loan atAnchor claim)
      parentEq related live owning (AllocationClaim.of_loan atAnchor preserved)
  · exact Or.inl owning

/-- A fresh owning row becomes the current claim of its own referent: the whole
allocation claim moves to the new identity, whose parent chain is exactly the
claim it replaces. -/
theorem AllocationClaim.fresh_owning {before after : World} {fresh : Loan} {authority : Authority}
    {address : Address}
    (valid : before.WellFormed) (locations : before.LocationExtension after)
    (loans : after.loans = before.loans.set before.nextLoan fresh)
    (claim : AllocationClaim before authority address) (parent : fresh.parent = authority.parentLoan)
    (referent : fresh.referent = address) (live : fresh.live = true) (owning : fresh.kind = .owning) :
    AllocationClaim after (.loan before.nextLoan) address := by
  obtain ⟨identity,loan,root,domain,atIdentity,found,_,_,_,whole,selected,home,_⟩ := claim
  obtain ⟨changed,newSelected,same⟩ := locations.root selected
  have homeEq : changed.home = root.home := by simpa only [Root.location] using congrArg Root.home same
  have parentBound : ∀ p, fresh.parent = some p → p < before.nextLoan := by
    intro p equal
    have same : some p = some identity := by rw [← equal,parent,atIdentity]
    rw [Option.some.inj same]
    exact World.loanBounds valid found
  refine ⟨before.nextLoan,fresh,changed,domain,rfl,by rw [loans,Table.get_set],live,owning,referent,whole,
    newSelected,by simpa only [homeEq] using home,?_⟩
  intro child successor found' live'' owning'' ancestry
  exact AncestorLoan.fresh_leaf (World.no_child_of_fresh valid loans parentBound) ancestry rfl

/-- At most one live owning node is the current allocation claim of one place,
so revocation has a unique successor. -/
theorem AllocationClaim.unique {world : World} (valid : world.WellFormed) {left right : Identity}
    {address : Address}
    (first : AllocationClaim world (.loan left) address) (second : AllocationClaim world (.loan right) address) :
    left = right := by
  obtain ⟨leftId,firstLoan,_,_,atLeft,firstFound,firstLive,firstOwning,firstReferent,_,_,_,firstLatest⟩ := first
  obtain ⟨rightId,rightLoan,_,_,atRight,rightFound,rightLive,rightOwning,rightReferent,_,_,_,secondLatest⟩ := second
  have leftEq : leftId = left := Option.some.inj (show (some leftId : Option Identity) = some left from atLeft.symm)
  have rightEq : rightId = right := Option.some.inj (show (some rightId : Option Identity) = some right from atRight.symm)
  have leftFound : world.loans.get left = some firstLoan := leftEq ▸ firstFound
  have rightFound : world.loans.get right = some rightLoan := rightEq ▸ rightFound
  have overlap : firstLoan.referent.Overlaps rightLoan.referent := by
    rw [firstReferent,rightReferent]
    exact (Address.Prefix.refl address).overlaps
  have unique : firstLoan.mode = .unique :=
    (World.loanKinds valid left firstLoan leftFound).1 firstOwning
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,overlaps,_,_,_⟩ := valid
  rcases overlaps left right firstLoan rightLoan leftFound rightFound firstLive rightLive overlap
    (Or.inl unique) with forward | backward
  · exact (leftEq ▸ firstLatest right rightLoan rightFound rightLive rightOwning
      (leftEq.symm ▸ forward)).symm
  · exact rightEq ▸ secondLatest left firstLoan leftFound firstLive firstOwning (rightEq.symm ▸ backward)

/-- Custody is retired from the actual rows, not from the permission projection:
inserting one fresh row keeps every existing custody record. -/
theorem Authority.Custodied.fresh_loan {before after : World} {fresh : Loan} {authority : Authority}
    {custody : ClaimCustody}
    (valid : before.WellFormed) (loans : after.loans = before.loans.set before.nextLoan fresh)
    (held : authority.Custodied before custody) : authority.Custodied after custody := by
  induction authority with
  | owner => trivial
  | loan identity =>
    obtain ⟨loan,found,condition⟩ := held
    exact ⟨loan,World.fresh_loan_retained valid loans found,condition⟩
  | shared backing ih =>
    show backing.Recorded after.loans
    rw [loans]
    exact held.set _ _
  | guarded backing carrier ih => exact ih held

/-- Source provenance of an authority survives the insertion of a fresh row. -/
theorem Authority.Recorded.fresh_loan {before after : World} {fresh : Loan} {authority : Authority}
    (loans : after.loans = before.loans.set before.nextLoan fresh) (recorded : authority.Recorded before.loans) :
    authority.Recorded after.loans := by
  rw [loans]; exact recorded.set _ _

/-- Fresh loan insertion preserves the inherited dependencies of every
previously recorded authority used to construct a later loan. -/
theorem Authority.guardLoans_fresh_loan {before after : World} {fresh : Loan} {authority : Authority}
    (valid : before.WellFormed) (loans : after.loans = before.loans.set before.nextLoan fresh)
    (recorded : authority.Recorded before.loans) :
    authority.guardLoans after = authority.guardLoans before := by
  induction authority with
  | owner => rfl
  | loan identity =>
    obtain ⟨loan,found⟩ := recorded
    have bound := World.loanBounds valid found
    simp only [Authority.guardLoans,loans,Table.get_set_other _ _ _ _ (Nat.ne_of_lt bound)]
  | shared backing ih => exact ih recorded
  | guarded backing carrier ih =>
    obtain ⟨inner,⟨loan,found⟩⟩ := recorded
    have bound := World.loanBounds valid found
    simp only [Authority.guardLoans,ih inner,loans,Table.get_set_other _ _ _ _ (Nat.ne_of_lt bound)]

/-- Pending permissions are the reserved places of the active availabilities.
Inserting a fresh row keeps every one of them: the availability table is not
part of the transition, and the fresh identity cannot be a reserved authority. -/
theorem World.fresh_loan_reserved {before after : World} {fresh : Loan}
    (valid : before.WellFormed) (availability : after.availability = before.availability)
    (loans : after.loans = before.loans.set before.nextLoan fresh)
    {id : Identity} {available : Availability} (found : after.availability.get id = some available) :
    ∀ place ∈ available.reserved, place.authority.Recorded after.loans := by
  intro place member
  have old : before.availability.get id = some available := by simpa only [availability] using found
  rw [loans]
  exact (World.reserved_authority_recorded valid old member).set _ _

/-- The permission projection of every retained row survives one fresh row:
the one authoritative field an ordered binder fills for a loan-only mutation. -/
theorem World.fresh_loan_permissionState {before after : World} {fresh : Loan}
    (valid : before.WellFormed) (loans : after.loans = before.loans.set before.nextLoan fresh) :
    ∀ identity loan, before.loans.get identity = some loan →
      ∃ current, after.loans.get identity = some current ∧ current.permissionState = loan.permissionState :=
  fun _ _ found => ⟨_,World.fresh_loan_retained valid loans found,rfl⟩

/-- A fresh non-owning row protects every observed claim, so the claim frame is
unconditional for borrow and storage-claim producers. -/
theorem AllocationClaim.fresh_loan_nonowning {before after : World} {fresh : Loan} {authority : Authority}
    {address : Address} {anchor : Identity}
    (valid : before.WellFormed) (locations : before.LocationExtension after)
    (loans : after.loans = before.loans.set before.nextLoan fresh)
    (claim : AllocationClaim before authority address) (atAnchor : authority.parentLoan = some anchor)
    (parentBound : ∀ p, fresh.parent = some p → p < before.nextLoan) (kind : fresh.kind ≠ .owning) :
    AllocationClaim after authority address :=
  claim.fresh_loan valid locations loans atAnchor parentBound (Or.inl kind)

/-- A retained resource binding survives one fresh row: its custody is read from
the actual rows, its observed allocation claim is retained under that claim's
own protection criterion, and a retained storage borrow is the same record. -/
theorem StorageBinding.HeldBy.fresh_loan {before after : World} {fresh : Loan} {owner : Identity}
    {binding : StorageBinding} {anchor : Identity}
    (valid : before.WellFormed) (locations : before.LocationExtension after)
    (loans : after.loans = before.loans.set before.nextLoan fresh)
    (atAnchor : binding.authority.parentLoan = some anchor)
    (parentBound : ∀ p, fresh.parent = some p → p < before.nextLoan)
    (protection : before.ClaimProtected fresh.kind fresh.parent anchor)
    (held : binding.HeldBy before owner) : binding.HeldBy after owner := by
  refine ⟨Authority.Custodied.fresh_loan valid loans held.1,?_⟩
  rcases held.2 with ⟨claim,writable⟩ | storage
  · exact Or.inl ⟨claim.fresh_loan valid locations loans atAnchor parentBound protection,writable⟩
  · obtain ⟨identity,loan,atParent,found,live,kind,referent,shared⟩ := storage
    exact Or.inr ⟨identity,loan,atParent,World.fresh_loan_retained valid loans found,
      live,kind,referent,shared⟩

/-! ## Producer laws

Each actual loan-producing rule inserts one row. These laws pin that row's
referent, mode and guard list (the *incoming* values, never the query's), and
give the claim protection the rule really establishes, so a consumer never
re-derives them from the resulting world. -/

theorem FormsLoan.claim_protected {purpose : LoanPurpose} {program : RuntimeProgram}
    {before after : World} {authority : Authority} {mode : Mutability} {region : Identity}
    {referent handle : Address}
    (borrowed : FormsLoan program purpose before authority mode region referent handle after)
    (anchor : Identity) : before.ClaimProtected purpose.kind authority.parentLoan anchor :=
  Or.inl (by cases purpose <;> decide)

theorem ClaimsStorage.claim_protected {custody : ClaimCustody} {before after : World}
    {authority : Authority} {access : Access} {address : Address} {created : Identity}
    (_claimed : ClaimsStorage custody before authority access address created after)
    (anchor : Identity) : before.ClaimProtected .storageBorrow authority.parentLoan anchor :=
  Or.inl (by decide)

theorem FormsLoan.fresh_row {purpose : LoanPurpose} {program : RuntimeProgram}
    {before after : World} {authority : Authority} {mode : Mutability} {region : Identity}
    {referent handle : Address}
    (borrowed : FormsLoan program purpose before authority mode region referent handle after) :
    after.loans.get before.nextLoan = some
      ⟨before.nextLoan,authority.parentLoan,referent,mode,region,true,purpose.kind,
        authority.guardLoans before,false,none⟩ := by
  cases borrowed with
  | borrow stored referentType initialized regionLive admitted ready permitted vacant destinationType
      parentEq written =>
      rw [parentEq]
      exact Table.get_set _ _ _

theorem ClaimsStorage.fresh_row {custody : ClaimCustody} {before after : World}
    {authority : Authority} {access : Access} {address : Address} {created : Identity}
    (claimed : ClaimsStorage custody before authority access address created after) :
    ∃ (root : Root), after.loans.get before.nextLoan = some
      ⟨before.nextLoan,authority.parentLoan,address,
        (if access = .shared then .shared else .unique),root.region,true,
        .storageBorrow,authority.guardLoans before,false,some custody⟩ := by
  cases claimed with
  | @claim r selected located permitted =>
      exact ⟨r,Table.get_set _ _ _⟩

theorem ClaimsAllocation.fresh_row {custody : ClaimCustody} {before after : World}
    {authority : Authority} {address : Address} {created : Identity}
    (claimed : ClaimsAllocation custody before authority address created after) :
    ∃ (root : Root), after.loans.get before.nextLoan = some
      ⟨before.nextLoan,authority.parentLoan,address,.unique,root.region,true,
        .owning,authority.guardLoans before,false,some custody⟩ := by
  cases claimed with
  | @claim r owning permitted selected =>
      exact ⟨r,Table.get_set _ _ _⟩

/-- An actual owning claim moves the current owner: the fresh identity is the
new claim and the incoming authority no longer is. No post-state permission is
consulted, and no unrelated claim is involved. -/
theorem ClaimsAllocation.claim_replaced {custody : ClaimCustody} {before after : World}
    {authority : Authority} {address : Address} {created : Identity}
    (valid : before.WellFormed) (claimed : ClaimsAllocation custody before authority address created after) :
    ∃ anchor, authority.parentLoan = some anchor ∧
      AllocationClaim after (.loan created) address ∧ ¬ AllocationClaim after authority address := by
  cases claimed with
  | @claim r owning permitted selected =>
    have claim := owning
    obtain ⟨anchor,loan,_,_,atAnchor,found,_,_,_,_,_,_,_⟩ := claim
    have bound : anchor < before.nextLoan := World.loanBounds valid found
    have parentBound : ∀ p, (some anchor : Option Identity) = some p → p < before.nextLoan := by
      intro p same
      rw [(Option.some.inj same).symm]
      exact bound
    refine ⟨anchor,atAnchor,?_⟩
    constructor
    · exact AllocationClaim.fresh_owning valid (World.LocationExtension.of_locations (fun _ => rfl)) rfl
        owning rfl rfl rfl rfl
    · intro preserved
      exact AllocationClaim.fresh_loan_revoked valid rfl (AllocationClaim.of_loan atAnchor owning)
        atAnchor AncestorLoan.refl rfl rfl (AllocationClaim.of_loan atAnchor preserved)

end Glorious.Language
