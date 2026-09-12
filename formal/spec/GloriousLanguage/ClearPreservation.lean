import GloriousLanguage.TransferPreservation

/-! The actual clear/write boundary, shared by value construction and storage cleanup. -/
namespace Glorious.Language

theorem World.clear_resident_origin {before after : World} {address observed : Address} {value : Value}
    (written : before.write address none = some after) (resident : after.Resident observed value) :
    ∃ original, before.Resident observed original ∧ value.shell = original.shell := by
  have stored := World.resident_iff_stores.mp resident
  have outside : ¬ address.Prefix observed := by
    intro included
    obtain ⟨suffix,equal⟩ := Address.prefix_extension included
    have absent := World.write_read_inside written suffix
    rw [← equal,stored] at absent
    cases absent
  have framed := World.write_read_shell written outside
  rw [stored] at framed
  obtain ⟨original,found,same⟩ := Option.map_eq_some_iff.mp framed.symm
  exact ⟨original,World.resident_iff_stores.mpr found,same.symm⟩

/-- Framing a write that retains old resident identities, heads and arities.
The operation-specific origin proof supplies these facts from the actual
write, rather than assuming a well-formed result. -/
theorem World.write_wellFormedWithOrigins_of_origin {before after : World} {address : Address} {authority : Authority}
    {replacement : Option Value} {originBound : Identity}
    (valid : before.WellFormedWithOrigins originBound) (permission : Permitted before authority .owned address)
    (written : before.write address replacement = some after)
    (origin : ∀ observed value, after.Resident observed value → ∃ original,
      before.Resident observed original ∧ value.owner = original.owner ∧ value.head = original.head ∧
        value.fields.length = original.fields.length) : after.WellFormedWithOrigins originBound := by
  have rest := World.write_rest written
  have loansEq := congrArg World.loans rest
  have proofEq := congrArg World.availability rest
  have regionsEq := congrArg World.liveRegions rest
  have rootBound := congrArg World.nextRoot rest
  have ownerBound := congrArg World.nextOwner rest
  have loanBound := congrArg World.nextLoan rest
  have regionBound := congrArg World.nextRegion rest
  have proofBound := congrArg World.nextProof rest
  have locations := World.write_locations written
  have rootsUnique := World.write_unique_roots valid.1 written
  have parents : after.LoanParents := by simpa only [World.LoanParents,loansEq] using World.loanParents valid
  have guards : after.LoanGuards := by simpa only [World.LoanGuards,loansEq] using World.loanGuards valid
  have kinds : after.LoanKinds := by simpa only [World.LoanKinds,loansEq] using World.loanKinds valid
  have located : after.LiveLoanLocations := by
    intro id loan found live
    have selected : before.loans.get id = some loan := by simpa only [loansEq] using found
    exact World.Located.transport locations (fun _ => World.write_read_shell written)
      (permission.owned_no_loan_descendant (World.loanParents valid) selected live)
      (World.liveLoanLocations valid id loan selected live)
  rcases valid with ⟨_,loansUnique,proofsUnique,regionsUnique,proofs,packs,owners,unique,
    roots,regions,bases,ranges,loans,references,overlaps,_,_,_⟩
  refine ⟨rootsUnique,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,parents,located,guards,kinds⟩
  · simpa only [loansEq] using loansUnique
  · simpa only [proofEq] using proofsUnique
  · simpa only [regionsEq] using regionsUnique
  · intro id available found
    have selected : before.availability.get id = some available := by simpa only [proofEq] using found
    obtain ⟨identity,bound,brand,active,recorded⟩ := proofs id available selected
    refine ⟨identity,by simpa only [proofBound] using bound,brand,fun live => ⟨?_,?_⟩,
      by simpa only [loansEq] using recorded⟩
    · simpa only [regionsEq] using (active live).1
    · intro place member
      obtain ⟨root,found⟩ := Option.isSome_iff_exists.mp ((active live).2 place member)
      obtain ⟨_,selected,_⟩ := World.root_transport locations found
      simp [selected]
  · intro observed value pack resident head
    obtain ⟨original,found,_,headEq,arity⟩ := origin observed value resident
    simpa only [proofBound,regionsEq,arity] using packs observed original pack found (headEq.symm.trans head)
  · intro observed value resident
    obtain ⟨original,found,owner,_,_⟩ := origin observed value resident
    simpa only [ownerBound,owner] using owners observed original found
  · intro a b x y first second same
    obtain ⟨left,leftFound,leftOwner,_,_⟩ := origin a x first
    obtain ⟨right,rightFound,rightOwner,_,_⟩ := origin b y second
    exact unique a b left right leftFound rightFound (leftOwner.symm.trans (same.trans rightOwner))
  · intro id root found
    obtain ⟨original,selected,same⟩ := World.root_origin locations found
    rw [same]
    simpa only [rootBound,regionsEq] using roots id original selected
  · simpa only [regionsEq,regionBound] using regions
  · intro id root found live
    obtain ⟨original,selected,same⟩ := World.root_origin locations found
    have originalLive : original.live = true := by rw [same] at live; exact live
    rw [same]
    exact bases id original selected originalLive
  · intro a b left right first second different leftLive rightLive
    obtain ⟨oldLeft,leftFound,leftEq⟩ := World.root_origin locations first
    obtain ⟨oldRight,rightFound,rightEq⟩ := World.root_origin locations second
    have originalLeft : oldLeft.live = true := by rw [leftEq] at leftLive; exact leftLive
    have originalRight : oldRight.live = true := by rw [rightEq] at rightLive; exact rightLive
    rw [leftEq,rightEq]
    exact ranges a b oldLeft oldRight leftFound rightFound different originalLeft originalRight
  · intro id loan found
    have selected : before.loans.get id = some loan := by simpa only [loansEq] using found
    obtain ⟨identity,bound,active⟩ := loans id loan selected
    refine ⟨identity,by simpa only [loanBound] using bound,fun live => ⟨?_,?_⟩⟩
    · simpa only [regionsEq] using (active live).1
    · obtain ⟨_,found⟩ := Option.isSome_iff_exists.mp (active live).2
      obtain ⟨_,selected,_⟩ := World.root_transport locations found
      simp [selected]
  · intro observed value id resident head
    obtain ⟨original,found,_,headEq,_⟩ := origin observed value resident
    obtain ⟨loan,selected,live⟩ := references observed original id found (headEq.symm.trans head)
    exact ⟨loan,by simpa only [loansEq] using selected,live⟩
  · intro a b left right first second leftLive rightLive overlap unique
    have leftFound : before.loans.get a = some left := by simpa only [loansEq] using first
    have rightFound : before.loans.get b = some right := by simpa only [loansEq] using second
    exact (overlaps a b left right leftFound rightFound leftLive rightLive overlap unique).imp
      (AncestorLoan.transport (before := before) loansEq) (AncestorLoan.transport (before := before) loansEq)

theorem World.write_wellFormed_of_origin {before after : World} {address : Address} {authority : Authority}
    {replacement : Option Value}
    (valid : before.WellFormed) (permission : Permitted before authority .owned address)
    (written : before.write address replacement = some after)
    (origin : ∀ observed value, after.Resident observed value → ∃ original,
      before.Resident observed original ∧ value.owner = original.owner ∧ value.head = original.head ∧
        value.fields.length = original.fields.length) : after.WellFormed := by
  have checked := World.write_wellFormedWithOrigins_of_origin valid permission written origin
  simpa only [World.WellFormed,congrArg World.nextOwner (World.write_rest written)] using checked

theorem World.clear_wellFormedWithOrigins {before after : World} {address : Address} {authority : Authority}
    {originBound : Identity} (valid : before.WellFormedWithOrigins originBound)
    (permission : Permitted before authority .owned address)
    (written : before.write address none = some after) : after.WellFormedWithOrigins originBound := by
  apply World.write_wellFormedWithOrigins_of_origin valid permission written
  intro observed value resident
  obtain ⟨original,found,shell⟩ := World.clear_resident_origin written resident
  refine ⟨original,found,?_,?_,?_⟩
  · simpa [Value.shell,Value.withFields,Value.owner] using congrArg Value.owner shell
  · simpa [Value.shell,Value.withFields,Value.head] using congrArg Value.head shell
  · simpa [Value.shell,Value.withFields,Value.fields] using congrArg (fun value => value.fields.length) shell

theorem World.clear_wellFormed {before after : World} {address : Address} {authority : Authority}
    (valid : before.WellFormed) (permission : Permitted before authority .owned address)
    (written : before.write address none = some after) : after.WellFormed := by
  have checked := World.clear_wellFormedWithOrigins valid permission written
  simpa only [World.WellFormed,congrArg World.nextOwner (World.write_rest written)] using checked

theorem World.clear_worldTypedWithOrigins {program : Kernel.Program} {before after : World}
    {address : Address} {authority : Authority} {originBound : Identity}
    (typed : Typing.WorldTypedWithOrigins program before originBound)
    (permission : Permitted before authority .owned address) (written : before.write address none = some after) :
    Typing.WorldTypedWithOrigins program after originBound := by
  have roots := World.clear_typed_roots typed.roots written
  have rest := World.write_rest written
  have loansEq := congrArg World.loans rest
  have proofEq := congrArg World.availability rest
  refine ⟨World.clear_wellFormedWithOrigins typed.1 permission written,?_,?_,?_⟩
  · intro observed value resident
    have checked := World.stores_typed roots (World.resident_iff_stores.mp resident)
    apply checked.transport ?_ proofEq (fun _ origin => origin.transport (World.write_locations written))
    intro id loan found live
    exact ⟨by simpa only [loansEq] using found,fun _ type =>
      (World.write_address_types written (permission.owned_no_loan_descendant (World.loanParents typed.1) found live)).mp type⟩
  · intro id root value found contents
    by_cases live : root.live = true
    · exact (roots id root value found live contents).2
    · exact typed.2.2.1 id root value (World.write_dead_root written found live) contents
  · apply World.root_regions_transport typed.2.2.2 (World.write_locations written)
    have same := congrArg World.nextRegion rest
    exact Nat.le_of_eq same.symm

theorem World.clear_worldTyped {program : Kernel.Program} {before after : World}
    {address : Address} {authority : Authority} (typed : Typing.WorldTyped program before)
    (permission : Permitted before authority .owned address) (written : before.write address none = some after) :
    Typing.WorldTyped program after := by
  have checked := World.clear_worldTypedWithOrigins typed permission written
  simpa only [Typing.WorldTyped,congrArg World.nextOwner (World.write_rest written)] using checked

end Glorious.Language
