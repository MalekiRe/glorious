import GloriousLanguage.PointerPreservation

/-! General preservation through storage retirement, loan release and region
closure. These are the actual teardown relations used by cleanup and
cancellation; no well-formed or typed post-state is an admission premise. -/
namespace Glorious.Language

theorem World.Resident.field {world : World} {address : Address} {value child : Value}
    (resident : world.Resident address value) (member : some child ∈ value.fields) :
    ∃ nested, world.Resident nested child := by
  obtain ⟨index,bound,found⟩ := List.mem_iff_getElem.mp member
  refine ⟨address.child index,World.resident_iff_stores.mpr ?_⟩
  change world.read { address with fields := address.fields ++ [index] } = some child
  rw [World.read_append,World.resident_iff_stores.mp resident]
  simp [Value.atPath,List.getElem?_eq_getElem bound,found]

theorem AddressOffset.retained {program : Program} {before after : World}
    {address : Address} {type : Term} {offset : Nat}
    (typed : AddressOffset program before address type offset)
    (roots : ∀ root, before.roots.get address.root = some root → after.roots.get address.root = some root)
    (reads : ∀ observed, after.read observed = before.read observed) :
    AddressOffset program after address type offset := by
  induction typed with
  | root found live => exact .root (roots _ found) live
  | child _ field ih => exact .child (ih roots) (field.transport (by rw [reads]))

theorem AddressType.retained {program : Program} {before after : World} {address : Address} {type : Term}
    (typed : AddressType program before address type)
    (roots : ∀ root, before.roots.get address.root = some root → after.roots.get address.root = some root)
    (reads : ∀ observed, after.read observed = before.read observed) :
    AddressType program after address type := by
  obtain ⟨offset,typed⟩ := typed
  exact ⟨offset,typed.retained roots reads⟩

/-- Only resident reference handles need survive loan release. Arbitrary
nonresident typed values may name the loan being ended and cannot be framed. -/
theorem Typing.ValueTyped.resident_transport {program : Kernel.Program} {before after : World}
    {value : Value} (typed : Typing.ValueTyped program before value)
    (references : ∀ id loan, before.References id → before.loans.get id = some loan → loan.live = true →
      after.loans.get id = some loan ∧ ∀ type, AddressType program.declarations before loan.referent type →
        AddressType program.declarations after loan.referent type)
    (proofs : after.availability = before.availability)
    (pointers : ∀ pointer : RawPointer, pointer.Origin before → pointer.Origin after)
    (resident : ∃ address, before.Resident address value) : Typing.ValueTyped program after value := by
  refine Typing.ValueTyped.rec
    (motive_1 := fun value _ => (∃ address, before.Resident address value) → Typing.ValueTyped program after value)
    (motive_2 := fun fields types _ =>
      (∀ value, some value ∈ fields → ∃ address, before.Resident address value) → Typing.FieldsTyped program after fields types)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed resident
  · exact fun {_ _} _ => .unit
  · exact fun {_ _ _} valid _ => .scalar valid
  · intro owner type head live fields types shape _ ih ⟨address,resident⟩
    exact .aggregate shape (ih (fun _ member => resident.field member))
  · intro owner mode region type id loan live found active modeEq regionEq located ⟨address,resident⟩
    obtain ⟨selected,types⟩ := references id loan ⟨address,_,resident,rfl⟩ found active
    exact .reference selected active modeEq regionEq (types type located)
  · exact fun {_ _ _ _ _} bound origin _ => .pointer bound (pointers _ origin)
  · intro owner id arguments live fields function selected _ ih ⟨address,resident⟩
    exact .callable selected (ih (fun _ member => resident.field member))
  · exact fun {_ _ _ _ _ _} selected _ => .operation selected
  · exact fun {_ _ _ _ _} _ => .label
  · exact fun {_ _ _ _} type _ => .continuation type
  · exact fun {_ _ _ _ _ _ _} found brand id region residents _ =>
      .available (by simpa [proofs] using found) brand id region residents
  · intro owner brand region live fields types pack _ brandEq regionEq length distinct ih ⟨address,resident⟩
    exact .bindings (ih (fun _ member => resident.field member)) brandEq regionEq length distinct
  · exact fun _ => .nil
  · exact fun {_ _ _} _ ih residents => .hole (ih (fun _ member => residents _ (List.mem_cons_of_mem _ member)))
  · intro value fields type types _ same _ ih tail residents
    exact .resident (ih (residents _ (by simp))) same (tail (fun _ member => residents _ (List.mem_cons_of_mem _ member)))

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
  have located : after.LiveLoanLocations := by
    intro id loan found live
    have selected : before.loans.get id = some loan := by simpa only [loansEq] using found
    exact World.Located.transport locations (fun _ => World.write_read_shell written)
      (permission.owned_no_loan_descendant (World.loanParents valid) selected live)
      (World.liveLoanLocations valid id loan selected live)
  rcases valid with ⟨_,loansUnique,proofsUnique,regionsUnique,proofs,packs,owners,unique,
    roots,regions,bases,ranges,loans,references,overlaps,_,_⟩
  refine ⟨rootsUnique,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,parents,located⟩
  · simpa only [loansEq] using loansUnique
  · simpa only [proofEq] using proofsUnique
  · simpa only [regionsEq] using regionsUnique
  · intro id available found
    have selected : before.availability.get id = some available := by simpa only [proofEq] using found
    obtain ⟨identity,bound,brand,active⟩ := proofs id available selected
    refine ⟨identity,by simpa only [proofBound] using bound,brand,fun live => ⟨?_,?_⟩⟩
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
    apply checked.transport ?_ proofEq (fun _ origin => origin.write written)
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

theorem Retires.roots_other {before after : World} {id : Identity}
    (retired : Retires before id after) {other : Identity} (different : other ≠ id) :
    after.roots.get other = before.roots.get other := by
  cases retired
  exact Table.get_set_other _ _ _ _ different

theorem Retires.live_root {before after : World} {id other : Identity} {root : Root}
    (retired : Retires before id after) (found : after.roots.get other = some root) (live : root.live = true) :
    before.roots.get other = some root := by
  cases retired with
  | vacant _ _ _ _ =>
      by_cases same : other = id
      · subst other
        simp only [Table.get_set] at found
        cases found
        cases live
      · simpa only [Table.get_set_other _ _ _ _ same] using found

theorem Retires.read {before after : World} {id : Identity} (retired : Retires before id after)
    (address : Address) : after.read address = before.read address := by
  cases retired with
  | @vacant root selected live empty _ =>
      by_cases same : address.root = id
      · by_cases generation : root.generation = address.generation <;>
          simp [World.read,World.root,same,Table.get_set,selected,live,empty,generation]
      · simp only [World.read,World.root,Table.get_set_other _ _ _ _ same]

theorem Retires.resident {before after : World} {id : Identity} (retired : Retires before id after)
    {address : Address} {value : Value} : after.Resident address value ↔ before.Resident address value := by
  simp only [World.resident_iff_stores,World.Stores,retired.read]

theorem Retires.root_other {before after : World} {id : Identity} (retired : Retires before id after)
    {address : Address} (different : address.root ≠ id) : after.root address = before.root address := by
  simp only [World.root,retired.roots_other different]

theorem Retires.located {before after : World} {id : Identity} (retired : Retires before id after)
    {address : Address} (different : address.root ≠ id) (located : before.Located address) : after.Located address := by
  rcases located with ⟨value,stored⟩ | ⟨root,found,vacant⟩
  · exact Or.inl ⟨value,by simpa only [World.Stores,retired.read] using stored⟩
  · exact Or.inr ⟨root,by simpa only [retired.root_other different] using found,vacant⟩

theorem Retires.wellFormed {before after : World} {id : Identity}
    (valid : before.WellFormed) (retired : Retires before id after) : after.WellFormed := by
  have residents := fun {address value} => (retired.resident (address := address) (value := value)).mp
  have liveRoots := fun {other root} => retired.live_root (other := other) (root := root)
  have rootFrame := fun {address} => retired.root_other (address := address)
  have locations := fun {address} => retired.located (address := address)
  cases retired with
  | vacant selected _ _ safe =>
      rcases valid with ⟨rootUnique,loanUnique,proofUnique,regionUnique,proofs,packs,owners,ownerUnique,
        roots,regions,bases,ranges,loans,references,overlaps,parents,located⟩
      refine ⟨rootUnique.set _ _,loanUnique,proofUnique,regionUnique,?_,?_,?_,?_,?_,regions,?_,?_,?_,?_,?_,parents,?_⟩
      · intro key available found
        obtain ⟨identity,bound,brand,active⟩ := proofs key available found
        refine ⟨identity,bound,brand,fun live => ⟨(active live).1,?_⟩⟩
        intro place member
        simpa only [rootFrame (safe.2 key available found live place member)] using (active live).2 place member
      · exact fun address value pack resident head => packs address value pack (residents resident) head
      · exact fun address value resident => owners address value (residents resident)
      · exact fun a b x y first second same => ownerUnique a b x y (residents first) (residents second) same
      · intro key root found
        by_cases same : key = id
        · subst key
          simp only [Table.get_set] at found
          cases found
          obtain ⟨bound,_,layout,bytes,bounds⟩ := roots id _ selected
          exact ⟨bound,by simp,layout,bytes,bounds⟩
        · exact roots key root (by simpa only [Table.get_set_other _ _ _ _ same] using found)
      · exact fun key root found live => bases key root (liveRoots found live) live
      · exact fun a b left right first second different leftLive rightLive =>
          ranges a b left right (liveRoots first leftLive) (liveRoots second rightLive) different leftLive rightLive
      · intro key loan found
        obtain ⟨identity,bound,active⟩ := loans key loan found
        refine ⟨identity,bound,fun live => ⟨(active live).1,?_⟩⟩
        simpa only [rootFrame (safe.1 key loan found live)] using (active live).2
      · exact fun address value key resident head => references address value key (residents resident) head
      · intro a b left right first second leftLive rightLive overlap unique
        rcases overlaps a b left right first second leftLive rightLive overlap unique with ancestry | ancestry
        · exact Or.inl (ancestry.transport (before := before) (by rfl))
        · exact Or.inr (ancestry.transport (before := before) (by rfl))
      · exact fun key loan found live => locations (safe.1 key loan found live) (located key loan found live)

theorem Retires.worldTyped {program : Kernel.Program} {before after : World} {id : Identity}
    (typed : Typing.WorldTyped program before) (retired : Retires before id after) : Typing.WorldTyped program after := by
  refine ⟨retired.wellFormed typed.1,?_,?_,?_⟩
  · intro address value resident
    have original := retired.resident.mp resident
    apply (typed.2.1 address value original).resident_transport ?_ ?_ (fun _ origin => origin.retire retired) ⟨address,original⟩
    · intro key loan _ found live
      have safe : loan.referent.root ≠ id := by
        cases retired with
        | vacant _ _ _ allowed => exact allowed.1 key loan found live
      refine ⟨?_,fun _ type => type.retained (fun _ selected => ?_) retired.read⟩
      · cases retired
        exact found
      · simpa only [retired.roots_other safe] using selected
    · cases retired
      rfl
  · intro key root value found contents
    cases retired with
    | vacant _ _ empty _ =>
        by_cases same : key = id
        · subst key
          simp only [Table.get_set] at found
          cases found
          simp [empty] at contents
        · exact typed.2.2.1 key root value (by simpa only [Table.get_set_other _ _ _ _ same] using found) contents
  · intro key root found
    cases retired with
    | vacant selected _ _ _ =>
        by_cases same : key = id
        · subst key
          simp only [Table.get_set] at found
          cases found
          have supported := typed.2.2.2 id _ selected
          exact supported
        · exact typed.2.2.2 key root (by simpa only [Table.get_set_other _ _ _ _ same] using found)

theorem EndsLoan.live_origin {before after : World} {id key : Identity} {loan : Loan}
    (ended : EndsLoan before id after) (found : after.loans.get key = some loan) (live : loan.live = true) :
    before.loans.get key = some loan := by
  cases ended with
  | restored _ _ _ _ _ =>
      by_cases same : key = id
      · subst key
        simp only [Table.get_set] at found
        cases found
        cases live
      · simpa only [Table.get_set_other _ _ _ _ same] using found

theorem AncestorLoan.endLoan {before after : World} {id ancestor child : Identity}
    (ended : EndsLoan before id after) (related : AncestorLoan before ancestor child) : AncestorLoan after ancestor child := by
  cases ended with
  | restored selected _ _ _ _ =>
      induction related with
      | refl => exact .refl
      | @parent parent child loan found link _ ih =>
          by_cases same : child = id
          · subst child
            have equal := Option.some.inj (selected.symm.trans found)
            subst loan
            exact .parent (Table.get_set _ _ _) link ih
          · exact .parent (by simpa only [Table.get_set_other _ _ _ _ same] using found) link ih

theorem EndsLoan.wellFormed {before after : World} {id : Identity}
    (valid : before.WellFormed) (ended : EndsLoan before id after) : after.WellFormed := by
  have parents := ended.loanParents valid
  have locations := ended.liveLoanLocations (World.liveLoanLocations valid)
  have ancestry := fun {a b} => AncestorLoan.endLoan (ancestor := a) (child := b) ended
  have liveOrigin := fun {key loan} => ended.live_origin (key := key) (loan := loan)
  cases ended with
  | restored selected _ _ unreferenced _ =>
      rcases valid with ⟨rootUnique,loanUnique,proofUnique,regionUnique,proofs,packs,owners,ownerUnique,
        roots,regions,bases,ranges,loans,references,overlaps,_,_⟩
      refine ⟨rootUnique,loanUnique.set _ _,proofUnique,regionUnique,proofs,packs,owners,ownerUnique,
        roots,regions,bases,ranges,?_,?_,?_,parents,locations⟩
      · intro key loan found
        by_cases same : key = id
        · subst key
          simp only [Table.get_set] at found
          cases found
          obtain ⟨identity,bound,_⟩ := loans id _ selected
          exact ⟨identity,bound,by simp⟩
        · exact loans key loan (by simpa only [Table.get_set_other _ _ _ _ same] using found)
      · intro address value key resident head
        have different : key ≠ id := by
          intro same
          subst key
          exact unreferenced ⟨address,value,resident,head⟩
        obtain ⟨loan,found,live⟩ := references address value key resident head
        exact ⟨loan,by simpa only [Table.get_set_other _ _ _ _ different] using found,live⟩
      · intro a b left right first second leftLive rightLive overlap unique
        exact (overlaps a b left right (liveOrigin first leftLive) (liveOrigin second rightLive)
          leftLive rightLive overlap unique).imp ancestry ancestry

theorem EndsLoan.worldTyped {program : Kernel.Program} {before after : World} {id : Identity}
    (typed : Typing.WorldTyped program before) (ended : EndsLoan before id after) : Typing.WorldTyped program after := by
  have valid := ended.wellFormed typed.1
  cases ended with
  | restored _ _ _ unreferenced _ =>
      refine ⟨valid,?_,typed.2.2⟩
      intro address value resident
      apply (typed.2.1 address value resident).resident_transport ?_ ?_ ?_ ⟨address,resident⟩
      · intro key loan references found _
        have different : key ≠ id := fun same => unreferenced (same ▸ references)
        exact ⟨by simpa only [Table.get_set_other _ _ _ _ different] using found,
          fun _ type => type.retained (fun _ selected => selected) (fun _ => rfl)⟩
      · rfl
      · exact fun _ origin => origin

namespace Execution

theorem RegionEnds.wellFormed {before after : World} {region : Identity}
    (valid : before.WellFormed) (ended : RegionEnds before region after) : after.WellFormed := by
  obtain ⟨⟨noRoots,noLoans,noProofs,noPacks⟩,rfl⟩ := ended
  rcases valid with ⟨rootUnique,loanUnique,proofUnique,regionUnique,proofs,packs,owners,ownerUnique,
    roots,regions,bases,ranges,loans,references,overlaps,parents,locations⟩
  refine ⟨rootUnique,loanUnique,proofUnique,regionUnique.filter _,?_,?_,owners,ownerUnique,?_,?_,bases,ranges,?_,references,?_,parents,locations⟩
  · intro id available found
    obtain ⟨identity,bound,brand,active⟩ := proofs id available found
    refine ⟨identity,bound,brand,fun live => ⟨?_,(active live).2⟩⟩
    simpa using And.intro (active live).1 (noProofs id available found live)
  · intro address value pack resident head
    obtain ⟨bound,live,length,distinct,facts⟩ := packs address value pack resident head
    refine ⟨bound,?_,length,distinct,facts⟩
    simpa using And.intro live (noPacks address value pack resident head)
  · intro id root found
    obtain ⟨bound,active,layout,bytes,bounds⟩ := roots id root found
    refine ⟨bound,fun live => ?_,layout,bytes,bounds⟩
    simpa using And.intro (active live) (noRoots id root found live)
  · intro id member
    exact regions id (List.mem_filter.mp member).1
  · intro id loan found
    obtain ⟨identity,bound,active⟩ := loans id loan found
    refine ⟨identity,bound,fun live => ⟨?_,(active live).2⟩⟩
    simpa using And.intro (active live).1 (noLoans id loan found live)
  · intro a b left right first second leftLive rightLive overlap unique
    exact (overlaps a b left right first second leftLive rightLive overlap unique).imp
      (fun related => related.transport (before := before) (after := { before with liveRegions := before.liveRegions.filter (· != region) }) rfl)
      (fun related => related.transport (before := before) (after := { before with liveRegions := before.liveRegions.filter (· != region) }) rfl)

theorem RegionEnds.worldTyped {program : Kernel.Program} {before after : World} {region : Identity}
    (typed : Typing.WorldTyped program before) (ended : RegionEnds before region after) : Typing.WorldTyped program after := by
  have valid := ended.wellFormed typed.1
  obtain ⟨_,rfl⟩ := ended
  refine ⟨valid,?_,typed.2.2⟩
  intro address value resident
  apply (typed.2.1 address value resident).resident_transport ?_ ?_ ?_ ⟨address,resident⟩
  · intro id loan _ found _
    exact ⟨found,fun _ type => type.retained (fun _ selected => selected) (fun _ => rfl)⟩
  · rfl
  · exact fun _ origin => origin

end Execution

theorem CanEndStorage.owner_permission {world : World} {id : Identity} {root : Root}
    (safe : CanEndStorage world id) (found : world.roots.get id = some root) (live : root.live = true) :
    Permitted world .owner .owned ⟨id,root.generation,[]⟩ := by
  refine ⟨⟨root,by simp [World.root,found,live]⟩,?_⟩
  intro key loan selected active overlap _
  exact safe.1 key loan selected active overlap.1.symm

theorem Memory.ReleasesBuffer.wellFormed {program : Program} {before after : World} {pointer : RawPointer} {domain : Identity}
    (valid : before.WellFormed) (released : Memory.ReleasesBuffer program before pointer domain after) : after.WellFormed := by
  cases released with
  | release _ _ _ found live _ _ _ _ _ _ safe written retired closed =>
      exact closed.wellFormed (retired.wellFormed (World.clear_wellFormed valid (safe.owner_permission found live) written))

theorem Memory.ReleasesBuffer.worldTyped {program : Kernel.Program} {before after : World} {pointer : RawPointer} {domain : Identity}
    (typed : Typing.WorldTyped program before) (released : Memory.ReleasesBuffer program.declarations before pointer domain after) :
    Typing.WorldTyped program after := by
  cases released with
  | release _ _ _ found live _ _ _ _ _ _ safe written retired closed =>
      exact closed.worldTyped (retired.worldTyped (World.clear_worldTyped typed (safe.owner_permission found live) written))

theorem Execution.RetiresEmpty.worldTyped {program : Kernel.Program} {before after : World} {addresses : List Address}
    (typed : Typing.WorldTyped program before) (retired : Execution.RetiresEmpty before addresses after) :
    Typing.WorldTyped program after := by
  induction retired with
  | nil => exact typed
  | cons _ first _ ih => exact ih (first.worldTyped typed)

/-- Deactivating a reservation keeps the identity and type of any retained
witness. Activity controls use permission, not its representation shape. -/
theorem Typing.ValueTyped.deactivateAvailability {program : Kernel.Program} {world : World} {value : Value}
    {id : Identity} {available : Availability} (selected : world.availability.get id = some available)
    (typed : Typing.ValueTyped program world value) :
    Typing.ValueTyped program { world with availability := world.availability.set id { available with active := false } } value := by
  refine Typing.ValueTyped.rec
    (motive_1 := fun value _ => Typing.ValueTyped program
      { world with availability := world.availability.set id { available with active := false } } value)
    (motive_2 := fun fields types _ => Typing.FieldsTyped program
      { world with availability := world.availability.set id { available with active := false } } fields types)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
  · exact fun {_ _} => .unit
  · exact fun {_ _ _} valid => .scalar valid
  · exact fun {_ _ _ _ _ _} shape _ fields => .aggregate shape fields
  · exact fun {_ _ _ _ _ _ _} found active mode region located =>
      .reference found active mode region (located.retained (fun _ found => found) (fun _ => rfl))
  · exact fun {_ _ _ _ _} bound origin => .pointer bound origin
  · exact fun {_ _ _ _ _ _} callable _ fields => .callable callable fields
  · exact fun {_ _ _ _ _ _} operation => .operation operation
  · exact fun {_ _ _ _ _} => .label
  · exact fun {_ _ _ _} type => .continuation type
  · intro owner brand region residents key live proof found brandEq idEq regionEq residentsEq
    by_cases same : key = id
    · subst key
      have equal := Option.some.inj (selected.symm.trans found)
      subst proof
      exact .available (Table.get_set _ _ _) brandEq idEq regionEq residentsEq
    · exact .available (by simpa only [Table.get_set_other _ _ _ _ same] using found) brandEq idEq regionEq residentsEq
  · exact fun {_ _ _ _ _ _ _} _ brand region length distinct fields => .bindings fields brand region length distinct
  · exact .nil
  · exact fun {_ _ _} _ fields => .hole fields
  · exact fun {_ _ _ _} _ type _ value fields => .resident value type fields

theorem World.deactivateAvailability_wellFormed {world : World} {id : Identity} {available : Availability}
    (valid : world.WellFormed) (selected : world.availability.get id = some available) :
    ({ world with availability := world.availability.set id { available with active := false } } : World).WellFormed := by
  rcases valid with ⟨rootsUnique,loansUnique,proofsUnique,regionsUnique,proofs,packs,owners,unique,
    roots,regions,bases,ranges,loans,references,overlaps,parents,locations⟩
  refine ⟨rootsUnique,loansUnique,proofsUnique.set _ _,regionsUnique,?_,packs,owners,unique,
    roots,regions,bases,ranges,loans,references,?_,parents,locations⟩
  · intro key proof found
    by_cases same : key = id
    · subst key
      simp only [Table.get_set] at found
      cases found
      obtain ⟨identity,bound,brand,_⟩ := proofs id available selected
      exact ⟨identity,bound,brand,by simp⟩
    · exact proofs key proof (by simpa only [Table.get_set_other _ _ _ _ same] using found)
  · intro a b left right first second leftLive rightLive overlap unique
    rcases overlaps a b left right first second leftLive rightLive overlap unique with ancestor | ancestor
    · exact Or.inl (ancestor.transport (before := world) (by rfl))
    · exact Or.inr (ancestor.transport (before := world) (by rfl))

theorem World.deactivateAvailability_worldTyped {program : Kernel.Program} {world : World} {id : Identity} {available : Availability}
    (typed : Typing.WorldTyped program world) (selected : world.availability.get id = some available) :
    Typing.WorldTyped program { world with availability := world.availability.set id { available with active := false } } := by
  exact ⟨World.deactivateAvailability_wellFormed typed.1 selected,
    fun address value resident => (typed.2.1 address value resident).deactivateAvailability selected,typed.2.2⟩

end Glorious.Language
