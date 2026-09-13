import GloriousLanguage.BorrowConstructionPreservation
import GloriousLanguage.CopyStructure

/-! Preservation for source Copy. The existing copy traversal supplies fresh
owner identities and the binding-fact renaming; copies keep referent identity
and do not acquire ownership of the storage they reference. -/
namespace Glorious.Language

theorem CopyTree.bounds {program : Program} {next finish : Nat} {value copied : Value} {origins : Table Identity}
    (copy : CopyTree program next value finish copied origins) :
    next < finish ∧
    (∀ path resident, ResidentAt copied path resident → next ≤ resident.owner ∧ resident.owner < finish) ∧
    (∀ original fresh, (original,fresh) ∈ origins → next ≤ fresh ∧ fresh < finish) := by
  refine CopyTree.rec
    (motive_1 := fun next _ finish copied origins _ => next < finish ∧
      (∀ path resident, ResidentAt copied path resident → next ≤ resident.owner ∧ resident.owner < finish) ∧
      (∀ original fresh, (original,fresh) ∈ origins → next ≤ fresh ∧ fresh < finish))
    (motive_2 := fun next _ finish copied origins _ => next ≤ finish ∧
      (∀ (index : Nat) child, copied[index]? = some (some child) → ∀ path resident,
        ResidentAt child path resident → next ≤ resident.owner ∧ resident.owner < finish) ∧
      (∀ original fresh, (original,fresh) ∈ origins → next ≤ fresh ∧ fresh < finish))
    ?_ ?_ ?_ copy
  · intro next owner type head fields resources copied finish origins _ _ _ ih
    have bound : next < finish := by omega
    refine ⟨bound,?_,?_⟩
    · intro path resident inside
      cases inside with
      | root => exact ⟨Nat.le_refl _,bound⟩
      | field selected nested =>
          have bounds := ih.2.1 _ _ selected _ _ nested
          exact ⟨by omega,bounds.2⟩
    · intro original fresh member
      rcases List.mem_cons.mp member with equal | later
      · cases equal; exact ⟨Nat.le_refl _,bound⟩
      · have bounds := ih.2.2 _ _ later
        exact ⟨by omega,bounds.2⟩
  · intro next
    exact ⟨Nat.le_refl _,fun _ _ impossible => by simp at impossible,fun _ _ impossible => by simp at impossible⟩
  · intro next middle finish value copied rest copies first later _ _ ih tail
    refine ⟨Nat.le_trans (Nat.le_of_lt ih.1) tail.1,?_,?_⟩
    · intro index child selected path resident inside
      cases index with
      | zero =>
          have same := Option.some.inj (Option.some.inj selected)
          subst child
          have bounds := ih.2.1 path resident inside
          exact ⟨bounds.1,Nat.lt_of_lt_of_le bounds.2 tail.1⟩
      | succ index =>
          have bounds := tail.2.1 index child selected path resident inside
          exact ⟨Nat.le_trans (Nat.le_of_lt ih.1) bounds.1,bounds.2⟩
    · intro original fresh member
      rcases List.mem_append.mp member with earlier | later
      · have bounds := ih.2.2 _ _ earlier
        exact ⟨bounds.1,Nat.lt_of_lt_of_le bounds.2 tail.1⟩
      · have bounds := tail.2.2 _ _ later
        exact ⟨Nat.le_trans (Nat.le_of_lt ih.1) bounds.1,bounds.2⟩

theorem CopyFields.bounds {program : Program} {next finish : Nat}
    {fields copied : List (Option Value)} {origins : Table Identity}
    (copy : CopyFields program next fields finish copied origins) :
    next ≤ finish ∧
    (∀ (index : Nat) child, copied[index]? = some (some child) → ∀ path resident,
      ResidentAt child path resident → next ≤ resident.owner ∧ resident.owner < finish) := by
  refine CopyFields.rec
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun next _ finish copied _ _ => next ≤ finish ∧
      (∀ (index : Nat) child, copied[index]? = some (some child) → ∀ path resident,
        ResidentAt child path resident → next ≤ resident.owner ∧ resident.owner < finish))
    ?_ ?_ ?_ copy
  · intros; trivial
  · intro next
    exact ⟨Nat.le_refl _,fun _ _ impossible => by simp at impossible⟩
  · intro next middle finish value copied rest copies first later tree _ _ ih
    have bounds := tree.bounds
    refine ⟨Nat.le_trans (Nat.le_of_lt bounds.1) ih.1,?_⟩
    intro index child selected path resident inside
    cases index with
    | zero =>
        have same := Option.some.inj (Option.some.inj selected)
        subst child
        have range := bounds.2.1 path resident inside
        exact ⟨range.1,Nat.lt_of_lt_of_le range.2 ih.1⟩
    | succ index =>
        have range := ih.2 index child selected path resident inside
        exact ⟨Nat.le_trans (Nat.le_of_lt bounds.1) range.1,range.2⟩

theorem CopyTree.owner_unique {program : Program} {next finish : Nat} {value copied : Value} {origins : Table Identity}
    (copy : CopyTree program next value finish copied origins) :
    ∀ left right x y, ResidentAt copied left x → ResidentAt copied right y → x.owner = y.owner → left = right := by
  refine CopyTree.rec
    (motive_1 := fun _ _ _ copied _ _ =>
      ∀ left right x y, ResidentAt copied left x → ResidentAt copied right y → x.owner = y.owner → left = right)
    (motive_2 := fun _ _ _ copied _ _ =>
      ∀ first second left right x y a b,
        copied[first]? = some (some x) → copied[second]? = some (some y) →
        ResidentAt x left a → ResidentAt y right b → a.owner = b.owner → first :: left = second :: right)
    ?_ ?_ ?_ copy
  · intro next owner type head fields resources copied finish origins _ _ tree ih left right x y first second same
    cases first with
    | root =>
        cases second with
        | root => rfl
        | field selected nested =>
            have bounds := tree.bounds.2 _ _ selected _ _ nested
            change next = y.owner at same
            omega
    | field selected nested =>
        cases second with
        | root =>
            have bounds := tree.bounds.2 _ _ selected _ _ nested
            change x.owner = next at same
            have lower : next+1 ≤ x.owner := bounds.1
            rw [same] at lower
            exact False.elim (Nat.not_succ_le_self _ lower)
        | field other inside => exact ih _ _ _ _ _ _ _ _ selected other nested inside same
  · intro next first second left right x y a b selected
    simp at selected
  · intro next middle finish value copied rest copies first later tree tail ih restIH
      leftIndex rightIndex left right x y a b first second atFirst atSecond same
    cases leftIndex with
    | zero =>
        have equal := Option.some.inj (Option.some.inj first)
        subst x
        cases rightIndex with
        | zero =>
            have equal := Option.some.inj (Option.some.inj second)
            subst y
            exact congrArg (List.cons 0) (ih _ _ _ _ atFirst atSecond same)
        | succ rightIndex =>
            have earlier := (tree.bounds.2.1 _ _ atFirst).2
            have later := (tail.bounds.2 _ _ second _ _ atSecond).1
            rw [same] at earlier
            exact False.elim ((Nat.not_lt_of_ge later) earlier)
    | succ leftIndex =>
        cases rightIndex with
        | zero =>
            have equal := Option.some.inj (Option.some.inj second)
            subst y
            have earlier := (tree.bounds.2.1 _ _ atSecond).2
            have later := (tail.bounds.2 _ _ first _ _ atFirst).1
            rw [← same] at earlier
            exact False.elim ((Nat.not_lt_of_ge later) earlier)
        | succ rightIndex =>
            have equal := restIH _ _ _ _ _ _ _ _ first second atFirst atSecond same
            have indices := List.cons.inj equal
            simp [indices.1,indices.2]

theorem CopyTree.resident_origin {program : Program} {next finish : Nat} {value copied : Value} {origins : Table Identity}
    (copy : CopyTree program next value finish copied origins) :
    ∀ path resident, ResidentAt copied path resident → ∃ original,
      ResidentAt value path original ∧ resident.head = original.head ∧ resident.fields.length = original.fields.length := by
  intro path resident inside
  obtain ⟨original,first,last,names,located,subtree⟩ := copy.resident_copy path resident inside
  refine ⟨original,located,?_,?_⟩
  · cases subtree; rfl
  · cases subtree with
    | resident _ _ fields => exact fields.length

theorem CopyValue.bounds {program : Program} {next finish : Nat} {value copied : Value}
    (copy : CopyValue program next value finish copied) :
    next < finish ∧ ∀ path resident, ResidentAt copied path resident → next ≤ resident.owner ∧ resident.owner < finish := by
  cases copy with
  | copy tree _ =>
      refine ⟨tree.bounds.1,?_⟩
      intro path resident inside
      obtain ⟨original,rawInside,rfl⟩ := ResidentAt.mapBindingOrigins_iff.mp inside
      simpa only [Value.mapBindingOrigins_owner] using tree.bounds.2.1 path original rawInside

theorem CopyValue.owner_unique {program : Program} {next finish : Nat} {value copied : Value}
    (copy : CopyValue program next value finish copied) :
    ∀ left right x y, ResidentAt copied left x → ResidentAt copied right y → x.owner = y.owner → left = right := by
  cases copy with
  | copy tree _ =>
      intro left right x y first second same
      obtain ⟨oldFirst,rawFirst,rfl⟩ := ResidentAt.mapBindingOrigins_iff.mp first
      obtain ⟨oldSecond,rawSecond,rfl⟩ := ResidentAt.mapBindingOrigins_iff.mp second
      exact tree.owner_unique left right oldFirst oldSecond rawFirst rawSecond (by simpa only [Value.mapBindingOrigins_owner] using same)

theorem CopyValue.resident_origin {program : Program} {next finish : Nat} {value copied : Value}
    (copy : CopyValue program next value finish copied) {path : List Nat} {resident : Value}
    (inside : ResidentAt copied path resident) :
    ∃ original map, ResidentAt value path original ∧
      resident.head = (match original.head with | .bindings pack => .bindings (pack.mapOrigins map) | head => head) ∧
      resident.fields.length = original.fields.length ∧ ∀ old, old < next → map old < finish := by
  cases copy with
  | @copy raw origins tree _ =>
      obtain ⟨rawResident,rawInside,rfl⟩ := ResidentAt.mapBindingOrigins_iff.mp inside
      obtain ⟨original,oldInside,head,length⟩ := tree.resident_origin _ _ rawInside
      refine ⟨original,(fun id => (origins.get id).getD id),oldInside,?_,?_,?_⟩
      · rw [Value.mapBindingOrigins_head,head]
        rfl
      · simpa only [Value.mapBindingOrigins_length] using length
      · intro old bound
        cases found : origins.get old with
        | none => simpa only [found,Option.getD_none] using Nat.lt_trans bound tree.bounds.1
        | some fresh =>
            have bound := (tree.bounds.2.2 old fresh (Table.mem_of_get found)).2
            simpa only [found,Option.getD_some] using bound

theorem World.write_value_origin {before after : World} {destination observed : Address} {inserted value : Value}
    (written : before.write destination (some inserted) = some after) (resident : after.Resident observed value) :
    (∃ suffix, observed = { destination with fields := destination.fields ++ suffix } ∧ ResidentAt inserted suffix value) ∨
      ∃ original, before.Resident observed original ∧ value.shell = original.shell := by
  have stored := World.resident_iff_stores.mp resident
  by_cases included : destination.Prefix observed
  · obtain ⟨suffix,equal⟩ := Address.prefix_extension included
    have inside := World.write_read_inside written suffix
    rw [← equal,stored] at inside
    exact Or.inl ⟨suffix,equal,ResidentAt.iff_atPath.mpr inside.symm⟩
  · have framed := World.write_read_shell written included
    rw [stored] at framed
    obtain ⟨original,found,same⟩ := Option.map_eq_some_iff.mp framed.symm
    exact Or.inr ⟨original,World.resident_iff_stores.mpr found,same.symm⟩

/-- An insertion theorem about its actual input value and vacant storage.
Owner separation and header obligations are premises on the inserted tree,
not a well-formed post-state. Copy and moving aggregate construction derive
these obligations from their respective authoritative producers. -/
theorem World.install_wellFormedWithOrigins {before middle : World} {destination : Address} {inserted : Value} {next originBound : Nat}
    (valid : before.WellFormedWithOrigins originBound) (vacant : before.Vacant destination) (monotone : before.nextOwner ≤ next)
    (owners : ∀ path value, ResidentAt inserted path value → value.owner < next)
    (unique : ∀ a b x y, ResidentAt inserted a x → ResidentAt inserted b y → x.owner = y.owner → a = b)
    (separate : ∀ path value, ResidentAt inserted path value →
      ∀ address original, before.Resident address original → value.owner ≠ original.owner)
    (packs : ∀ path value pack, ResidentAt inserted path value → value.head = .bindings pack →
      pack.brand < before.nextProof ∧ pack.region ∈ before.liveRegions ∧ pack.fields.length = value.fields.length ∧
      pack.fields.Nodup ∧ ∀ fact ∈ pack.facts, fact.resultOrigin < originBound)
    (references : ∀ path value id, ResidentAt inserted path value → value.head = .reference id →
      ∃ loan, before.loans.get id = some loan ∧ loan.live = true)
    (written : before.write destination (some inserted) = some middle) :
    ({ middle with nextOwner := next } : World).WellFormedWithOrigins originBound := by
  have rest := World.write_rest written
  have loansEq := congrArg World.loans rest
  have proofEq := congrArg World.availability rest
  have regionsEq := congrArg World.liveRegions rest
  have rootBound := congrArg World.nextRoot rest
  have loanBound := congrArg World.nextLoan rest
  have regionBound := congrArg World.nextRegion rest
  have proofBound := congrArg World.nextProof rest
  have locations := World.write_locations written
  have rootsUnique := World.write_unique_roots valid.1 written
  rcases valid with ⟨_,loansUnique,proofsUnique,regionsUnique,proofs,oldPacks,oldOwners,oldUnique,roots,regions,bases,ranges,
    loans,oldReferences,overlaps,parents,located,guards⟩
  refine ⟨rootsUnique,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [loansEq] using loansUnique
  · simpa only [proofEq] using proofsUnique
  · simpa only [regionsEq] using regionsUnique
  · intro id available found
    have oldFound : before.availability.get id = some available := by simpa only [proofEq] using found
    obtain ⟨identity,bound,brand,active,recorded⟩ := proofs id available oldFound
    refine ⟨identity,by simpa only [proofBound] using bound,brand,?_,
      by simpa only [loansEq] using recorded⟩
    intro live
    obtain ⟨region,reserved⟩ := active live
    refine ⟨by simpa only [regionsEq] using region,?_⟩
    intro place member
    obtain ⟨root,selected⟩ := Option.isSome_iff_exists.mp (reserved place member)
    obtain ⟨_,afterRoot,_⟩ := World.root_transport locations selected
    change (middle.root place.address).isSome = true
    simp [afterRoot]
  · intro address value pack resident head
    rcases World.write_value_origin written resident with ⟨path,_,inside⟩ | ⟨original,oldResident,shell⟩
    · simpa only [proofBound,regionsEq] using packs path value pack inside head
    · have oldHead : original.head = .bindings pack := by
        have same : value.head = original.head := by
          simpa [Value.shell,Value.withFields,Value.head] using congrArg Value.head shell
        exact same.symm.trans head
      have arity : value.fields.length = original.fields.length := by
        simpa [Value.shell,Value.withFields,Value.fields] using congrArg (fun value => value.fields.length) shell
      obtain ⟨brand,region,length,distinct,facts⟩ := oldPacks address original pack oldResident oldHead
      exact ⟨by simpa only [proofBound] using brand,by simpa only [regionsEq] using region,
        length.trans arity.symm,distinct,facts⟩
  · intro address value resident
    rcases World.write_value_origin written resident with ⟨path,_,inside⟩ | ⟨original,oldResident,shell⟩
    · exact owners path value inside
    · have same : value.owner = original.owner := by
        simpa [Value.shell,Value.withFields,Value.owner] using congrArg Value.owner shell
      simpa only [same] using Nat.lt_of_lt_of_le (oldOwners address original oldResident) monotone
  · intro a b x y first second same
    rcases World.write_value_origin written first with ⟨left,leftAddress,leftInside⟩ | ⟨oldFirst,oldA,shellA⟩
    · rcases World.write_value_origin written second with ⟨right,rightAddress,rightInside⟩ | ⟨oldSecond,oldB,shellB⟩
      · have equal := unique left right x y leftInside rightInside same
        exact leftAddress.trans (equal ▸ rightAddress.symm)
      · have oldOwner : y.owner = oldSecond.owner := by
          simpa [Value.shell,Value.withFields,Value.owner] using congrArg Value.owner shellB
        exact False.elim (separate left x leftInside b oldSecond oldB (same.trans oldOwner))
    · have oldOwnerA : x.owner = oldFirst.owner := by
        simpa [Value.shell,Value.withFields,Value.owner] using congrArg Value.owner shellA
      rcases World.write_value_origin written second with ⟨right,_,rightInside⟩ | ⟨oldSecond,oldB,shellB⟩
      · exact False.elim (separate right y rightInside a oldFirst oldA (same.symm.trans oldOwnerA))
      · have oldOwnerB : y.owner = oldSecond.owner := by
          simpa [Value.shell,Value.withFields,Value.owner] using congrArg Value.owner shellB
        exact oldUnique a b oldFirst oldSecond oldA oldB (oldOwnerA.symm.trans (same.trans oldOwnerB))
  · intro id root found
    obtain ⟨original,oldFound,same⟩ := World.root_origin locations found
    rw [same]
    simpa only [rootBound,regionsEq] using roots id original oldFound
  · simpa only [regionsEq,regionBound] using regions
  · intro id root found live
    obtain ⟨original,oldFound,same⟩ := World.root_origin locations found
    have oldLive : original.live = true := by rw [same] at live; exact live
    rw [same]
    exact bases id original oldFound oldLive
  · intro a b left right leftFound rightFound different leftLive rightLive
    obtain ⟨oldLeft,oldFirst,leftEq⟩ := World.root_origin locations leftFound
    obtain ⟨oldRight,oldSecond,rightEq⟩ := World.root_origin locations rightFound
    have oldLeftLive : oldLeft.live = true := by rw [leftEq] at leftLive; exact leftLive
    have oldRightLive : oldRight.live = true := by rw [rightEq] at rightLive; exact rightLive
    rw [leftEq,rightEq]
    exact ranges a b oldLeft oldRight oldFirst oldSecond different oldLeftLive oldRightLive
  · intro id loan found
    have oldFound : before.loans.get id = some loan := by simpa only [loansEq] using found
    obtain ⟨identity,bound,active⟩ := loans id loan oldFound
    refine ⟨identity,by simpa only [loanBound] using bound,?_⟩
    intro live
    obtain ⟨region,root⟩ := active live
    refine ⟨by simpa only [regionsEq] using region,?_⟩
    obtain ⟨_,selected⟩ := Option.isSome_iff_exists.mp root
    obtain ⟨_,afterRoot,_⟩ := World.root_transport locations selected
    change (middle.root loan.referent).isSome = true
    simp [afterRoot]
  · intro address value id resident head
    have live : ∃ loan, before.loans.get id = some loan ∧ loan.live = true := by
      rcases World.write_value_origin written resident with ⟨path,_,inside⟩ | ⟨original,oldResident,shell⟩
      · exact references path value id inside head
      · have same : value.head = original.head := by
          simpa [Value.shell,Value.withFields,Value.head] using congrArg Value.head shell
        exact oldReferences address original id oldResident (same.symm.trans head)
    simpa only [loansEq] using live
  · intro a b left right first second leftLive rightLive overlap unique
    have oldFirst : before.loans.get a = some left := by simpa only [loansEq] using first
    have oldSecond : before.loans.get b = some right := by simpa only [loansEq] using second
    rcases overlaps a b left right oldFirst oldSecond leftLive rightLive overlap unique with ancestry | ancestry
    · exact Or.inl (AncestorLoan.transport (before := before) loansEq ancestry)
    · exact Or.inr (AncestorLoan.transport (before := before) loansEq ancestry)
  · simpa only [World.LoanParents,loansEq] using parents
  · intro id loan found live
    have oldFound : before.loans.get id = some loan := by simpa only [loansEq] using found
    have retained := World.write_located written (vacant.no_located_descendant (located id loan oldFound live))
      (located id loan oldFound live)
    exact retained
  · simpa only [World.LoanGuards,World.LoanKinds,loansEq] using guards

theorem World.install_wellFormed {before middle : World} {destination : Address} {inserted : Value} {next : Nat}
    (valid : before.WellFormed) (vacant : before.Vacant destination) (monotone : before.nextOwner ≤ next)
    (owners : ∀ path value, ResidentAt inserted path value → value.owner < next)
    (unique : ∀ a b x y, ResidentAt inserted a x → ResidentAt inserted b y → x.owner = y.owner → a = b)
    (separate : ∀ path value, ResidentAt inserted path value →
      ∀ address original, before.Resident address original → value.owner ≠ original.owner)
    (packs : ∀ path value pack, ResidentAt inserted path value → value.head = .bindings pack →
      pack.brand < before.nextProof ∧ pack.region ∈ before.liveRegions ∧ pack.fields.length = value.fields.length ∧
      pack.fields.Nodup ∧ ∀ fact ∈ pack.facts, fact.resultOrigin < next)
    (references : ∀ path value id, ResidentAt inserted path value → value.head = .reference id →
      ∃ loan, before.loans.get id = some loan ∧ loan.live = true)
    (written : before.write destination (some inserted) = some middle) :
    ({ middle with nextOwner := next } : World).WellFormed :=
  World.install_wellFormedWithOrigins (valid.mono monotone) vacant monotone owners unique separate packs references written

theorem World.Stores.residentAt {world : World} {address : Address} {whole value : Value} {path : List Nat}
    (stored : world.Stores address whole) (inside : ResidentAt whole path value) :
    world.Resident { address with fields := address.fields ++ path } value := by
  apply World.resident_iff_stores.mpr
  change world.read { address with fields := address.fields ++ path } = some value
  rw [World.read_append,stored]
  exact ResidentAt.iff_atPath.mp inside

theorem Copies.wellFormed {program : RuntimeProgram} {before after : World} {authority source destination}
    (valid : before.WellFormed) (copied : Copies program before authority source destination after) : after.WellFormed := by
  cases copied with
  | copy stored _ _ _ vacant _ copy written =>
    apply World.install_wellFormed valid vacant (Nat.le_of_lt copy.bounds.1)
      (fun path value inside => (copy.bounds.2 path value inside).2) copy.owner_unique ?_ ?_ ?_ written
    · intro path value inside address original resident same
      have fresh := (copy.bounds.2 path value inside).1
      have old := World.owner_bound valid resident
      rw [← same] at old
      exact (Nat.not_lt_of_ge fresh) old
    · intro path value pack inside head
      obtain ⟨original,map,oldInside,shape,length,bounds⟩ := copy.resident_origin inside
      have oldResident := stored.residentAt oldInside
      have mapped := shape.symm.trans head
      have originalPack : ∃ oldPack, original.head = .bindings oldPack ∧ pack = oldPack.mapOrigins map := by
        cases selected : original.head <;> simp_all
      obtain ⟨oldPack,selected,rfl⟩ := originalPack
      obtain ⟨brand,region,arity,distinct,facts⟩ := valid.2.2.2.2.2.1 _ original oldPack oldResident selected
      refine ⟨brand,region,arity.trans length.symm,distinct,?_⟩
      intro fact member
      obtain ⟨oldFact,oldMember,rfl⟩ := List.mem_map.mp member
      exact bounds _ (facts oldFact oldMember)
    · intro path value id inside head
      obtain ⟨original,map,oldInside,shape,_,_⟩ := copy.resident_origin inside
      have selected : original.head = .reference id := by
        have mapped := shape.symm.trans head
        cases selected : original.head <;> simp_all
      exact valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ original id (stored.residentAt oldInside) selected

theorem Copies.locations {program : RuntimeProgram} {before after : World} {authority source destination}
    (copied : Copies program before authority source destination after) (id : Identity) :
    (after.roots.get id).map Root.location = (before.roots.get id).map Root.location := by
  cases copied with
  | copy _ _ _ _ _ _ _ written => exact World.write_locations written id

theorem Typing.ValueTyped.copy {program : Kernel.Program} {before after : World}
    {authority source destination value} (valid : before.WellFormed)
    (copied : Copies program.toRuntimeProgram before authority source destination after)
    (typed : Typing.ValueTyped program before value) : Typing.ValueTyped program after value := by
  apply typed.transport ?_ ?_ (fun _ origin => origin.transport copied.locations)
  · intro id loan found active
    cases copied with
    | copy _ _ _ _ vacant _ _ written =>
        refine ⟨?_,?_⟩
        · have same := World.write_loans written
          simpa only [same] using found
        · intro type located
          exact ((World.write_address_types written (vacant.no_located_descendant
            (World.liveLoanLocations valid _ _ found active))).mp located).retained
              (fun _ selected => selected) (fun _ => rfl)
  · cases copied with
    | copy _ _ _ _ _ _ _ written =>
        have same := congrArg World.availability (World.write_rest written)
        exact same

theorem Copies.worldTyped {program : Kernel.Program} {before after : World} {authority source destination}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (copied : Copies program.toRuntimeProgram before authority source destination after) : Typing.WorldTyped program after := by
  have well := copied.wellFormed typed.1
  have retained : ∀ value, Typing.ValueTyped program before value → Typing.ValueTyped program after value :=
    fun _ value => value.copy typed.1 copied
  cases copied with
  | copy stored _ _ _ _ destinationType copy written =>
    obtain ⟨offset,destinationType⟩ := destinationType
    have roots := World.write_typed_roots valid inventory typed.roots destinationType written
      (fun resident same => by
        cases Option.some.inj same
        exact ⟨copy.typed (World.stores_typed typed.roots stored),copy.type_eq⟩)
    have realized := typed.2.2.2.2.of_locations (World.write_locations written)
    refine ⟨well,?_,?_,?_,realized⟩
    · intro address value resident
      exact retained _ (World.stores_typed roots (World.resident_iff_stores.mp resident))
    · intro id root value found contents
      by_cases live : root.live = true
      · exact (roots id root value found live contents).2
      · exact typed.2.2.1 id root value (World.write_dead_root written found live) contents
    · intro id root found
      obtain ⟨original,oldFound,same⟩ := World.root_origin (World.write_locations written) found
      have bound := congrArg World.nextRegion (World.write_rest written)
      rw [same]
      simpa only [bound] using typed.2.2.2.1 id original oldFound

theorem Acquires.worldTyped {program : Kernel.Program} {before after : World} {authority force source destination}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (acquired : Acquires program.toRuntimeProgram before authority force source destination after) : Typing.WorldTyped program after := by
  cases acquired with
  | explicitMove moved => exact moved.worldTyped valid inventory typed
  | copy copied => exact copied.worldTyped valid inventory typed
  | move _ _ _ moved => exact moved.worldTyped valid inventory typed

namespace Execution

theorem Captures.worldTyped {program : Kernel.Program} {context : Context} {before after : World} {captures addresses}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (captured : Captures program context before captures addresses after) : Typing.WorldTyped program after := by
  induction captured with
  | nil => exact typed
  | owned _ _ temporary acquired _ ih => exact ih (acquired.worldTyped valid inventory (temporary.worldTyped typed))
  | borrowed _ _ _ temporary borrowed _ ih => exact ih (borrowed.worldTyped valid inventory (temporary.worldTyped typed))

theorem CopiesObservations.worldTyped {program : Kernel.Program} {context : Context}
    {before after : World} {observations bindings}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (copied : CopiesObservations program context before observations bindings after) : Typing.WorldTyped program after := by
  induction copied with
  | nil => exact typed
  | copy _ _ temporary copied _ ih => exact ih (copied.worldTyped valid inventory (temporary.worldTyped typed))
  | borrow _ _ temporary borrowed _ ih => exact ih (borrowed.worldTyped valid inventory (temporary.worldTyped typed))

end Execution

end Glorious.Language
