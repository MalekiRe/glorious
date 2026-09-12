import GloriousLanguage.Preservation

/-! Ownership and whole-world preservation for the actual two-write transfer.
Resident origins below are derived from those writes, not supplied metadata. -/
namespace Glorious.Language

theorem Value.replace_inside {before after : Value} {path : List Nat} {replacement : Option Value}
    (written : before.replace path replacement = some after) (suffix : List Nat) :
    after.atPath (path ++ suffix) = replacement >>= fun value => value.atPath suffix := by
  induction path generalizing before after with
  | nil =>
      have same : replacement = some after := written
      simp [same]
  | cons index path ih =>
      rcases Value.replace_cons_shape written with ⟨_,found,⟨rfl,rfl⟩ | ⟨child,changed,rfl,nested,rfl⟩⟩
      · have bound := (List.getElem?_eq_some_iff.mp found).1
        change ((before.fields.set index replacement)[index]?.join >>= fun child => child.atPath suffix) = _
        rw [List.getElem?_set_self bound]
        rfl
      · have bound := (List.getElem?_eq_some_iff.mp found).1
        change ((before.fields.set index (some changed))[index]?.join >>= fun child => child.atPath (path ++ suffix)) = _
        rw [List.getElem?_set_self bound]
        exact ih nested

theorem World.write_read_inside {before after : World} {address : Address} {replacement : Option Value}
    (written : before.write address replacement = some after) (suffix : List Nat) :
    after.read { address with fields := address.fields ++ suffix } =
      replacement >>= fun value => value.atPath suffix := by
  unfold World.write at written
  cases selected : before.root address with
  | none => simp [selected] at written
  | some root =>
      have found := World.root_found selected
      simp only [selected] at written
      dsimp at written
      split at written
      next empty =>
        have result := Option.some.inj written
        subst after
        have emptyPath : address.fields = [] := List.isEmpty_iff.mp empty
        simp [World.read,World.root,Table.get_set,found.2.1,found.2.2,emptyPath]
      next =>
        cases resident : root.value with
        | none => simp [resident] at written
        | some whole =>
            simp only [resident] at written
            dsimp at written
            cases replaced : whole.replace address.fields replacement with
            | none => simp [replaced] at written
            | some changed =>
                have result : after = { before with roots := before.roots.set address.root { root with value := some changed } } := by
                  simpa [replaced] using written.symm
                subst after
                simpa [World.read,World.root,Table.get_set,found.2.1,found.2.2] using Value.replace_inside replaced suffix

/-- The location change witnessed by a move. It carries no dynamic facts:
the resident-origin theorem derives it from clear and install. -/
def Address.TransferredTo (source destination previous current : Address) : Prop :=
  (previous = current ∧ ¬ source.Prefix previous) ∨
  ∃ suffix, previous = { source with fields := source.fields ++ suffix } ∧
    current = { destination with fields := destination.fields ++ suffix }

theorem Address.TransferredTo.functional {source destination previous left right : Address}
    (a : Address.TransferredTo source destination previous left)
    (b : Address.TransferredTo source destination previous right) : left = right := by
  rcases a with ⟨rfl,outside⟩ | ⟨leftSuffix,oldLeft,newLeft⟩
  · rcases b with ⟨same,_⟩ | ⟨suffix,old,_⟩
    · exact same
    · exact False.elim (outside (old ▸ ⟨rfl,rfl,suffix,rfl⟩))
  · rcases b with ⟨rfl,outside⟩ | ⟨rightSuffix,oldRight,newRight⟩
    · exact False.elim (outside (oldLeft ▸ ⟨rfl,rfl,leftSuffix,rfl⟩))
    · have paths := congrArg Address.fields (oldLeft.symm.trans oldRight)
      have same : leftSuffix = rightSuffix := List.append_cancel_left paths
      subst rightSuffix
      exact newLeft.trans newRight.symm

theorem Address.prefix_extension {ancestor descendant : Address} (included : ancestor.Prefix descendant) :
    ∃ suffix, descendant = { ancestor with fields := ancestor.fields ++ suffix } := by
  rcases included with ⟨root,generation,suffix,fields⟩
  exact ⟨suffix,by cases ancestor; cases descendant; simp_all⟩

/-- Every post-transfer resident has exactly an old resident shell and follows
the deterministic location change above. Modified ancestors retain their own
shell; residents in the moved subtree retain their complete contents. -/
theorem Transfers.resident_origin {program : RuntimeProgram} {before after : World} {authority source destination}
    (transfer : Transfers program before authority source destination after) {address : Address} {value : Value}
    (resident : after.Resident address value) :
    ∃ previous original, before.Resident previous original ∧ value.shell = original.shell ∧
      Address.TransferredTo source destination previous address := by
  have afterStored := World.resident_iff_stores.mp resident
  cases transfer with
  | move stored _ _ _ _ _ _ clear install =>
      by_cases inside : destination.Prefix address
      · obtain ⟨suffix,equal⟩ := Address.prefix_extension inside
        have read := World.write_read_inside install suffix
        have same : _ = some value := afterStored
        rw [equal,read] at same
        refine ⟨{ source with fields := source.fields ++ suffix },value,?_,rfl,Or.inr ⟨suffix,rfl,equal⟩⟩
        apply World.resident_iff_stores.mpr
        change before.read { source with fields := source.fields ++ suffix } = some value
        rw [World.read_append,stored]
        exact same
      · have middleShell := World.write_read_shell install inside
        change after.read address = some value at afterStored
        rw [afterStored] at middleShell
        obtain ⟨middle,middleStored,middleEq⟩ := Option.map_eq_some_iff.mp middleShell.symm
        have outside : ¬ source.Prefix address := by
          intro included
          obtain ⟨suffix,equal⟩ := Address.prefix_extension included
          have absent := World.write_read_inside clear suffix
          rw [← equal,middleStored] at absent
          cases absent
        have oldShell := World.write_read_shell clear outside
        rw [middleStored] at oldShell
        obtain ⟨original,oldStored,oldEq⟩ := Option.map_eq_some_iff.mp oldShell.symm
        exact ⟨address,original,World.resident_iff_stores.mpr oldStored,middleEq.symm.trans oldEq.symm,Or.inl ⟨rfl,outside⟩⟩

theorem Transfers.owner_unique {program : RuntimeProgram} {before after : World} {authority source destination}
    (valid : before.WellFormed) (transfer : Transfers program before authority source destination after) :
    ∀ a b left right, after.Resident a left → after.Resident b right → left.owner = right.owner → a = b := by
  intro a b left right leftStored rightStored same
  obtain ⟨oldA,oldLeft,first,leftShell,leftMove⟩ := transfer.resident_origin leftStored
  obtain ⟨oldB,oldRight,second,rightShell,rightMove⟩ := transfer.resident_origin rightStored
  have leftOwner : left.owner = oldLeft.owner := by
    simpa [Value.shell,Value.withFields,Value.owner] using congrArg Value.owner leftShell
  have rightOwner : right.owner = oldRight.owner := by
    simpa [Value.shell,Value.withFields,Value.owner] using congrArg Value.owner rightShell
  have oldSame := valid.2.2.2.2.2.2.2.1 oldA oldB oldLeft oldRight first second (leftOwner.symm.trans (same.trans rightOwner))
  subst oldB
  exact leftMove.functional rightMove

theorem Table.Unique.set {α : Type} {table : Table α} (unique : table.Unique) (id : Identity) (value : α) :
    (table.set id value).Unique := by
  change (id :: (table.erase id).map Prod.fst).Nodup
  apply List.nodup_cons.mpr
  constructor
  · intro member
    obtain ⟨entry,inTable,same⟩ := List.mem_map.mp member
    have different := (List.mem_filter.mp inTable).2
    simp [same] at different
  · exact unique.sublist ((List.filter_sublist (p := fun entry : Identity × α => entry.1 != id)).map Prod.fst)

theorem World.write_rest {before after : World} {address : Address} {replacement : Option Value}
    (written : before.write address replacement = some after) : after = { before with roots := after.roots } := by
  obtain ⟨_,_,_,rfl⟩ := World.write_value_update written
  rfl

theorem World.write_canEndStorage {before after : World} {address : Address} {replacement : Option Value} {id : Identity}
    (written : before.write address replacement = some after) (safe : CanEndStorage before id) :
    CanEndStorage after id := by
  have loans := congrArg World.loans (World.write_rest written)
  have availability := congrArg World.availability (World.write_rest written)
  apply safe.sameHomes (after := after) ?_ loans availability
  simpa [Option.map_map,Function.comp_def,Root.location] using
    congrArg (Option.map Root.home) (World.write_locations written id)

theorem Transfers.rest {program : RuntimeProgram} {before after : World} {authority source destination}
    (transfer : Transfers program before authority source destination after) : after = { before with roots := after.roots } := by
  cases transfer with
  | move _ _ _ _ _ _ _ clear install =>
      have first := World.write_rest clear
      have last := World.write_rest install
      conv => lhs; rw [last,first]

theorem World.write_unique_roots {before after : World} {address : Address} {replacement : Option Value}
    (unique : before.roots.Unique) (written : before.write address replacement = some after) : after.roots.Unique := by
  obtain ⟨_,_,_,rfl⟩ := World.write_value_update written
  exact unique.set _ _

theorem Transfers.unique_roots {program : RuntimeProgram} {before after : World} {authority source destination}
    (unique : before.roots.Unique) (transfer : Transfers program before authority source destination after) : after.roots.Unique := by
  cases transfer with
  | move _ _ _ _ _ _ _ clear install => exact World.write_unique_roots (World.write_unique_roots unique clear) install

theorem Root.of_location_eq {before after : Root} (same : after.location = before.location) :
    after = { before with value := after.value } := by
  cases before
  cases after
  simp_all [Root.location]

theorem World.root_origin {before after : World} {id : Identity} {root : Root}
    (locations : ∀ id, (after.roots.get id).map Root.location = (before.roots.get id).map Root.location)
    (found : after.roots.get id = some root) :
    ∃ original, before.roots.get id = some original ∧ root = { original with value := root.value } := by
  have same := locations id
  rw [found] at same
  obtain ⟨original,selected,equal⟩ := Option.map_eq_some_iff.mp same.symm
  exact ⟨original,selected,Root.of_location_eq equal.symm⟩

theorem World.write_dead_root {before after : World} {address : Address} {replacement : Option Value}
    {id : Identity} {root : Root} (written : before.write address replacement = some after)
    (found : after.roots.get id = some root) (dead : root.live ≠ true) : before.roots.get id = some root := by
  obtain ⟨original,changed,selected,result⟩ := World.write_value_update written
  have live : original.live = true := (World.root_found (by
    unfold World.write at written
    cases atRoot : before.root address with
    | none => simp [atRoot] at written
    | some actual =>
        have actualFound := (World.root_found atRoot).1
        have equal := Option.some.inj (selected.symm.trans actualFound)
        rw [equal])).2.1
  rw [result] at found
  by_cases same : id = address.root
  · subst id
    have rootEq : root = { original with value := changed } := by simpa [Table.get_set] using found.symm
    exact False.elim (dead (rootEq ▸ live))
  · simpa [Table.get_set_other _ _ _ _ same] using found

theorem Transfers.dead_root {program : RuntimeProgram} {before after : World} {authority source destination}
    {id : Identity} {root : Root} (transfer : Transfers program before authority source destination after)
    (found : after.roots.get id = some root) (dead : root.live ≠ true) : before.roots.get id = some root := by
  cases transfer with
  | move _ _ _ _ _ _ _ clear install => exact World.write_dead_root clear (World.write_dead_root install found dead) dead

theorem AncestorLoan.transport {before after : World} {ancestor child : Identity}
    (loans : after.loans = before.loans) (related : AncestorLoan before ancestor child) : AncestorLoan after ancestor child := by
  induction related with
  | refl => exact .refl
  | parent found parent _ ih => exact .parent (by simpa [loans] using found) parent ih

theorem LoanPermission.transport {before after : World} {identity : Identity} {access : Access} {address : Address}
    (loans : after.loans = before.loans) (permission : LoanPermission before identity access address) :
    LoanPermission after identity access address := by
  obtain ⟨active,found,live,root,generation,path,mode,allowed,guards,dependent⟩ := permission
  refine ⟨active,by simpa only [loans] using found,live,root,generation,path,mode,?_,
    by simpa only [loans] using guards,by simpa only [loans] using dependent⟩
  intro other loan found live different overlap conflict
  exact AncestorLoan.transport loans
    (allowed other loan (by simpa only [loans] using found) live different overlap conflict)

theorem Permitted.transport {before after : World} {authority : Authority} {access : Access} {address : Address}
    (locations : ∀ id, (after.roots.get id).map Root.location = (before.roots.get id).map Root.location)
    (loans : after.loans = before.loans) (permission : Permitted before authority access address) :
    Permitted after authority access address := by
  have rootExists : ∃ root, before.root address = some root := by
    cases authority <;> exact permission.1
  obtain ⟨root,selected⟩ := rootExists
  obtain ⟨changed,found,_⟩ := World.root_transport locations selected
  induction authority with
  | owner => exact ⟨⟨changed,found⟩,by simpa only [loans] using permission.2⟩
  | loan id => exact ⟨⟨changed,found⟩,permission.2.transport loans⟩
  | shared backing ih => exact ⟨⟨changed,found⟩,permission.2.1,ih permission.2.2⟩
  | guarded backing carrier ih =>
      obtain ⟨loan,selected,guard⟩ := permission.2.2
      exact ⟨⟨changed,found⟩,ih permission.2.1,loan,by simpa only [loans] using selected,guard.transport loans⟩

theorem Transfers.wellFormed {program : RuntimeProgram} {before after : World} {authority source destination}
    (valid : before.WellFormed) (transfer : Transfers program before authority source destination after) : after.WellFormed := by
  have rest := transfer.rest
  have loansEq := congrArg World.loans rest
  have proofEq := congrArg World.availability rest
  have regionsEq := congrArg World.liveRegions rest
  have rootBound := congrArg World.nextRoot rest
  have ownerBound := congrArg World.nextOwner rest
  have loanBound := congrArg World.nextLoan rest
  have regionBound := congrArg World.nextRegion rest
  have proofBound := congrArg World.nextProof rest
  have rootsUnique := transfer.unique_roots valid.1
  have ownersUnique := transfer.owner_unique valid
  have parents := transfer.loanParents (World.loanParents valid)
  have located := transfer.liveLoanLocations valid
  have guards : after.LoanGuards := by simpa only [World.LoanGuards,loansEq] using World.loanGuards valid
  have kinds : after.LoanKinds := by simpa only [World.LoanKinds,loansEq] using World.loanKinds valid
  rcases valid with ⟨_,loansUnique,proofsUnique,regionsUnique,proofs,packs,owners,_,roots,regions,bases,ranges,loans,references,overlaps,_,_,_⟩
  refine ⟨rootsUnique,?_,?_,?_,?_,?_,?_,ownersUnique,?_,?_,?_,?_,?_,?_,?_,parents,located,guards,kinds⟩
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
    obtain ⟨_,afterRoot,_⟩ := World.root_transport transfer.locations selected
    simp [afterRoot]
  · intro address value pack resident head
    obtain ⟨previous,original,oldResident,shell,_⟩ := transfer.resident_origin resident
    have oldHead : original.head = .bindings pack := by
      have same : value.head = original.head := by simpa [Value.shell,Value.withFields,Value.head] using congrArg Value.head shell
      exact same.symm.trans head
    have arity : value.fields.length = original.fields.length := by
      simpa [Value.shell,Value.withFields,Value.fields] using congrArg (fun value => value.fields.length) shell
    simpa only [proofBound,regionsEq,ownerBound,arity] using packs previous original pack oldResident oldHead
  · intro address value resident
    obtain ⟨previous,original,oldResident,shell,_⟩ := transfer.resident_origin resident
    have owner : value.owner = original.owner := by simpa [Value.shell,Value.withFields,Value.owner] using congrArg Value.owner shell
    simpa only [ownerBound,owner] using owners previous original oldResident
  · intro id root found
    obtain ⟨original,oldFound,same⟩ := World.root_origin transfer.locations found
    rw [same]
    simpa only [rootBound,regionsEq] using roots id original oldFound
  · simpa only [regionsEq,regionBound] using regions
  · intro id root found live
    obtain ⟨original,oldFound,same⟩ := World.root_origin transfer.locations found
    have oldLive : original.live = true := by rw [same] at live; exact live
    rw [same]
    exact bases id original oldFound oldLive
  · intro a b left right leftFound rightFound different leftLive rightLive
    obtain ⟨oldLeft,oldFirst,leftEq⟩ := World.root_origin transfer.locations leftFound
    obtain ⟨oldRight,oldSecond,rightEq⟩ := World.root_origin transfer.locations rightFound
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
    obtain ⟨_,afterRoot,_⟩ := World.root_transport transfer.locations selected
    simp [afterRoot]
  · intro address value id resident head
    obtain ⟨previous,original,oldResident,shell,_⟩ := transfer.resident_origin resident
    have same : value.head = original.head := by simpa [Value.shell,Value.withFields,Value.head] using congrArg Value.head shell
    obtain ⟨loan,found,live⟩ := references previous original id oldResident (same.symm.trans head)
    exact ⟨loan,by simpa only [loansEq] using found,live⟩
  · intro a b left right leftFound rightFound leftLive rightLive overlap unique
    have oldFirst : before.loans.get a = some left := by simpa only [loansEq] using leftFound
    have oldSecond : before.loans.get b = some right := by simpa only [loansEq] using rightFound
    rcases overlaps a b left right oldFirst oldSecond leftLive rightLive overlap unique with ancestor | ancestor
    · exact Or.inl (ancestor.transport transfer.loans)
    · exact Or.inr (ancestor.transport transfer.loans)

/-- Region generativity is a property of stored types, including vacant and
retired roots. A storage write changes values, never this root type contract. -/
theorem World.root_regions_transport {before after : World}
    (supported : ∀ id root, before.roots.get id = some root → root.type.RuntimeRegionsBelow before.nextRegion)
    (locations : ∀ id, (after.roots.get id).map Root.location = (before.roots.get id).map Root.location)
    (bound : before.nextRegion ≤ after.nextRegion) :
    ∀ id root, after.roots.get id = some root → root.type.RuntimeRegionsBelow after.nextRegion := by
  intro id root found
  obtain ⟨original,selected,same⟩ := World.root_origin locations found
  rw [same]
  exact (supported id original selected).mono bound

theorem Transfers.worldTyped {program : Kernel.Program} {before after : World} {authority source destination}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (transfer : Transfers program before authority source destination after) : Typing.WorldTyped program after := by
  obtain ⟨residents,roots⟩ := transfer.typed_residents valid inventory typed
  refine ⟨transfer.wellFormed typed.1,residents,?_,?_⟩
  · intro id root value found contents
    by_cases live : root.live = true
    · exact roots id root value found live contents
    · exact typed.2.2.1 id root value (transfer.dead_root found live) contents
  · apply World.root_regions_transport typed.2.2.2 transfer.locations
    have same := congrArg World.nextRegion transfer.rest
    exact Nat.le_of_eq same.symm

end Glorious.Language
