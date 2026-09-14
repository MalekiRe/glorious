import GloriousLanguage.HandoffAccess
import GloriousLanguage.TransferPreservation

/-! Snapshot preservation derives its invariants from the actual relocation.
No safety postcondition or resource-admission premise is used by these proofs. -/
namespace Glorious.Language

theorem Table.get_append_left {α : Type} {left right : Table α} {id : Identity} {value : α}
    (found : left.get id = some value) : (left ++ right).get id = some value := by
  induction left with
  | nil => simp [Table.get] at found
  | cons entry rest ih =>
      rcases entry with ⟨key,item⟩
      by_cases same : key = id
      · subst key
        simpa [Table.get] using found
      · simpa [Table.get,same] using ih (by simpa [Table.get,same] using found)

theorem Table.Unique.get_of_mem {α : Type} {table : Table α} {id : Identity} {value : α}
    (unique : table.Unique) (member : (id,value) ∈ table) : table.get id = some value := by
  induction table with
  | nil => simp at member
  | cons entry rest ih =>
      rcases entry with ⟨key,item⟩
      have separate := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with equal | later
      · cases equal
        simp [Table.get]
      · have different : key ≠ id := by
          intro same
          exact separate.1 (same ▸ List.mem_map.mpr ⟨(id,value),later,rfl⟩)
        simpa [Table.get,different] using ih separate.2 later

theorem Table.Unique.append_shift {α : Type} {table : Table α} {base : Nat}
    {selected : Identity × α → Bool} {transform : Identity × α → Identity × α}
    (unique : table.Unique) (bounds : ∀ entry ∈ table, entry.1 < base)
    (shifted : ∀ entry ∈ table.filter selected, (transform entry).1 = base + entry.1) :
    (table ++ (table.filter selected).map transform).Unique := by
  have original : (table.map Prod.fst).Nodup := unique
  have selectedUnique : ((table.filter selected).map Prod.fst).Nodup :=
    original.sublist ((List.filter_sublist).map Prod.fst)
  have keys : ((table.filter selected).map transform).map Prod.fst =
      ((table.filter selected).map Prod.fst).map (base + ·) := by
    simp only [List.map_map]
    exact List.map_congr_left shifted
  change ((table ++ (table.filter selected).map transform).map Prod.fst).Nodup
  rw [List.map_append,keys]
  refine List.nodup_append.mpr ⟨original,?_,?_⟩
  · exact List.pairwise_map.mpr (selectedUnique.imp (fun different same => different (Nat.add_left_cancel same)))
  · intro old inOld fresh inFresh same
    obtain ⟨entry,member,atOld⟩ := List.mem_map.mp inOld
    obtain ⟨previous,_,atFresh⟩ := List.mem_map.mp inFresh
    have bound := bounds entry member
    have oldLess : old < base := atOld ▸ bound
    have freshGe : base ≤ fresh := by rw [← atFresh]; exact Nat.le_add_right _ _
    exact (Nat.not_lt_of_ge freshGe) (same ▸ oldLess)

theorem World.reserved_root_bound {world : World} {originBound : Identity}
    (well : world.WellFormedWithOrigins originBound) {id : Identity} {available : Availability}
    {place : ResolvedPlace} (found : world.availability.get id = some available)
    (active : available.active = true) (member : place ∈ available.reserved) :
    place.address.root < world.nextRoot := by
  obtain ⟨root,selected⟩ := Option.isSome_iff_exists.mp
    (((well.2.2.2.2.1 id available found).2.2.2.1 active).2 place member)
  exact World.root_bound well (World.root_found selected).1

theorem World.region_bound {world : World} (valid : world.WellFormed) {region : Identity}
    (member : region ∈ world.liveRegions) : region < world.nextRegion :=
  valid.2.2.2.2.2.2.2.2.2.1 region member

theorem AncestorLoan.trans {world : World} {first middle last : Identity}
    (left : AncestorLoan world first middle) (right : AncestorLoan world middle last) : AncestorLoan world first last := by
  induction right with
  | refl => exact left
  | parent found parent _ ih => exact .parent found parent ih

theorem AncestorLoan.weaken {before after : World} {ancestor child : Identity}
    (lookup : ∀ id loan, before.loans.get id = some loan → after.loans.get id = some loan)
    (related : AncestorLoan before ancestor child) : AncestorLoan after ancestor child := by
  induction related with
  | refl => exact .refl
  | parent found parent _ ih => exact .parent (lookup _ _ found) parent ih

theorem AncestorLoan.unique_ancestor {world : World} {ancestor descendant : Identity} {first last : Loan}
    (parents : world.LoanParents) (ancestry : AncestorLoan world ancestor descendant)
    (foundFirst : world.loans.get ancestor = some first) (foundLast : world.loans.get descendant = some last)
    (unique : last.mode = .unique) : first.mode = .unique := by
  induction ancestry generalizing last with
  | refl =>
      have same := Option.some.inj (foundFirst.symm.trans foundLast)
      exact same ▸ unique
  | @parent parent child loan found selected _ ih =>
      have same := Option.some.inj (found.symm.trans foundLast)
      subst last
      obtain ⟨middle,located,_,_,mode,_⟩ := parents child loan parent found selected
      exact ih located (mode unique)


namespace Execution

theorem Relocation.values_length (map : Relocation) (fields : List (Option Value)) :
    (map.values fields).length = fields.length := by
  induction fields with
  | nil => rfl
  | cons field rest ih => cases field <;> simp [Relocation.values,ih]

theorem Relocation.value_owner (map : Relocation) (value : Value) :
    (map.value value).owner = map.ownerBase + value.owner := by cases value; rfl

theorem Relocation.value_type (map : Relocation) (value : Value) : (map.value value).type = map.term value.type := by
  cases value
  simp only [Relocation.value,Value.type]

theorem Relocation.value_fields_length (map : Relocation) (value : Value) :
    (map.value value).fields.length = value.fields.length := by
  cases value
  exact map.values_length _

theorem Relocation.values_get (map : Relocation) (fields : List (Option Value)) (index : Nat) :
    (map.values fields)[index]? = (fields[index]?).map (Option.map map.value) := by
  induction fields generalizing index with
  | nil => simp [Relocation.values]
  | cons field rest ih => cases index <;> cases field <;> simp [Relocation.values,ih]

theorem Relocation.value_atPath (map : Relocation) (value : Value) (path : List Nat) :
    (map.value value).atPath path = (value.atPath path).map map.value := by
  induction path generalizing value with
  | nil => rfl
  | cons index path ih =>
      cases value with
      | resident owner type head live fields =>
          change (map.values fields)[index]?.join >>= (fun child => child.atPath path) = _
          rw [map.values_get]
          cases selected : fields[index]? with
          | none => simp [Value.atPath,Value.fields,selected]
          | some field => cases field with
            | none => simp [Value.atPath,Value.fields,selected]
            | some child => simpa [Value.atPath,Value.fields,selected] using ih child

theorem SnapshotMap.unique_roots {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map) (homes : Table Home) :
    (map.copyWorld before.world homes).roots.Unique := by
  apply Table.Unique.append_shift valid.1 (base := map.rootBase)
  · intro entry member
    rw [selected.rootBase]
    exact World.root_bound valid (valid.1.get_of_mem member)
  · intro entry member
    have included := (List.mem_filter.mp member).2
    simp only [decide_eq_true_eq] at included
    simp [Relocation.root,relocateId,included]

theorem SnapshotMap.unique_loans {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map) (homes : Table Home) :
    (map.copyWorld before.world homes).loans.Unique := by
  apply Table.Unique.append_shift valid.2.1 (base := map.loanBase)
  · intro entry member
    rw [selected.loanBase]
    exact World.loanBounds valid (valid.2.1.get_of_mem member)
  · intro entry member
    have included := (List.mem_filter.mp member).2
    simp only [decide_eq_true_eq] at included
    simp [Relocation.loan,relocateId,included]

theorem Relocation.old_root {map : Relocation} {world : World} {homes : Table Home} {id : Identity} {root : Root}
    (found : world.roots.get id = some root) : (map.copyWorld world homes).roots.get id = some root :=
  Table.get_append_left found

theorem Relocation.old_loan {map : Relocation} {world : World} {homes : Table Home} {id : Identity} {loan : Loan}
    (found : world.loans.get id = some loan) : (map.copyWorld world homes).loans.get id = some loan :=
  Table.get_append_left found

theorem Relocation.root_origin {map : Relocation} {world : World} {homes : Table Home} {id : Identity} {root : Root}
    (unique : world.roots.Unique) (found : (map.copyWorld world homes).roots.get id = some root) :
    world.roots.get id = some root ∨ ∃ old original, world.roots.get old = some original ∧ old ∈ map.roots ∧
      id = map.root old ∧ root = map.rootValue old { original with home := (homes.get old).getD original.home } := by
  have member := Table.mem_of_get found
  rcases List.mem_append.mp member with old | copied
  · exact Or.inl (unique.get_of_mem old)
  · obtain ⟨⟨old,original⟩,included,equal⟩ := List.mem_map.mp copied
    obtain ⟨member,inRoots⟩ := List.mem_filter.mp included
    have pair := Prod.mk.inj equal
    exact Or.inr ⟨old,original,unique.get_of_mem member,by simpa using inRoots,pair.1.symm,pair.2.symm⟩

theorem Relocation.loan_origin {map : Relocation} {world : World} {homes : Table Home} {id : Identity} {loan : Loan}
    (unique : world.loans.Unique) (found : (map.copyWorld world homes).loans.get id = some loan) :
    world.loans.get id = some loan ∨ ∃ old original, world.loans.get old = some original ∧ old ∈ map.loans ∧
      id = map.loan old ∧ loan = map.loanValue original := by
  have member := Table.mem_of_get found
  rcases List.mem_append.mp member with old | copied
  · exact Or.inl (unique.get_of_mem old)
  · obtain ⟨⟨old,original⟩,included,equal⟩ := List.mem_map.mp copied
    obtain ⟨member,inLoans⟩ := List.mem_filter.mp included
    have pair := Prod.mk.inj equal
    exact Or.inr ⟨old,original,unique.get_of_mem member,by simpa using inLoans,pair.1.symm,pair.2.symm⟩

theorem SnapshotMap.copied_root {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    {homes : Table Home} {id : Identity} {root : Root}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (found : before.world.roots.get id = some root) (included : id ∈ map.roots) :
    (map.copyWorld before.world homes).roots.get (map.root id) =
      some (map.rootValue id { root with home := (homes.get id).getD root.home }) := by
  apply (selected.unique_roots valid homes).get_of_mem
  apply List.mem_append_right
  apply List.mem_map.mpr
  exact ⟨(id,root),List.mem_filter.mpr ⟨Table.mem_of_get found,by simpa using included⟩,rfl⟩

theorem SnapshotMap.copied_loan {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    {homes : Table Home} {id : Identity} {loan : Loan}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (found : before.world.loans.get id = some loan) (included : id ∈ map.loans) :
    (map.copyWorld before.world homes).loans.get (map.loan id) = some (map.loanValue loan) := by
  apply (selected.unique_loans valid homes).get_of_mem
  apply List.mem_append_right
  apply List.mem_map.mpr
  exact ⟨(id,loan),List.mem_filter.mpr ⟨Table.mem_of_get found,by simpa using included⟩,rfl⟩

theorem Relocation.old_resident {map : Relocation} {world : World} {homes : Table Home} {address : Address} {value : Value}
    (resident : world.Resident address value) : (map.copyWorld world homes).Resident address value := by
  obtain ⟨root,whole,found,live,generation,contents,inside⟩ := resident
  exact ⟨root,whole,Relocation.old_root found,live,generation,contents,inside⟩

theorem SnapshotMap.copied_resident {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    {homes : Table Home} {address : Address} {value : Value}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (resident : before.world.Resident address value) (included : address.root ∈ map.roots) :
    (map.copyWorld before.world homes).Resident (map.address address) (map.value value) := by
  obtain ⟨root,whole,found,live,generation,contents,inside⟩ := resident
  refine ⟨map.rootValue address.root { root with home := (homes.get address.root).getD root.home },map.value whole,
    selected.copied_root valid found included,live,generation,?_,?_⟩
  · simp [Relocation.rootValue,contents]
  · apply ResidentAt.iff_atPath.mpr
    rw [Relocation.address,Relocation.value_atPath,ResidentAt.iff_atPath.mp inside]
    rfl

theorem Relocation.resident_origin {map : Relocation} {world : World} {homes : Table Home} {address : Address} {value : Value}
    (unique : world.roots.Unique) (resident : (map.copyWorld world homes).Resident address value) :
    world.Resident address value ∨ ∃ previous original, previous.root ∈ map.roots ∧ world.Resident previous original ∧
      address = map.address previous ∧ value = map.value original := by
  rcases address with ⟨id,generation,path⟩
  obtain ⟨root,whole,found,live,generationEq,contents,inside⟩ := resident
  rcases Relocation.root_origin unique found with old | ⟨old,original,oldFound,included,idEq,rootEq⟩
  · exact Or.inl ⟨root,whole,old,live,generationEq,contents,inside⟩
  · subst root
    change id = map.root old at idEq
    subst id
    obtain ⟨oldWhole,oldContents,equal⟩ := Option.map_eq_some_iff.mp contents
    subst whole
    have atPath := ResidentAt.iff_atPath.mp inside
    rw [Relocation.value_atPath] at atPath
    obtain ⟨oldValue,oldPath,valueEq⟩ := Option.map_eq_some_iff.mp atPath
    exact Or.inr ⟨⟨old,generation,path⟩,oldValue,included,
      ⟨original,oldWhole,oldFound,live,generationEq,oldContents,ResidentAt.iff_atPath.mpr oldPath⟩,rfl,valueEq.symm⟩

theorem Relocation.old_selected_root {map : Relocation} {world : World} {homes : Table Home} {address : Address} {root : Root}
    (selected : world.root address = some root) : (map.copyWorld world homes).root address = some root := by
  obtain ⟨found,live,generation⟩ := World.root_found selected
  simp [World.root,Relocation.old_root (map := map) (homes := homes) found,live,generation]

theorem SnapshotMap.copied_selected_root {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    {homes : Table Home} {address : Address} {root : Root}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (found : before.world.root address = some root) (included : address.root ∈ map.roots) :
    (map.copyWorld before.world homes).root (map.address address) =
      some (map.rootValue address.root { root with home := (homes.get address.root).getD root.home }) := by
  obtain ⟨present,live,generation⟩ := World.root_found found
  simp [World.root,Relocation.address,selected.copied_root valid present included,Relocation.rootValue,live,generation]

theorem Relocation.region_live {map : Relocation} {world : World} {homes : Table Home} {region : Identity}
    (live : region ∈ world.liveRegions) : map.region region ∈ (map.copyWorld world homes).liveRegions := by
  by_cases selected : region ∈ map.regions
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨region,selected,rfl⟩)
  · simpa [Relocation.copyWorld,Relocation.region,relocateId,selected] using Or.inl live

theorem SnapshotMap.unique_regions {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (distinct : map.regions.Nodup) (homes : Table Home) : (map.copyWorld before.world homes).liveRegions.Nodup := by
  have shifted : map.regions.map map.region = map.regions.map (map.regionBase + ·) := by
    apply List.map_congr_left
    intro region included
    simp [Relocation.region,relocateId,included]
  change (before.world.liveRegions ++ map.regions.map map.region).Nodup
  rw [shifted]
  refine List.nodup_append.mpr ⟨valid.2.2.2.1,?_,?_⟩
  · exact List.pairwise_map.mpr (distinct.imp (fun different same => different (Nat.add_left_cancel same)))
  · intro old member fresh copied same
    obtain ⟨region,_,equal⟩ := List.mem_map.mp copied
    have bound := World.region_bound valid member
    rw [same,← equal,selected.regionBase] at bound
    exact (Nat.not_lt_of_ge (Nat.le_add_right _ _)) bound

theorem relocateId_bound {selected : List Identity} {base id limit : Identity}
    (bound : id < limit) : relocateId selected base id < base + limit := by
  unfold relocateId
  split
  · exact Nat.add_lt_add_left bound base
  · exact Nat.lt_of_lt_of_le bound (Nat.le_add_left _ _)

theorem SnapshotMap.selected_loan {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    {id : Identity} {loan : Loan} (selected : SnapshotMap program before suspension map)
    (included : id ∈ map.loans) (found : before.world.loans.get id = some loan) :
    loan.live = true ∧ loan.mode = .shared := by
  obtain ⟨original,present,live,mode⟩ := ((selected.loans id).mp included).record
  have same := Option.some.inj (present.symm.trans found)
  subst original
  exact ⟨live,mode⟩

theorem SnapshotMap.reference_loan {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    {address : Address} {value : Value} {id : Identity} {loan : Loan}
    (selected : SnapshotMap program before suspension map) (included : address.root ∈ map.roots)
    (resident : before.world.Resident address value) (head : value.head = .reference id)
    (found : before.world.loans.get id = some loan) (live : loan.live = true) (shared : loan.mode = .shared) :
    id ∈ map.loans :=
  (selected.loans id).mpr (.reference found live shared included resident head)

theorem SnapshotMap.owner_unique {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map) (homes : Table Home) :
    ∀ a b left right, (map.copyWorld before.world homes).Resident a left →
      (map.copyWorld before.world homes).Resident b right → left.owner = right.owner → a = b := by
  intro a b left right first second same
  have unique := valid.2.2.2.2.2.2.2.1
  rcases Relocation.resident_origin valid.1 first with oldLeft | ⟨oldA,originalLeft,_,oldLeft,rfl,rfl⟩
  · rcases Relocation.resident_origin valid.1 second with oldRight | ⟨oldB,originalRight,_,oldRight,rfl,rfl⟩
    · exact unique a b left right oldLeft oldRight same
    · have bound := World.owner_bound valid oldLeft
      rw [map.value_owner,selected.ownerBase] at same
      exact False.elim ((Nat.not_lt_of_ge (Nat.le_add_right _ _)) (same ▸ bound))
  · rcases Relocation.resident_origin valid.1 second with oldRight | ⟨oldB,originalRight,_,oldRight,rfl,rfl⟩
    · have bound := World.owner_bound valid oldRight
      rw [map.value_owner,selected.ownerBase] at same
      exact False.elim ((Nat.not_lt_of_ge (Nat.le_add_right _ _)) (same.symm ▸ bound))
    · rw [map.value_owner,map.value_owner] at same
      have oldSame := Nat.add_left_cancel same
      have addressEq := unique oldA oldB originalLeft originalRight oldLeft oldRight oldSame
      exact congrArg map.address addressEq

theorem Relocation.value_fields_get (map : Relocation) (value : Value) (index : Nat) :
    (map.value value).fields[index]? = (value.fields[index]?).map (Option.map map.value) := by
  cases value
  exact map.values_get _ _

theorem Relocation.old_located {map : Relocation} {world : World} {homes : Table Home} {address : Address}
    (located : world.Located address) : (map.copyWorld world homes).Located address := by
  rcases located with ⟨value,stored⟩ | ⟨root,selected,vacant⟩
  · exact Or.inl ⟨value,World.resident_iff_stores.mp (Relocation.old_resident (World.resident_iff_stores.mpr stored))⟩
  · exact Or.inr ⟨root,Relocation.old_selected_root selected,vacant⟩

theorem SnapshotMap.copied_located {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    {homes : Table Home} {address : Address}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (located : before.world.Located address) (included : address.root ∈ map.roots) :
    (map.copyWorld before.world homes).Located (map.address address) := by
  rcases located with ⟨value,stored⟩ | ⟨root,found,⟨fields,empty⟩ | ⟨parent,index,whole,fields,contents,container,path,empty⟩⟩
  · exact Or.inl ⟨map.value value,World.resident_iff_stores.mp
      (selected.copied_resident valid (World.resident_iff_stores.mpr stored) included)⟩
  · refine Or.inr ⟨_,selected.copied_selected_root valid found included,Or.inl ⟨fields,?_⟩⟩
    simp [Relocation.rootValue,empty]
  · refine Or.inr ⟨_,selected.copied_selected_root valid found included,
      Or.inr ⟨parent,index,map.value whole,fields,?_,map.value container,?_,?_⟩⟩
    · simp [Relocation.rootValue,contents]
    · rw [map.value_atPath,path]; rfl
    · rw [map.value_fields_get,empty]; rfl

theorem Relocation.address_unselected {map : Relocation} {address : Address} (outside : address.root ∉ map.roots) :
    map.address address = address := by
  cases address
  simp_all [Relocation.address,Relocation.root,relocateId]

theorem Relocation.address_prefix (map : Relocation) {ancestor child : Address} (included : ancestor.Prefix child) :
    (map.address ancestor).Prefix (map.address child) :=
  ⟨congrArg map.root included.1,included.2.1,included.2.2⟩

theorem SnapshotMap.parent_selected {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    {id parent : Identity} {loan ancestor : Loan} (selected : SnapshotMap program before suspension map)
    (included : id ∈ map.loans) (found : before.world.loans.get id = some loan) (parentEq : loan.parent = some parent)
    (parentFound : before.world.loans.get parent = some ancestor) (live : ancestor.live = true) (shared : ancestor.mode = .shared) :
    parent ∈ map.loans := by
  exact (selected.loans parent).mpr (.parent ((selected.loans id).mp included) found parentEq parentFound live shared)

theorem SnapshotMap.parent_address {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    {id parent : Identity} {loan ancestor : Loan} (selected : SnapshotMap program before suspension map)
    (replayable : Replayable program.toRuntimeProgram before.world suspension.roots)
    (included : id ∈ map.loans) (found : before.world.loans.get id = some loan) (parentEq : loan.parent = some parent)
    (parentFound : before.world.loans.get parent = some ancestor) (live : ancestor.live = true) (outside : parent ∉ map.loans) :
    map.address ancestor.referent = ancestor.referent := by
  apply Relocation.address_unselected
  intro root
  have shared := replayable.2.2.2 parent ancestor parentFound live (selected.roots ▸ root)
  exact outside (selected.parent_selected included found parentEq parentFound live shared)

theorem SnapshotMap.loan_parents {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (replayable : Replayable program.toRuntimeProgram before.world suspension.roots) (homes : Table Home) :
    (map.copyWorld before.world homes).LoanParents := by
  intro id loan parent found parentEq
  rcases Relocation.loan_origin valid.2.1 found with old | ⟨old,original,present,included,rfl,rfl⟩
  · obtain ⟨ancestor,parentFound,bound,contains,mode,live⟩ := World.loanParents valid id loan parent old parentEq
    exact ⟨ancestor,Relocation.old_loan parentFound,bound,contains,mode,live⟩
  · obtain ⟨oldParent,parentFound,parentMapped⟩ := Option.map_eq_some_iff.mp parentEq
    subst parent
    obtain ⟨ancestor,atParent,bound,contains,mode,live⟩ := World.loanParents valid old original oldParent present parentFound
    have parentLive := live (selected.selected_loan included present).1
    by_cases parentIncluded : oldParent ∈ map.loans
    · refine ⟨map.loanValue ancestor,selected.copied_loan valid atParent parentIncluded,?_,map.address_prefix contains,mode,live⟩
      simpa [Relocation.loan,relocateId,included,parentIncluded] using Nat.add_lt_add_left bound map.loanBase
    · have unchanged := selected.parent_address replayable included present parentFound atParent parentLive parentIncluded
      refine ⟨ancestor,?_,?_,?_,mode,live⟩
      · simpa [Relocation.loan,relocateId,parentIncluded] using Relocation.old_loan (map := map) (homes := homes) atParent
      · have parentBound := World.loanBounds valid atParent
        simpa [Relocation.loan,relocateId,included,parentIncluded,selected.loanBase] using
          Nat.lt_of_lt_of_le parentBound (Nat.le_add_right before.world.nextLoan old)
      · change ancestor.referent.Prefix (map.address original.referent)
        simpa [unchanged] using map.address_prefix contains

theorem SnapshotMap.live_loan_locations {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map) (homes : Table Home) :
    (map.copyWorld before.world homes).LiveLoanLocations := by
  intro id loan found live
  rcases Relocation.loan_origin valid.2.1 found with old | ⟨old,original,present,included,rfl,rfl⟩
  · exact Relocation.old_located (World.liveLoanLocations valid id loan old live)
  · have oldLocated := World.liveLoanLocations valid old original present live
    by_cases root : original.referent.root ∈ map.roots
    · exact selected.copied_located valid oldLocated root
    · simpa [Relocation.loanValue,Relocation.address_unselected root] using
        Relocation.old_located (map := map) (homes := homes) oldLocated

theorem SnapshotMap.loan_guards {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map) (homes : Table Home) :
    (map.copyWorld before.world homes).LoanGuards := by
  intro id loan guard found member
  rcases Relocation.loan_origin valid.2.1 found with old | ⟨old,original,present,included,rfl,rfl⟩
  · obtain ⟨carrier,atGuard,bound,live⟩ := World.loanGuards valid id loan guard old member
    exact ⟨carrier,Relocation.old_loan atGuard,bound,live⟩
  · obtain ⟨oldGuard,inGuards,rfl⟩ := List.mem_map.mp member
    obtain ⟨carrier,atGuard,bound,live⟩ := World.loanGuards valid old original oldGuard present inGuards
    by_cases copied : oldGuard ∈ map.loans
    · exact ⟨map.loanValue carrier,selected.copied_loan valid atGuard copied,
        by simpa [Relocation.loan,relocateId,included,copied] using Nat.add_lt_add_left bound map.loanBase,live⟩
    · exact ⟨carrier,by simpa [Relocation.loan,relocateId,copied] using
          Relocation.old_loan (map := map) (homes := homes) atGuard,
        by simpa [Relocation.loan,relocateId,included,copied,selected.loanBase] using
          Nat.lt_of_lt_of_le (World.loanBounds valid atGuard) (Nat.le_add_right before.world.nextLoan old),live⟩

theorem Relocation.loan_kind (map : Relocation) {loan : Loan} (valid : loan.KindValid) :
    (map.loanValue loan).KindValid := by
  simpa only [Loan.KindValid,LoanKind.Allows,Relocation.loanValue,Option.isSome_map] using valid

theorem Relocation.loan_kinds {world : World} {map : Relocation}
    (valid : world.WellFormed) (homes : Table Home) :
    (map.copyWorld world homes).LoanKinds := by
  intro id loan found
  rcases Relocation.loan_origin valid.2.1 found with old | ⟨old,original,present,_,rfl,rfl⟩
  · exact World.loanKinds valid id loan old
  · exact map.loan_kind (World.loanKinds valid old original present)

theorem Relocation.reference_origin {map : Relocation} {value : Value} {id : Identity}
    (head : (map.value value).head = .reference id) : ∃ previous, value.head = .reference previous ∧ id = map.loan previous := by
  cases value with
  | resident owner type original live fields =>
      cases original <;> simp [Relocation.value,Value.head] at head
      rename_i loan
      exact ⟨loan,rfl,head.symm⟩

/-- The relocated handle's loan has the relocated referent AND region, even
when the referent is external. Parent edges are preserved by `loan_parents`. -/
theorem SnapshotMap.reference_target {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    {homes : Table Home} {address : Address} {value : Value} {id : Identity} {loan : Loan}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (replayable : Replayable program.toRuntimeProgram before.world suspension.roots)
    (included : address.root ∈ map.roots) (resident : before.world.Resident address value)
    (head : value.head = .reference id) (found : before.world.loans.get id = some loan) (live : loan.live = true) :
    (map.copyWorld before.world homes).loans.get (map.loan id) = some (map.loanValue loan) ∧
      (map.loanValue loan).referent = map.address loan.referent ∧ (map.loanValue loan).region = map.region loan.region := by
  have shared := replayable.2.2.1 address value id loan (selected.roots ▸ included) resident head found
  exact ⟨selected.copied_loan valid found (selected.reference_loan included resident head found live shared),rfl,rfl⟩

theorem SnapshotMap.ancestor_external {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    {homes : Table Home} {ancestor child : Identity}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (outside : ancestor ∉ map.loans) (related : AncestorLoan before.world ancestor child) :
    AncestorLoan (map.copyWorld before.world homes) ancestor (map.loan child) := by
  induction related with
  | refl => simpa [Relocation.loan,relocateId,outside] using (AncestorLoan.refl (world := map.copyWorld before.world homes) (identity := ancestor))
  | @parent parent child loan found parentEq related ih =>
      by_cases included : child ∈ map.loans
      · exact .parent (selected.copied_loan valid found included) (by simp [Relocation.loanValue,parentEq]) ih
      · have original : AncestorLoan (map.copyWorld before.world homes) ancestor child :=
          (AncestorLoan.parent found parentEq related).weaken (fun _ _ => Relocation.old_loan)
        simpa [Relocation.loan,relocateId,included] using original

theorem SnapshotMap.external_unique {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    {homes : Table Home} {old copied : Identity} {external original : Loan}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (found : before.world.loans.get old = some external) (live : external.live = true) (unique : external.mode = .unique)
    (copyFound : before.world.loans.get copied = some original) (included : copied ∈ map.loans)
    (overlap : external.referent.Overlaps (map.address original.referent)) :
    AncestorLoan (map.copyWorld before.world homes) old (map.loan copied) := by
  have unchanged : map.address original.referent = original.referent := by
    apply Relocation.address_unselected
    intro relocated
    have bound := World.live_loan_root_bound valid found live
    have root : (map.address original.referent).root = before.world.nextRoot + original.referent.root := by
      simp [Relocation.address,Relocation.root,relocateId,relocated,selected.rootBase]
    rw [overlap.1,root] at bound
    exact (Nat.not_lt_of_ge (Nat.le_add_right _ _)) bound
  rw [unchanged] at overlap
  have copyFacts := selected.selected_loan included copyFound
  have compatible := valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 old copied external original found copyFound live copyFacts.1 overlap (Or.inl unique)
  rcases compatible with ancestor | ancestor
  · have outside : old ∉ map.loans := by
      intro member
      have shared := (selected.selected_loan member found).2
      cases shared.symm.trans unique
    exact selected.ancestor_external valid outside ancestor
  · have impossible := ancestor.unique_ancestor (World.loanParents valid) copyFound found unique
    cases copyFacts.2.symm.trans impossible

theorem SnapshotMap.loan_exclusivity {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map) (homes : Table Home) :
    ∀ a b left right, (map.copyWorld before.world homes).loans.get a = some left →
      (map.copyWorld before.world homes).loans.get b = some right → left.live = true → right.live = true →
      left.referent.Overlaps right.referent → left.mode = .unique ∨ right.mode = .unique →
      AncestorLoan (map.copyWorld before.world homes) a b ∨ AncestorLoan (map.copyWorld before.world homes) b a := by
  intro a b left right first second leftLive rightLive overlap unique
  rcases Relocation.loan_origin valid.2.1 first with oldLeft | ⟨oldA,originalLeft,presentLeft,leftIncluded,rfl,rfl⟩
  · rcases Relocation.loan_origin valid.2.1 second with oldRight | ⟨oldB,originalRight,presentRight,rightIncluded,rfl,rfl⟩
    · rcases valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a b left right oldLeft oldRight leftLive rightLive overlap unique with ancestor | ancestor
      · exact Or.inl (ancestor.weaken (fun _ _ => Relocation.old_loan))
      · exact Or.inr (ancestor.weaken (fun _ _ => Relocation.old_loan))
    · rcases unique with unique | impossible
      · exact Or.inl (selected.external_unique valid oldLeft leftLive unique presentRight rightIncluded overlap)
      · have shared := (selected.selected_loan rightIncluded presentRight).2
        change originalRight.mode = .unique at impossible
        cases shared.symm.trans impossible
  · rcases Relocation.loan_origin valid.2.1 second with oldRight | ⟨oldB,originalRight,presentRight,rightIncluded,rfl,rfl⟩
    · rcases unique with impossible | unique
      · have shared := (selected.selected_loan leftIncluded presentLeft).2
        change originalLeft.mode = .unique at impossible
        cases shared.symm.trans impossible
      · exact Or.inr (selected.external_unique valid oldRight rightLive unique presentLeft leftIncluded (Address.Overlaps.symm overlap))
    · have sharedLeft := (selected.selected_loan leftIncluded presentLeft).2
      have sharedRight := (selected.selected_loan rightIncluded presentRight).2
      rcases unique with impossible | impossible
      · change originalLeft.mode = .unique at impossible
        cases sharedLeft.symm.trans impossible
      · change originalRight.mode = .unique at impossible
        cases sharedRight.symm.trans impossible

theorem Relocation.bindings_origin {map : Relocation} {value : Value} {pack : BindingPack}
    (head : (map.value value).head = .bindings pack) :
    ∃ previous, value.head = .bindings previous ∧ pack = { previous.mapOrigins map.owner with region := map.region previous.region } := by
  cases value with
  | resident owner type original live fields =>
      cases original <;> simp [Relocation.value,Value.head] at head
      rename_i previous
      exact ⟨previous,rfl,head.symm⟩

theorem SnapshotMap.root_disjoint {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map) (homes : Table Home) :
    ∀ a b left right, (map.copyWorld before.world homes).roots.get a = some left →
      (map.copyWorld before.world homes).roots.get b = some right → a ≠ b → left.live = true → right.live = true →
      left.layout.size = 0 ∨ right.layout.size = 0 ∨
        left.base + left.layout.size ≤ right.base ∨ right.base + right.layout.size ≤ left.base := by
  intro a b left right first second different leftLive rightLive
  rcases Relocation.root_origin valid.1 first with oldLeft | ⟨oldA,originalLeft,presentLeft,leftIncluded,rfl,rfl⟩
  · rcases Relocation.root_origin valid.1 second with oldRight | ⟨oldB,originalRight,presentRight,rightIncluded,rfl,rfl⟩
    · exact valid.2.2.2.2.2.2.2.2.2.2.2.1 a b left right oldLeft oldRight different leftLive rightLive
    · obtain ⟨base,physical,_,_,_,disjoint⟩ := selected.physical oldB originalRight rightIncluded presentRight
      have apart := disjoint a left oldLeft leftLive
      simp only [Relocation.rootValue,physical,Option.getD_some]
      rcases apart with rightZero | leftZero | beforeLeft | afterLeft
      · exact Or.inr (Or.inl rightZero)
      · exact Or.inl leftZero
      · exact Or.inr (Or.inr (Or.inr beforeLeft))
      · exact Or.inr (Or.inr (Or.inl afterLeft))
  · rcases Relocation.root_origin valid.1 second with oldRight | ⟨oldB,originalRight,presentRight,rightIncluded,rfl,rfl⟩
    · obtain ⟨base,physical,_,_,_,disjoint⟩ := selected.physical oldA originalLeft leftIncluded presentLeft
      simpa [Relocation.rootValue,physical] using disjoint b right oldRight rightLive
    · obtain ⟨leftBase,leftPhysical,_⟩ := selected.physical oldA originalLeft leftIncluded presentLeft
      obtain ⟨rightBase,rightPhysical,_⟩ := selected.physical oldB originalRight rightIncluded presentRight
      have oldDifferent : oldA ≠ oldB := fun same => different (congrArg map.root same)
      have apart := selected.disjoint oldA oldB originalLeft originalRight leftBase rightBase
        leftIncluded rightIncluded oldDifferent presentLeft presentRight leftPhysical rightPhysical
      simpa [Relocation.rootValue,leftPhysical,rightPhysical] using apart

/-- General preservation for snapshot copying. Freshness, resident origins,
physical separation, regions and the full reborrow graph are all derived;
the copied world's well-formedness is not an admission premise. -/
theorem SnapshotMap.world_wellFormed {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (replayable : Replayable program.toRuntimeProgram before.world suspension.roots) (distinctRegions : map.regions.Nodup)
    (homes : Table Home) : (map.copyWorld before.world homes).WellFormed := by
  have rootUnique := selected.unique_roots valid homes
  have loanUnique := selected.unique_loans valid homes
  have regionUnique := selected.unique_regions valid distinctRegions homes
  have ownerUnique := selected.owner_unique valid homes
  have rootSeparate := selected.root_disjoint valid homes
  have loanSeparate := selected.loan_exclusivity valid homes
  have parents := selected.loan_parents valid replayable homes
  have locations := selected.live_loan_locations valid homes
  have guards := selected.loan_guards valid homes
  have kinds := Relocation.loan_kinds (map := map) valid homes
  have oldValid := valid
  rcases valid with ⟨_,_,proofUnique,_,proofs,packs,owners,_,roots,regions,bases,_,loans,references,_,_,_,_⟩
  refine ⟨rootUnique,loanUnique,proofUnique,regionUnique,?_,?_,?_,ownerUnique,?_,?_,?_,rootSeparate,?_,?_,loanSeparate,parents,locations,guards,kinds⟩
  · intro id available found
    obtain ⟨identity,bound,brand,active,recorded⟩ := proofs id available found
    refine ⟨identity,bound,brand,?_,fun place member =>
      (recorded place member).transport (fun _ loan found => ⟨loan,Relocation.old_loan found⟩)⟩
    intro live
    obtain ⟨region,reserved⟩ := active live
    refine ⟨List.mem_append_left _ region,?_⟩
    intro place member
    obtain ⟨root,atRoot⟩ := Option.isSome_iff_exists.mp (reserved place member)
    exact Option.isSome_iff_exists.mpr ⟨root,Relocation.old_selected_root atRoot⟩
  · intro address value pack resident head
    rcases Relocation.resident_origin oldValid.1 resident with original | ⟨old,valueOld,_,original,rfl,rfl⟩
    · obtain ⟨brand,region,arity,distinct,facts⟩ := packs address value pack original head
      refine ⟨brand,List.mem_append_left _ region,arity,distinct,?_⟩
      intro fact member
      exact Nat.lt_of_lt_of_le (facts fact member) (Nat.le_add_left _ _)
    · obtain ⟨packOld,oldHead,rfl⟩ := Relocation.bindings_origin head
      obtain ⟨brand,region,arity,distinct,facts⟩ := packs old valueOld packOld original oldHead
      refine ⟨brand,Relocation.region_live region,?_,distinct,?_⟩
      · simpa [BindingPack.mapOrigins,map.value_fields_length] using arity
      · intro fact member
        obtain ⟨oldFact,inOld,equal⟩ := List.mem_map.mp member
        subst fact
        exact relocateId_bound (facts oldFact inOld)
  · intro address value resident
    rcases Relocation.resident_origin oldValid.1 resident with original | ⟨old,valueOld,_,original,rfl,rfl⟩
    · exact Nat.lt_of_lt_of_le (owners address value original) (Nat.le_add_left _ _)
    · simpa [Relocation.copyWorld,map.value_owner] using Nat.add_lt_add_left (owners old valueOld original) map.ownerBase
  · intro id root found
    rcases Relocation.root_origin oldValid.1 found with original | ⟨old,rootOld,present,included,rfl,rfl⟩
    · obtain ⟨bound,region,layout,bytes,values⟩ := roots id root original
      exact ⟨Nat.lt_of_lt_of_le bound (Nat.le_add_left _ _),fun live => List.mem_append_left _ (region live),layout,bytes,values⟩
    · obtain ⟨bound,region,layout,bytes,values⟩ := roots old rootOld present
      exact ⟨relocateId_bound bound,fun live => Relocation.region_live (region live),layout,bytes,values⟩
  · intro region member
    rcases List.mem_append.mp member with old | copied
    · exact Nat.lt_of_lt_of_le (regions region old) (Nat.le_add_left _ _)
    · obtain ⟨previous,included,equal⟩ := List.mem_map.mp copied
      subst region
      exact relocateId_bound (regions previous (selected.liveRegions previous included))
  · intro id root found live
    rcases Relocation.root_origin oldValid.1 found with original | ⟨old,rootOld,present,included,rfl,rfl⟩
    · exact bases id root original live
    · obtain ⟨base,physical,positive,aligned,_⟩ := selected.physical old rootOld included present
      simpa [Relocation.rootValue,physical] using And.intro positive aligned
  · intro id loan found
    rcases Relocation.loan_origin oldValid.2.1 found with original | ⟨old,loanOld,present,included,rfl,rfl⟩
    · obtain ⟨identity,bound,active⟩ := loans id loan original
      refine ⟨identity,Nat.lt_of_lt_of_le bound (Nat.le_add_left _ _),?_⟩
      intro live
      obtain ⟨region,root⟩ := active live
      obtain ⟨root,atRoot⟩ := Option.isSome_iff_exists.mp root
      exact ⟨List.mem_append_left _ region,Option.isSome_iff_exists.mpr ⟨root,Relocation.old_selected_root atRoot⟩⟩
    · obtain ⟨identity,bound,active⟩ := loans old loanOld present
      refine ⟨congrArg map.loan identity,relocateId_bound bound,?_⟩
      intro live
      obtain ⟨region,root⟩ := active live
      refine ⟨Relocation.region_live region,?_⟩
      obtain ⟨root,atRoot⟩ := Option.isSome_iff_exists.mp root
      by_cases rootIncluded : loanOld.referent.root ∈ map.roots
      · exact Option.isSome_iff_exists.mpr ⟨_,selected.copied_selected_root oldValid atRoot rootIncluded⟩
      · change ((map.copyWorld before.world homes).root (map.address loanOld.referent)).isSome = true
        rw [Relocation.address_unselected rootIncluded]
        exact Option.isSome_iff_exists.mpr ⟨root,Relocation.old_selected_root atRoot⟩
  · intro address value id resident head
    rcases Relocation.resident_origin oldValid.1 resident with original | ⟨old,valueOld,included,original,rfl,rfl⟩
    · obtain ⟨loan,found,live⟩ := references address value id original head
      exact ⟨loan,Relocation.old_loan found,live⟩
    · obtain ⟨previous,oldHead,rfl⟩ := Relocation.reference_origin head
      obtain ⟨loan,found,live⟩ := references old valueOld previous original oldHead
      have target := selected.reference_target (homes := homes) oldValid replayable included original oldHead found live
      exact ⟨map.loanValue loan,target.1,live⟩

theorem CopiesSnapshot.wellFormed {program : Kernel.Program} {before after : State} {suspension : Suspension} {map : Relocation}
    (valid : before.world.WellFormed) (copied : CopiesSnapshot program before suspension map after) : after.world.WellFormed := by
  rw [copied.result]
  exact copied.relocation.world_wellFormed valid copied.replayable copied.regions suspension.homes

end Execution
end Glorious.Language
