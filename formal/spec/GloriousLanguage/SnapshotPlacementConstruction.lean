import GloriousLanguage.SnapshotCopyConstruction
import GloriousLanguage.SnapshotPlacement

/-! Constructive physical placement of a copied snapshot. The captured
inventory is placed in order: each selected root's relocated storage obtains a
fresh aligned extent inside the address space, disjoint from live storage and
from every extent already placed. The fold either places the whole inventory or
reports the real physical exhaustion of the next selected root given its
successful prefix. Nothing is installed before the whole placement succeeds. -/
namespace Glorious.Language.Execution

open Kernel

theorem Table.get_append_none {α : Type} {left right : Table α} {id : Identity}
    (absent : Table.get left id = none) : Table.get (left ++ right) id = Table.get right id := by
  induction left with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key,value⟩
      by_cases same : key = id
      · subst same
        simp [Table.get] at absent
      · have later : Table.get (rest ++ right) id = Table.get right id :=
          ih (by simpa [Table.get,same] using absent)
        simpa [Table.get,same] using later

theorem Table.get_append_single {α : Type} {left : Table α} {id : Identity} {value : α}
    (absent : Table.get left id = none) : Table.get (left ++ [(id,value)]) id = some value := by
  rw [Table.get_append_none absent]
  simp [Table.get]

theorem Table.get_eq_none_of_not_mem {α : Type} {table : Table α} {id : Identity}
    (fresh : id ∉ table.map Prod.fst) : Table.get table id = none := by
  cases found : Table.get table id with
  | none => rfl
  | some base => exact False.elim (fresh (List.mem_map.mpr ⟨(id,base),Table.mem_of_get found,rfl⟩))

theorem PlacementPrefix.empty {program : Kernel.Program} {world : World} :
    PlacementPrefix program.declarations world [] :=
  ⟨by simp [Table.Unique],
    by intro entry member; simp at member,
    by intro a b left right x y first; simp at first⟩

theorem PlacementPrefix.get_of_mem {program : Kernel.Program} {world : World} {table : Table Nat}
    (placed : PlacementPrefix program.declarations world table) {id : Identity} {base : Nat}
    (member : (id,base) ∈ table) : Table.get table id = some base :=
  placed.unique.get_of_mem member

theorem PlacementPrefix.get_append_new {program : Kernel.Program} {world : World} {table : Table Nat}
    (_placed : PlacementPrefix program.declarations world table) {id : Identity} {base : Nat}
    (fresh : id ∉ table.map Prod.fst) : Table.get (table ++ [(id,base)]) id = some base :=
  Table.get_append_single (Table.get_eq_none_of_not_mem fresh)

theorem PlacementPrefix.get_append_old {table : Table Nat} {id : Identity} {base : Nat}
    (found : Table.get table id = some base) : Table.get (table ++ [(id,base)]) id = some base :=
  Table.get_append_left found

/-- Placing one more selected root extends a placed prefix: the new entry is
unique, has its real extent, and is separated from every earlier entry. -/
theorem PlacementPrefix.step {program : Kernel.Program} {world : World} {table : Table Nat}
    {id : Identity} {root : Root} {base : Nat} (placed : PlacementPrefix program.declarations world table)
    (found : Table.get world.roots id = some root)
    (extent : PhysicalExtent program.declarations.input.target world root.layout base)
    (compatible : ∀ other otherBase otherRoot, (other,otherBase) ∈ table →
      Table.get world.roots other = some otherRoot →
      root.layout.size = 0 ∨ otherRoot.layout.size = 0 ∨
        base + root.layout.size ≤ otherBase ∨ otherBase + otherRoot.layout.size ≤ base)
    (fresh : id ∉ table.map Prod.fst) :
    PlacementPrefix program.declarations world (table ++ [(id,base)]) := by
  refine ⟨?_,?_,?_⟩
  · change ((table ++ [(id,base)]).map Prod.fst).Nodup
    rw [List.map_append,List.map_cons,List.map_nil]
    refine List.nodup_append.mpr ⟨placed.unique,List.nodup_cons.mpr ⟨by simp,by simp⟩,?_⟩
    intro old oldMember new newMember same
    rw [List.mem_singleton] at newMember
    subst newMember
    exact fresh (same ▸ oldMember)
  · intro entry member root2 rootAt
    rcases List.mem_append.mp member with old | freshEntry
    · exact placed.extent entry old root2 rootAt
    · rw [List.mem_singleton] at freshEntry
      subst freshEntry
      have sameRoot : root2 = root := Option.some.inj (rootAt.symm.trans found)
      subst sameRoot
      exact extent
  · intro a b left right x y first second different leftAt rightAt
    have firstMember : (a,x) ∈ table ∨ (a,x) = (id,base) := by
      have split := List.mem_append.mp first
      rcases split with old | freshEntry
      · exact Or.inl old
      · rw [List.mem_singleton] at freshEntry
        exact Or.inr freshEntry
    have secondMember : (b,y) ∈ table ∨ (b,y) = (id,base) := by
      have split := List.mem_append.mp second
      rcases split with old | freshEntry
      · exact Or.inl old
      · rw [List.mem_singleton] at freshEntry
        exact Or.inr freshEntry
    rcases firstMember with firstOld | firstNew
    · rcases secondMember with secondOld | secondNew
      · exact placed.separated a b left right x y firstOld secondOld different leftAt rightAt
      · injection secondNew with bEq yEq
        subst bEq
        subst yEq
        have rightEq : right = root := Option.some.inj (rightAt.symm.trans found)
        subst rightEq
        rcases compatible a x left firstOld leftAt with zero | zero | apart | apart
        · exact Or.inr (Or.inl zero)
        · exact Or.inl zero
        · exact Or.inr (Or.inr (Or.inr apart))
        · exact Or.inr (Or.inr (Or.inl apart))
    · injection firstNew with aEq xEq
      subst aEq
      subst xEq
      have leftEq : left = root := Option.some.inj (leftAt.symm.trans found)
      subst leftEq
      rcases secondMember with secondOld | secondNew
      · rcases compatible b y right secondOld rightAt with zero | zero | apart | apart
        · exact Or.inl zero
        · exact Or.inr (Or.inl zero)
        · exact Or.inr (Or.inr (Or.inl apart))
        · exact Or.inr (Or.inr (Or.inr apart))
      · injection secondNew with bEq yEq
        subst bEq
        exact False.elim (different rfl)

/-- The physical placement fold, in the selected-root order. A blocked step is
relative to the successful prefix placed before it: earlier placements may
exhaust a later request, and the failure is the absence of a real extent
compatible with that prefix, never missing logical evidence. -/
theorem placement_fold {program : Kernel.Program} {world : World} {roots : List Identity}
    (present : ∀ id ∈ roots, ∃ root, Table.get world.roots id = some root) (distinct : roots.Nodup) :
    SnapshotPlaced program.declarations world roots ∨ SnapshotBlocked program.declarations world roots := by
  suffices ∀ (placed : Table Nat) (remaining : List Identity),
      placed.map Prod.fst ++ remaining = roots → PlacementPrefix program.declarations world placed →
      remaining.Nodup → (∀ id ∈ remaining, ∃ root, Table.get world.roots id = some root) →
      (∀ id ∈ remaining, id ∉ placed.map Prod.fst) →
      SnapshotPlaced program.declarations world roots ∨ SnapshotBlocked program.declarations world roots by
    exact this [] roots (by simp) .empty distinct present (by simp)
  intro placed remaining
  induction remaining generalizing placed with
  | nil =>
      intro invariant placedFacts _ _ _
      exact Or.inl ⟨placed,by simpa using invariant,placedFacts.unique,
        fun id base lookup root found => placedFacts.extent (id,base) (Table.mem_of_get lookup) root found,
        fun a b left right x y _ _ different leftAt rightAt firstAt secondAt =>
          placedFacts.separated a b left right x y (Table.mem_of_get firstAt)
            (Table.mem_of_get secondAt) different leftAt rightAt⟩
  | cons id rest ih =>
      intro invariant placedFacts nodup presentRoots fresh
      obtain ⟨root,found⟩ := presentRoots id List.mem_cons_self
      have restNodup : rest.Nodup := (List.nodup_cons.mp nodup).2
      have presentRest : ∀ other ∈ rest, ∃ current, Table.get world.roots other = some current :=
        fun other member => presentRoots other (List.mem_cons_of_mem _ member)
      have freshHead : id ∉ placed.map Prod.fst := fresh id List.mem_cons_self
      by_cases extent : ∃ base, PhysicalExtent program.declarations.input.target world root.layout base ∧
          ∀ other otherBase otherRoot, (other,otherBase) ∈ placed →
            Table.get world.roots other = some otherRoot →
            root.layout.size = 0 ∨ otherRoot.layout.size = 0 ∨
              base + root.layout.size ≤ otherBase ∨ otherBase + otherRoot.layout.size ≤ base
      · obtain ⟨base,extentFacts,compatible⟩ := extent
        have extended := placedFacts.step found extentFacts compatible freshHead
        have extendedInvariant : (placed ++ [(id,base)]).map Prod.fst ++ rest = roots := by
          simpa only [List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.singleton_append]
            using invariant
        have extendedFresh : ∀ other ∈ rest, other ∉ (placed ++ [(id,base)]).map Prod.fst := by
          intro other member presentEntry
          have different : other ≠ id := fun same => (List.nodup_cons.mp nodup).1 (same ▸ member)
          have outside : other ∉ placed.map Prod.fst := fresh other (List.mem_cons_of_mem _ member)
          have split := List.mem_append.mp (by
            simpa only [List.map_append,List.map_cons,List.map_nil] using presentEntry)
          rcases split with old | single
          · exact outside old
          · rw [List.mem_singleton] at single
            exact different single
        exact ih (placed ++ [(id,base)]) extendedInvariant extended restNodup presentRest extendedFresh
      · refine Or.inr ⟨placed,id,rest,root,placedFacts,invariant.symm,found,?_⟩
        intro base extentFacts
        apply Classical.byContradiction
        intro impossible
        exact extent ⟨base,extentFacts,fun other otherBase otherRoot member rootAt => by
          apply Classical.byContradiction
          intro conflict
          exact impossible ⟨other,otherBase,otherRoot,member,rootAt,conflict⟩⟩

theorem SnapshotPhysical.get_of_mem {program : Kernel.Program} {world : World} {roots : List Identity}
    {table : Table Nat} (complete : SnapshotPhysical program.declarations world roots table)
    {id : Identity} {base : Nat} (member : (id,base) ∈ table) : Table.get table id = some base :=
  complete.unique.get_of_mem member

/-- The real extent of one placed root, in exactly the shape the storage plan
records: positive, aligned, in bounds, and disjoint from live storage. -/
theorem SnapshotPhysical.physical {program : Kernel.Program} {world : World} {roots : List Identity}
    {table : Table Nat} (complete : SnapshotPhysical program.declarations world roots table)
    {id : Identity} {root : Root} (member : id ∈ roots) (found : Table.get world.roots id = some root) :
    ∃ base, Table.get table id = some base ∧ 0 < base ∧
      base % root.layout.alignment = 0 ∧
      base + root.layout.size < 2^program.declarations.input.target.pointerBits ∧
      DisjointStorage world base root.layout.size := by
  have inKeys : id ∈ table.map Prod.fst := by rw [complete.keys]; exact member
  obtain ⟨entry,entryMem,entryEq⟩ := List.mem_map.mp inKeys
  have lookup : Table.get table id = some entry.2 := by
    have selected := complete.get_of_mem entryMem
    simpa only [entryEq] using selected
  obtain ⟨positive,aligned,bounded,disjoint⟩ := complete.extent id entry.2 lookup root found
  exact ⟨entry.2,lookup,positive,aligned,bounded,disjoint⟩

/-- A blocked placement admits no complete table that agrees with the placed
prefix: the next selected root has no real extent separated from that prefix,
and any complete table must place exactly that prefix. -/
theorem SnapshotPhysicalBlocked.no_extension {program : Kernel.Program} {world : World}
    {roots : List Identity} {placed : Table Nat} {blocked : Identity} {rest : List Identity} {root : Root}
    {table : Table Nat}
    (block : SnapshotPhysicalBlocked program.declarations world roots placed blocked rest root)
    (agrees : ∀ id base, Table.get placed id = some base → Table.get table id = some base)
    (physical : SnapshotPhysical program.declarations world roots table) : False := by
  have presentRoot : blocked ∈ roots := by
    rw [block.split]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have placedKeys : blocked ∉ placed.map Prod.fst := by
    have splitNodup : (placed.map Prod.fst ++ blocked :: rest).Nodup := by
      rw [← block.split,← physical.keys]
      exact physical.unique
    have separate := (List.nodup_append.mp splitNodup).2.2
    intro member
    exact separate blocked member blocked (List.mem_cons_self ..) rfl
  have inKeys : blocked ∈ table.map Prod.fst := by rw [physical.keys]; exact presentRoot
  obtain ⟨entry,entryMem,entryEq⟩ := List.mem_map.mp inKeys
  have lookup : Table.get table blocked = some entry.2 := by
    have selected := physical.get_of_mem entryMem
    simpa only [entryEq] using selected
  obtain ⟨other,otherBase,otherRoot,member,rootAt,conflict⟩ :=
    block.exhausted entry.2 (physical.extent blocked entry.2 lookup root block.present)
  have memberLookup : Table.get placed other = some otherBase := block.placedPrefix.get_of_mem member
  have otherLookup : Table.get table other = some otherBase := agrees other otherBase memberLookup
  have otherRoots : other ∈ roots := by
    rw [block.split]
    exact List.mem_append.mpr (Or.inl (PlacementPrefix.key_mem member))
  have different : other ≠ blocked := by
    intro same
    exact placedKeys (same ▸ PlacementPrefix.key_mem member)
  rcases physical.separated other blocked otherRoot root otherBase entry.2 otherRoots presentRoot different
      rootAt block.present otherLookup lookup with zero | zero | apart | apart
  · exact conflict (Or.inr (Or.inl zero))
  · exact conflict (Or.inl zero)
  · exact conflict (Or.inr (Or.inr (Or.inr apart)))
  · exact conflict (Or.inr (Or.inr (Or.inl apart)))

end Glorious.Language.Execution
