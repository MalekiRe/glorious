import GloriousLanguage.Storage

/-! The physical placement contract of a copied snapshot, stated below the
machine so the actual replay rules can require it. A placement is an ordered
table of fresh extents for the captured roots; it either covers the whole
inventory or is blocked at a named root given the successful prefix before it.
Nothing is installed before the whole placement succeeds. -/
namespace Glorious.Language.Execution

/-- A physically placed prefix of a snapshot copy. Every placed entry has a
real extent disjoint from live storage, and no two placed extents overlap. This
is a proof-side view of the actual placement, not a second storage graph. -/
structure PlacementPrefix (program : Program) (world : World) (table : Table Nat) : Prop where
  unique : table.Unique
  extent : ∀ (entry : Identity × Nat), entry ∈ table → ∀ root,
    Table.get world.roots entry.1 = some root →
      PhysicalExtent program.input.target world root.layout entry.2
  separated : ∀ a b left right x y, (a,x) ∈ table → (b,y) ∈ table → a ≠ b →
    Table.get world.roots a = some left → Table.get world.roots b = some right →
    left.layout.size = 0 ∨ right.layout.size = 0 ∨
      x + left.layout.size ≤ y ∨ y + right.layout.size ≤ x

theorem PlacementPrefix.key_mem {table : Table Nat} {id : Identity} {base : Nat}
    (member : (id,base) ∈ table) : id ∈ table.map Prod.fst :=
  List.mem_map.mpr ⟨(id,base),member,rfl⟩

/-- A complete physical placement of the captured inventory: one table covering
the whole inventory in order, whose entries have real extents and do not
overlap. It supplies exactly the physical fields of the actual storage plan. -/
structure SnapshotPhysical (program : Program) (world : World) (roots : List Identity)
    (table : Table Nat) : Prop where
  keys : table.map Prod.fst = roots
  unique : table.Unique
  extent : ∀ id base, Table.get table id = some base → ∀ root, Table.get world.roots id = some root →
    PhysicalExtent program.input.target world root.layout base
  separated : ∀ a b left right x y, a ∈ roots → b ∈ roots → a ≠ b →
    Table.get world.roots a = some left → Table.get world.roots b = some right →
    Table.get table a = some x → Table.get table b = some y →
    left.layout.size = 0 ∨ right.layout.size = 0 ∨
      x + left.layout.size ≤ y ∨ y + right.layout.size ≤ x

/-- The captured inventory is completely placed by a real table. -/
abbrev SnapshotPlaced (program : Program) (world : World) (roots : List Identity) : Prop :=
  ∃ table, SnapshotPhysical program world roots table

/-- The genuine physical exhaustion of the ordered placement: a successful
prefix exists and the next selected root has no real extent compatible with it.
No incomplete table is installed and no logical evidence is missing. -/
structure SnapshotPhysicalBlocked (program : Program) (world : World) (roots : List Identity)
    (placed : Table Nat) (blocked : Identity) (rest : List Identity) (root : Root) : Prop where
  placedPrefix : PlacementPrefix program world placed
  split : roots = placed.map Prod.fst ++ blocked :: rest
  present : Table.get world.roots blocked = some root
  exhausted : ∀ base, PhysicalExtent program.input.target world root.layout base →
    ∃ other otherBase otherRoot, (other,otherBase) ∈ placed ∧
      Table.get world.roots other = some otherRoot ∧
      ¬ (root.layout.size = 0 ∨ otherRoot.layout.size = 0 ∨
          base + root.layout.size ≤ otherBase ∨ otherBase + otherRoot.layout.size ≤ base)

/-- The ordered placement fold is blocked at a named selected root. -/
abbrev SnapshotBlocked (program : Program) (world : World) (roots : List Identity) : Prop :=
  ∃ placed blocked rest root, SnapshotPhysicalBlocked program world roots placed blocked rest root

end Glorious.Language.Execution
