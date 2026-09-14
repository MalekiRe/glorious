import GloriousLanguage.Effects

namespace Glorious.Language

theorem Table.get_map_keyed {α β : Type} (table : Table α) (f : Identity → α → β) (id : Identity) :
    Table.get (table.map (fun (key,value) => (key,f key value))) id = (table.get id).map (f id) := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨key,value⟩ := entry
    by_cases same : key = id
    · simp [Table.get,same]
    · simpa only [List.map_cons,Table.get,List.find?_cons,beq_eq_false_iff_ne.mpr same,
        Bool.false_eq_true,↓reduceIte,Option.map_map] using ih

/-- Relabel the home of every root while leaving values, loans and reads of the
world untouched. `suspendRoots` and `restoreRoots` are both instances; no second
storage inventory is introduced. -/
def World.rehome (world : World) (select : Identity → Root → Home) : World :=
  { world with roots := world.roots.map (fun (key,root) => (key,{ root with home := select key root })) }

theorem World.rehome_loans (world : World) (select : Identity → Root → Home) :
    (world.rehome select).loans = world.loans := rfl

theorem World.rehome_get (before : World) (select : Identity → Root → Home) (id : Identity) :
    ({ before with roots := before.roots.map (fun (key,root) =>
      (key,{ root with home := select key root })) } : World).roots.get id =
      (before.roots.get id).map (fun root => { root with home := select id root }) :=
  Table.get_map_keyed before.roots (fun id (root : Root) => { root with home := select id root }) id

theorem World.rehome_origin {before : World} {select : Identity → Root → Home} {id : Identity} {root : Root}
    (found : (before.rehome select).roots.get id = some root) :
    ∃ original, before.roots.get id = some original ∧ root = { original with home := select id original } := by
  unfold World.rehome at found
  rw [World.rehome_get] at found
  obtain ⟨original,selected,same⟩ := Option.map_eq_some_iff.mp found
  exact ⟨original,selected,same.symm⟩

theorem World.rehome_root (before : World) (select : Identity → Root → Home) (address : Address) :
    ({ before with roots := before.roots.map (fun (id,root) =>
      (id,{ root with home := select id root })) } : World).root address =
      (before.root address).map (fun root => { root with home := select address.root root }) := by
  unfold World.root
  rw [World.rehome_get]
  cases before.roots.get address.root with
  | none => rfl
  | some root => dsimp; split <;> rfl

theorem World.rehome_read (before : World) (select : Identity → Root → Home) (address : Address) :
    ({ before with roots := before.roots.map (fun (id,root) =>
      (id,{ root with home := select id root })) } : World).read address = before.read address := by
  unfold World.read
  rw [World.rehome_root]
  cases before.root address <;> rfl

namespace Execution

theorem suspendRoots.eq_rehome (before : World) (roots : List Identity) (id : Identity) :
    suspendRoots before roots id = before.rehome (fun key root => if key ∈ roots then .suspended id else root.home) := by
  unfold suspendRoots World.rehome
  congr 1
  apply List.map_congr_left
  intro entry member
  obtain ⟨key,root⟩ := entry
  dsimp
  split <;> rfl

theorem restoreRoots.eq_rehome (world : World) (homes : Table Home) :
    restoreRoots world homes = world.rehome (fun key root => (homes.get key).getD root.home) := rfl

end Execution
end Glorious.Language
