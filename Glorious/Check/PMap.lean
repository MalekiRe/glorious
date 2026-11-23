module

public import Lean.Data.PersistentHashMap
public import Glorious.Addr

/-!
# Maps the checker's state shares with its earlier selves

The checker keeps its state as one value and goes back to an earlier one
when a guess fails (`checkDeciding`, speculative inference). A `Std.HashMap`
that is still held by such an earlier state is copied whole the first time
it is changed after that: for a map that grows with the program, a cost of
its size each time. A persistent map changes the path to one entry, and
shares the rest with the earlier map.
-/

@[expose] public section

namespace Glorious

/-- A persistent map, with the part of `Std.HashMap`'s interface the checker uses. -/
structure PMap (α : Type) (β : Type) [BEq α] [Hashable α] where
  m : Lean.PersistentHashMap α β := Lean.PersistentHashMap.empty

namespace PMap

variable {α β : Type} [BEq α] [Hashable α]

@[inline] def insert (p : PMap α β) (k : α) (v : β) : PMap α β := ⟨p.m.insert k v⟩
@[inline] def get? (p : PMap α β) (k : α) : Option β := p.m.find? k

instance : GetElem? (PMap α β) α β (fun _ _ => False) where
  getElem _ _ h := absurd h id
  getElem? p k := p.get? k
  getElem! p k := match p.get? k with
    | some v => v
    | none => panic! "key is not in the map"

end PMap


end Glorious
