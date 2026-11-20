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

instance : Inhabited (PMap α β) := ⟨⟨Lean.PersistentHashMap.empty⟩⟩

@[inline] def insert (p : PMap α β) (k : α) (v : β) : PMap α β := ⟨p.m.insert k v⟩
@[inline] def get? (p : PMap α β) (k : α) : Option β := p.m.find? k
@[inline] def contains (p : PMap α β) (k : α) : Bool := p.m.contains k
@[inline] def getD (p : PMap α β) (k : α) (d : β) : β := (p.m.find? k).getD d
@[inline] def erase (p : PMap α β) (k : α) : PMap α β := ⟨p.m.erase k⟩
@[inline] def size (p : PMap α β) : Nat := p.m.foldl (fun n _ _ => n + 1) 0
@[inline] def insertIfNew (p : PMap α β) (k : α) (v : β) : PMap α β :=
  if p.m.contains k then p else p.insert k v
@[inline] def fold {σ : Type} (p : PMap α β) (f : σ → α → β → σ) (init : σ) : σ := p.m.foldl f init
@[inline] def toList (p : PMap α β) : List (α × β) := p.m.toList
@[inline] def toArray (p : PMap α β) : Array (α × β) := p.m.toArray

instance : GetElem? (PMap α β) α β (fun _ _ => False) where
  getElem _ _ h := absurd h id
  getElem? p k := p.get? k
  getElem! p k := match p.get? k with
    | some v => v
    | none => panic! "key is not in the map"

instance {m : Type → Type} [Monad m] : ForIn m (PMap α β) (α × β) where
  forIn p init f := forIn p.toList init f

end PMap


end Glorious
