import Grounded.Projections

/-! A lexical place selects its declared root and the shared checked field path.
Runtime reads and writes use BindingAccess over the actual addressed heap. -/
namespace Grounded


inductive PlaceType (program : Program) (home : Module) (context : List (BindingId × BindingType)) :
    Place → Ty → Bool → Prop where
  | root {name : BindingId} {fields : List FieldKey} {parent result : Ty} {mutable : Bool}
      (selected : lookup name context = some ⟨parent, mutable⟩)
      (path : PathType program home parent fields result) :
      PlaceType program home context ⟨name, fields⟩ result mutable

/-- Exclusive owned inputs may share a root when their checked fields are
separate. This is pre-state geometry, not loan permission or future readiness. -/
inductive PlaceDisjoint (program : Program) (home : Module) (context : List (BindingId × BindingType)) :
    Place → Place → Prop where
  | roots {left right : Place} (different : left.root ≠ right.root) :
      PlaceDisjoint program home context left right
  | fields {left right : Place} {slot : BindingType}
      (same : left.root = right.root) (selected : lookup left.root context = some slot)
      (apart : PathDisjoint program home slot.type left.fields right.fields) :
      PlaceDisjoint program home context left right



end Grounded
