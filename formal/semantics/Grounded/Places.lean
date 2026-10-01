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


end Grounded
