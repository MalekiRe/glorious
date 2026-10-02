import OwnershipMir.Focus

namespace OwnershipMir

/-- A proof-level tree context, used to instantiate the existing executable
focus. It is not an additional ownership inventory or runtime traversal. -/
inductive TreeFrame (α : Type) where
  | hole
  | left (inside : TreeFrame α) (right : Tree α)
  | right (left : Tree α) (inside : TreeFrame α)
  | body (shell : Shell) (inside : TreeFrame α)

def TreeFrame.plug {α : Type} : TreeFrame α → Tree α → Tree α
  | .hole, tree => tree
  | .left f r, tree => .pair (f.plug tree) r
  | .right l f, tree => .pair l (f.plug tree)
  | .body s f, tree => .wrap s (f.plug tree)

def TreeFrame.path {α : Type} : TreeFrame α → List Direction
  | .hole => []
  | .left f _ => .left :: f.path
  | .right _ f => .right :: f.path
  | .body _ f => .body :: f.path

def TreeFrame.rebuild {α : Type} (frame : TreeFrame α) (layout : Layout) (cell : Cell α) : Cell α :=
  match frame with
  | .hole => cell
  | _ => some (frame.plug (cell.getD (.hole layout)))

@[simp] theorem TreeFrame.rebuild_some {α : Type} (frame : TreeFrame α) (layout : Layout) (tree : Tree α) :
    frame.rebuild layout (some tree) = some (frame.plug tree) := by
  cases frame <;> rfl

@[simp] theorem TreeFrame.rebuild_getD {α : Type} (frame : TreeFrame α) (layout : Layout) (cell : Cell α) :
    (frame.rebuild layout cell).getD (.hole layout) = frame.plug (cell.getD (.hole layout)) := by
  cases frame <;> rfl

/-- The proof context corresponds exactly to the ordinary executable focus. -/
theorem TreeFrame.focus {α : Type} (frame : TreeFrame α) (layout : Layout) (tree : Tree α) :
    focus frame.path layout (some (frame.plug tree)) =
      some ⟨some tree, frame.rebuild layout⟩ := by
  induction frame with
  | hole => rfl
  | left f r ih =>
    simp only [TreeFrame.path, TreeFrame.plug, OwnershipMir.focus, ih, Option.map_some]
    congr 2
    funext cell
    simp only [TreeFrame.rebuild_getD]
    rfl
  | right l f ih =>
    simp only [TreeFrame.path, TreeFrame.plug, OwnershipMir.focus, ih, Option.map_some]
    congr 2
    funext cell
    simp only [TreeFrame.rebuild_getD]
    rfl
  | body s f ih =>
    simp only [TreeFrame.path, TreeFrame.plug, OwnershipMir.focus, ih, Option.map_some]
    congr 2
    funext cell
    simp only [TreeFrame.rebuild_getD]
    rfl

def TreeFrame.compose {α : Type} : TreeFrame α → TreeFrame α → TreeFrame α
  | .hole, inner => inner
  | .left f r, inner => .left (f.compose inner) r
  | .right l f, inner => .right l (f.compose inner)
  | .body s f, inner => .body s (f.compose inner)

@[simp] theorem TreeFrame.compose_plug {α : Type} (outer inner : TreeFrame α) (tree : Tree α) :
    (outer.compose inner).plug tree = outer.plug (inner.plug tree) := by
  induction outer <;> simp_all [TreeFrame.compose, TreeFrame.plug]

@[simp] theorem TreeFrame.compose_path {α : Type} (outer inner : TreeFrame α) :
    (outer.compose inner).path = outer.path ++ inner.path := by
  induction outer <;> simp_all [TreeFrame.compose, TreeFrame.path]

theorem TreeFrame.path_empty {α : Type} (frame : TreeFrame α) : frame.path = [] ↔ frame = .hole := by
  cases frame <;> simp [TreeFrame.path]

theorem TreeFrame.nested_rebuild {α : Type} (outer inner : TreeFrame α) (nonempty : inner ≠ .hole)
    (layout : Layout) :
    (outer.compose inner).rebuild layout none = some (outer.plug (inner.plug (.hole layout))) := by
  induction outer <;> cases inner <;> simp_all [TreeFrame.rebuild, TreeFrame.compose, TreeFrame.plug]

end OwnershipMir
