import OwnershipMir.Model

namespace OwnershipMir

structure Place (n : Nat) where
  root : Fin n
  path : List Direction
  layout : Layout

/-- Lexical projection permission is independent of physical focus and of
permission to dispose of an owner. Whole empty roots need no representation. -/
def Place.Visible {n : Nat} (authority : Authority) (place : Place n) (slots : Fin n → Cell AtomType) : Prop :=
  match slots place.root with
  | none => place.path = []
  | some shape => ∃ selected, Layout.Accessible authority (shape.layout id) place.path selected

/-- The empty path is ordinary whole-slot access, not a second operation. -/
def Place.find {n : Nat} {α : Type} (place : Place n) (slots : Fin n → Cell α) : Option (Lens α) :=
  focus place.path place.layout (slots place.root)

def Place.write {n : Nat} {α : Type} (place : Place n) (slots : Fin n → Cell α)
    (lens : Lens α) (value : Cell α) : Fin n → Cell α :=
  update slots place.root (lens.rebuild value)

theorem Place.realized {n : Nat} {signature : Signature} {state : State n} {context : Context n}
    (typed : state.Typed signature context) (place : Place n) (lens : Lens AtomType)
    (found : place.find context.slots = some lens) :
    ∃ actual, place.find state.slots = some actual ∧
      actual.selected.map (Value.kind signature) = lens.selected ∧
      ∀ replacement, (actual.rebuild replacement).map (Value.kind signature) =
        lens.rebuild (replacement.map (Value.kind signature)) := by
  apply focus_map (Atom.kind signature) place.path place.layout (state.slots place.root) lens
  change focus place.path place.layout ((state.slots place.root).map (Value.kind signature)) = some lens
  rw [typed.1]
  exact found

theorem Place.typed_write {n : Nat} {signature : Signature} {state : State n} {context : Context n}
    (typed : state.Typed signature context) (place : Place n) (actual : Lens Atom) (lens : Lens AtomType)
    (rebuild : ∀ value, (actual.rebuild value).map (Value.kind signature) =
      lens.rebuild (value.map (Value.kind signature)))
    {value : Cell Atom} {kind : Cell AtomType} (resident : value.map (Value.kind signature) = kind)
    {temp : Cell Atom} {tempKind : Cell AtomType} (register : temp.map (Value.kind signature) = tempKind) :
    (State.mk (place.write state.slots actual value) temp).Typed signature
      ⟨place.write context.slots lens kind, tempKind⟩ := by
  exact typed_update typed place.root (by rw [rebuild, resident]) register

/-- One frame equation covers movement in either direction, overlapping places
in the same aggregate, copying, and shell deconstruction. -/
theorem Place.mass_write {n : Nat} (state : State n) (place : Place n) (lens : Lens Atom)
    (found : place.find state.slots = some lens) (value temp : Cell Atom)
    (leaf : Atom → Nat) (shell : Shell → Nat) :
    (State.mk (place.write state.slots lens value) temp).mass leaf shell +
        cellMass leaf shell lens.selected + cellMass leaf shell state.temp =
      state.mass leaf shell + cellMass leaf shell value + cellMass leaf shell temp := by
  have framed := focus_mass leaf shell place.path place.layout (state.slots place.root) lens found value
  have slots := total_update (fun i => cellMass leaf shell (state.slots i)) place.root
    (cellMass leaf shell (lens.rebuild value))
  have pointwise : (fun i => cellMass leaf shell (place.write state.slots lens value i)) =
      update (fun i => cellMass leaf shell (state.slots i)) place.root (cellMass leaf shell (lens.rebuild value)) := by
    funext i
    simp only [Place.write, update]
    split <;> rfl
  simp only [State.mass, pointwise]
  omega

theorem Place.count_write {n : Nat} (state : State n) (place : Place n) (lens : Lens Atom)
    (found : place.find state.slots = some lens) (value temp : Cell Atom) (identity : ResourceIdentity) :
    (State.mk (place.write state.slots lens value) temp).count identity +
        weight identity lens.selected + weight identity state.temp =
      state.count identity + weight identity value + weight identity temp := by
  exact place.mass_write state lens found value temp (Atom.weight identity) (fun _ => 0)

def vacant {α : Type} : Cell α → Bool
  | none | some (.hole _) => true
  | _ => false

def Fits (shape : Shape) (cell : Cell AtomType) : Prop :=
  cell = none ∨ cell = some (.hole (shape.layout id))

theorem Fits.realized {signature : Signature} {shape : Shape} {cell : Cell Atom} {kind : Cell AtomType}
    (typed : cell.map (Value.kind signature) = kind) (fits : Fits shape kind) :
    vacant cell = true ∧ ∀ identity, weight identity cell = 0 := by
  rcases fits with absent | hole
  · have gone : cell = none := Option.map_eq_none_iff.mp (typed.trans absent)
    subst cell
    exact ⟨rfl, fun _ => rfl⟩
  · cases cell with
    | none => exact ⟨rfl, fun _ => rfl⟩
    | some tree =>
      cases tree <;> simp [Value.kind, Tree.map] at typed
      all_goals try { simp_all }
      exact ⟨rfl, fun _ => rfl⟩

inductive Extract where
  | whole | deconstruct

def Extract.apply {α : Type} : Extract → Tree α → Option (Tree α)
  | .whole, tree => some tree
  | .deconstruct, .wrap _ body => some body
  | _, _ => none

inductive Extract.Checked (authority : Authority) : Extract → Shape → Shape → Prop where
  | whole (shape) : Checked authority .whole shape shape
  | deconstruct {shell body} (authorized : authority.CanOpen shell (body.layout id)) :
      Checked authority .deconstruct (.wrap shell body) body

theorem Extract.Checked.realized {authority : Authority} {signature : Signature} {mode : Extract} {before after : Shape}
    (checked : Extract.Checked authority mode before after) {value : Value} (typed : value.kind signature = before) :
    ∃ result : Value, mode.apply value = some result ∧ result.kind signature = after := by
  cases checked with
  | whole shape => exact ⟨value, rfl, typed⟩
  | @deconstruct shell body authorized =>
    cases value <;> simp only [Value.kind, Tree.map, Tree.wrap.injEq] at typed
    all_goals try { contradiction }
    obtain ⟨rfl, bodyTyped⟩ := typed
    exact ⟨_, rfl, bodyTyped⟩

/-- A drop step releases only a scalar or a structurally exhausted container.
Children must have been handled by earlier instructions. -/
def Tree.shallow {α : Type} : Tree α → Prop
  | .hole _ | .nil | .leaf _ => True
  | .pair (.hole _) (.hole _) => True
  | .wrap _ (.hole _) => True
  | _ => False

end OwnershipMir
