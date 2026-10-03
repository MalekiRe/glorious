import OwnershipMir.Tree

namespace OwnershipMir

inductive Direction where
  | left | right | body
  deriving DecidableEq

abbrev Cell (α : Type) := Option (Tree α)

structure Lens (α : Type) where
  selected : Cell α
  rebuild : Cell α → Cell α

/-- One traversal supplies selection and rebuilding. Only the selected missing
child receives the instruction's declared hole layout; outer shells survive. -/
def focus {α : Type} : List Direction → Layout → Cell α → Option (Lens α)
  | [], _, cell => some ⟨cell, id⟩
  | .left :: tail, layout, some (.pair l r) =>
    (focus tail layout (some l)).map fun f =>
      ⟨f.selected, fun x => some (.pair ((f.rebuild x).getD (.hole layout)) r)⟩
  | .right :: tail, layout, some (.pair l r) =>
    (focus tail layout (some r)).map fun f =>
      ⟨f.selected, fun x => some (.pair l ((f.rebuild x).getD (.hole layout)))⟩
  | .body :: tail, layout, some (.wrap s b) =>
    (focus tail layout (some b)).map fun f =>
      ⟨f.selected, fun x => some (.wrap s ((f.rebuild x).getD (.hole layout)))⟩
  | _, _, _ => none

def cellMap {α β : Type} (f : α → β) (cell : Cell α) : Cell β := cell.map (Tree.map f)

def cellMass {α : Type} (leaf : α → Nat) (shell : Shell → Nat) : Cell α → Nat
  | none => 0
  | some tree => tree.mass leaf shell

@[simp] theorem map_getD {α β : Type} (f : α → β) (cell : Cell α) (layout : Layout) :
    (cell.getD (.hole layout)).map f = (cellMap f cell).getD (.hole layout) := by
  cases cell <;> rfl

@[simp] theorem mass_getD {α : Type} (leaf : α → Nat) (shell : Shell → Nat)
    (cell : Cell α) (layout : Layout) :
    (cell.getD (.hole layout)).mass leaf shell = cellMass leaf shell cell := by
  cases cell <;> rfl

/-- Classification commutes with the same physical focus and every rebuild.
This derives a runtime focus from a static path, not from a post-state premise. -/
theorem focus_map {α β : Type} (classify : α → β) (path : List Direction) (layout : Layout)
    (cell : Cell α) (typed : Lens β)
    (found : focus path layout (cellMap classify cell) = some typed) :
    ∃ actual, focus path layout cell = some actual ∧
      cellMap classify actual.selected = typed.selected ∧
      ∀ replacement, cellMap classify (actual.rebuild replacement) =
        typed.rebuild (cellMap classify replacement) := by
  induction path generalizing cell typed with
  | nil =>
    simp only [focus, Option.some.injEq] at found
    subst typed
    exact ⟨⟨cell, id⟩, rfl, rfl, fun _ => rfl⟩
  | cons direction path ih =>
    cases cell with
    | none => cases direction <;> simp [cellMap, focus] at found
    | some tree =>
      cases direction <;> cases tree <;> simp only [cellMap, Option.map_some, Tree.map, focus] at found
      all_goals try { contradiction }
      · rename_i l r
        obtain ⟨sub, selected, rfl⟩ := Option.map_eq_some_iff.mp found
        obtain ⟨actual, actualFound, actualSelected, rebuild⟩ := ih (some l) sub selected
        refine ⟨⟨actual.selected, fun x => some (.pair ((actual.rebuild x).getD (.hole layout)) r)⟩,
          by simp [focus, actualFound], actualSelected, ?_⟩
        intro replacement
        change some (((actual.rebuild replacement).getD (.hole layout)).map classify |>.pair (r.map classify)) = _
        rw [map_getD, rebuild]
      · rename_i l r
        obtain ⟨sub, selected, rfl⟩ := Option.map_eq_some_iff.mp found
        obtain ⟨actual, actualFound, actualSelected, rebuild⟩ := ih (some r) sub selected
        refine ⟨⟨actual.selected, fun x => some (.pair l ((actual.rebuild x).getD (.hole layout)))⟩,
          by simp [focus, actualFound], actualSelected, ?_⟩
        intro replacement
        change some (Tree.pair (l.map classify) (((actual.rebuild replacement).getD (.hole layout)).map classify)) = _
        rw [map_getD, rebuild]
      · rename_i s b
        obtain ⟨sub, selected, rfl⟩ := Option.map_eq_some_iff.mp found
        obtain ⟨actual, actualFound, actualSelected, rebuild⟩ := ih (some b) sub selected
        refine ⟨⟨actual.selected, fun x => some (.wrap s ((actual.rebuild x).getD (.hole layout)))⟩,
          by simp [focus, actualFound], actualSelected, ?_⟩
        intro replacement
        change some (Tree.wrap s (((actual.rebuild replacement).getD (.hole layout)).map classify)) = _
        rw [map_getD, rebuild]

/-- Ownership separates into the selected resident and an unchanged frame.
The equation is additive, so it needs no subtraction or uniqueness premise. -/
theorem focus_mass {α : Type} (leaf : α → Nat) (shell : Shell → Nat)
    (path : List Direction) (layout : Layout) (cell : Cell α) (lens : Lens α)
    (found : focus path layout cell = some lens) (replacement : Cell α) :
    cellMass leaf shell (lens.rebuild replacement) + cellMass leaf shell lens.selected =
      cellMass leaf shell cell + cellMass leaf shell replacement := by
  induction path generalizing cell lens with
  | nil =>
    simp only [focus, Option.some.injEq] at found
    subst lens
    exact Nat.add_comm _ _
  | cons direction path ih =>
    cases cell with
    | none => cases direction <;> simp [focus] at found
    | some tree =>
      cases direction <;> cases tree <;> simp only [focus] at found
      all_goals try { contradiction }
      all_goals
        obtain ⟨sub, selected, rfl⟩ := Option.map_eq_some_iff.mp found
        have equation := ih _ sub selected
        simp only [cellMass, Tree.mass, mass_getD] at equation ⊢
        omega

/-- Focusing then rebuilding the same cell is exactly the original tree. -/
theorem focus_rebuild {α : Type} (path : List Direction) (layout : Layout)
    (cell : Cell α) (lens : Lens α) (found : focus path layout cell = some lens) :
    lens.rebuild lens.selected = cell := by
  induction path generalizing cell lens with
  | nil =>
    simp only [focus, Option.some.injEq] at found
    subst lens
    rfl
  | cons direction path ih =>
    cases cell with
    | none => cases direction <;> simp [focus] at found
    | some tree =>
      cases direction <;> cases tree <;> simp only [focus] at found
      all_goals try { contradiction }
      all_goals
        obtain ⟨sub, selected, rfl⟩ := Option.map_eq_some_iff.mp found
        simp [ih _ sub selected]

/-- Rebuilding the same physical focus respects classification of the
replacement; no second path traversal or reconstructed lens is required. -/
theorem focus_rebuild_map_congr {α β : Type} (kind : α → β)
    {path : List Direction} {layout : Layout} {cell : Cell α} {lens : Lens α}
    (found : focus path layout cell = some lens) {first second : Cell α}
    (same : cellMap kind first = cellMap kind second) :
    cellMap kind (lens.rebuild first) = cellMap kind (lens.rebuild second) := by
  induction path generalizing cell lens with
  | nil => cases Option.some.inj found; exact same
  | cons direction path ih =>
    cases cell with
    | none => cases direction <;> simp [focus] at found
    | some tree =>
      cases direction <;> cases tree <;> simp only [focus] at found
      all_goals try contradiction
      all_goals
        obtain ⟨sub, focused, rfl⟩ := Option.map_eq_some_iff.mp found
        have framed := ih focused
        unfold cellMap at framed
        simp only [cellMap, Option.map_some, Tree.map, map_getD]
        rw [framed]


/-- Clearing retains the selected layout; filling preserves that layout.
The same equation serves physical references and declared static metadata. -/
theorem focus_rebuild_layout {α : Type} (kind : α → AtomType) (path : List Direction) (layout : Layout)
    {cell : Cell α} {lens : Lens α} (found : focus path layout cell = some lens)
    (replacement : Cell α)
    (fits : ∀ shape, lens.selected = some shape →
      ((replacement.getD (.hole layout)).layout kind) = shape.layout kind) :
    ∀ tree, cell = some tree → ((lens.rebuild replacement).getD (.hole layout)).layout kind = tree.layout kind := by
  induction path generalizing cell lens with
  | nil => cases Option.some.inj found; exact fits
  | cons direction path ih =>
    cases cell with
    | none => cases direction <;> cases found
    | some tree =>
      cases direction <;> cases tree <;> simp only [focus] at found
      all_goals try contradiction
      all_goals obtain ⟨inside, located, rfl⟩ := Option.map_eq_some_iff.mp found
      all_goals intro actual same; cases same
      all_goals simp only [Option.getD_some, Tree.layout]
      all_goals rw [ih located fits _ rfl]


end OwnershipMir
