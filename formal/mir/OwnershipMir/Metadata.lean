import OwnershipMir.Instructions

namespace OwnershipMir

variable {authority : Authority}

theorem focus_selected_declared {declarations : Declarations} (path : List Direction) (layout : Layout)
    {cell : Cell Kind} {lens : Lens Kind} (valid : Cell.Declared declarations id cell)
    (found : focus path layout cell = some lens) : Cell.Declared declarations id lens.selected := by
  induction path generalizing cell lens with
  | nil => cases Option.some.inj found; exact valid
  | cons direction path ih =>
    cases cell with
    | none => cases direction <;> cases found
    | some tree =>
      have treeValid := valid tree rfl
      cases direction <;> cases tree <;> simp only [focus] at found
      all_goals try contradiction
      all_goals obtain ⟨inside, located, rfl⟩ := Option.map_eq_some_iff.mp found
      · cases treeValid with
        | pair left right =>
          apply ih ?_ located
          intro tree same; cases same; exact left
      · cases treeValid with
        | pair left right =>
          apply ih ?_ located
          intro tree same; cases same; exact right
      · cases treeValid with
        | wrap resolved restriction payload nested =>
          apply ih ?_ located
          intro tree same; cases same; exact nested

/-- Clearing installs exactly the selected layout as a hole; filling preserves
an existing layout. This is the one layout equation used for every ancestor. -/
theorem focus_rebuild_layout (path : List Direction) (layout : Layout)
    {cell : Cell Kind} {lens : Lens Kind} (found : focus path layout cell = some lens)
    (replacement : Cell Kind)
    (fits : ∀ shape, lens.selected = some shape →
      ((replacement.getD (.hole layout)).layout id) = shape.layout id) :
    ∀ tree, cell = some tree → ((lens.rebuild replacement).getD (.hole layout)).layout id = tree.layout id := by
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

theorem focus_rebuild_declared {declarations : Declarations} (path : List Direction) (layout : Layout)
    {cell : Cell Kind} {lens : Lens Kind} (valid : Cell.Declared declarations id cell)
    (found : focus path layout cell = some lens) (replacement : Cell Kind)
    (newValid : Cell.Declared declarations id replacement)
    (fits : ∀ shape, lens.selected = some shape →
      ((replacement.getD (.hole layout)).layout id) = shape.layout id) :
    Cell.Declared declarations id (lens.rebuild replacement) := by
  cases cell with
  | none =>
    cases path with
    | nil => cases Option.some.inj found; exact newValid
    | cons direction path => cases direction <;> cases found
  | some tree =>
    intro result stored
    have same := focus_rebuild_layout path layout found replacement fits tree rfl
    rw [stored] at same
    exact (by simpa only [Option.getD_some] using same) ▸ valid tree rfl

theorem Context.declared_update {n : Nat} {declarations : Declarations} {context : Context n}
    (valid : context.Declared declarations) (i : Fin n) {value temp : Cell Kind}
    (resident : Cell.Declared declarations id value) (register : Cell.Declared declarations id temp) :
    (Context.mk (update context.slots i value) temp).Declared declarations := by
  refine ⟨fun j => ?_, register⟩
  by_cases same : j = i
  · subst j; simpa using resident
  · simpa [update, same] using valid.1 j

theorem Extract.Checked.declared {mode : Extract} {before after : Shape}
    (checked : Extract.Checked authority mode before after)
    (valid : Layout.Declared authority.declarations (before.layout id)) :
    Layout.Declared authority.declarations (after.layout id) := by
  cases checked with
  | whole => exact valid
  | deconstruct => cases valid with | wrap resolved restriction payload nested => exact nested

/-- Metadata validity is preserved by the same checked instruction transition;
it is not inferred by another ownership analysis or assumed in the post-state. -/
theorem Op.Checked.declared {n : Nat} {before after : Context n} {op : Op n}
    (checked : Op.Checked authority before op after) (valid : before.Declared authority.declarations) :
    after.Declared authority.declarations := by
  cases checked with
  | @take p mode input output lens empty found selected layout extract =>
    have inputValid := focus_selected_declared p.path p.layout (valid.1 p.root) found input selected
    have resultValid := extract.declared inputValid
    have rootValid := focus_rebuild_declared p.path p.layout (valid.1 p.root) found none
      (by intro tree impossible; cases impossible) (by intro shape same; cases selected.symm.trans same; exact layout)
    exact Context.declared_update valid p.root rootValid (by intro shape same; cases same; exact resultValid)
  | @put p shape lens resident found fits =>
    have shapeValid := valid.2 shape resident
    have rootValid := focus_rebuild_declared p.path p.layout (valid.1 p.root) found (some shape)
      (by intro tree same; cases same; exact shapeValid) (by
        intro original same
        rcases fits with absent | hole
        · cases absent.symm.trans same
        · cases hole.symm.trans same; rfl)
    exact Context.declared_update valid p.root rootValid (by intro tree impossible; cases impossible)
  | @copy p shape lens empty found selected allowed =>
    exact ⟨valid.1, by
      intro tree same
      cases same
      exact focus_selected_declared p.path p.layout (valid.1 p.root) found shape selected⟩
  | drop resident allowed exhausted => exact ⟨valid.1, by intro tree impossible; cases impossible⟩

theorem State.Typed.declared_iff {n : Nat} {declarations : Declarations} {signature : Signature}
    {state : State n} {context : Context n} (typed : state.Typed signature context) :
    state.Declared declarations signature ↔ context.Declared declarations := by
  have cell : ∀ (value : Cell Atom) (shape : Cell Kind), value.map (Value.kind signature) = shape →
      (Cell.Declared declarations (Atom.kind signature) value ↔ Cell.Declared declarations id shape) := by
    intro value shape same
    subst shape
    cases value with
    | none => simp [Cell.Declared]
    | some value => simp [Cell.Declared, Value.kind, Tree.layout_map]
  exact and_congr (forall_congr' fun i => cell _ _ (typed.1 i)) (cell _ _ typed.2)

theorem Op.Checked.preserves_declarations {n : Nat} {signature : Signature} {before after : Context n}
    {op : Op n} (checked : Op.Checked authority before op after) {state next : State n}
    (typed : state.Typed signature before) (valid : state.Declared authority.declarations signature)
    (executed : op.exec state = some next) : next.Declared authority.declarations signature := by
  exact ((checked.executed typed executed).1.declared_iff).mpr (checked.declared (typed.declared_iff.mp valid))

/-- Authorization is about the nominal value actually extracted by the physical
transition, not a caller-supplied flag or unrelated guessed layout. -/
theorem Op.Checked.deconstruction_authorized {n : Nat} {signature : Signature} {before after : Context n}
    {place : Place n} (checked : Op.Checked authority before (.take place .deconstruct) after)
    {state next : State n} (typed : state.Typed signature before)
    (executed : (Op.take place .deconstruct).exec state = some next) :
    ∃ (lens : Lens Atom) (shell : Shell) (body : Value) (declaration : Declaration),
      place.find state.slots = some lens ∧ lens.selected = some (.wrap shell body) ∧
      authority.declarations shell.name = some declaration ∧ shell.restriction = declaration.restriction ∧
      body.layout (Atom.kind signature) = declaration.fields.layout ∧
      declaration.fields.Visible declaration.owner authority.module := by
  obtain ⟨effect, _, legal⟩ := checked.effect typed executed
  cases effect with
  | @take _ p mode lens value result found live extracted unused =>
    cases value <;> simp only [Extract.apply, Option.some.injEq] at extracted
    all_goals try contradiction
    rename_i shell body extractedWitness
    subst result
    have allowed := legal.2
    cases allowed with
    | deconstruct authorized =>
      obtain ⟨declaration, resolved, restriction, payload, visible⟩ := authorized
      refine ⟨lens, shell, body, declaration, found, live, resolved, restriction, ?_, visible⟩
      simpa [Value.kind, Tree.layout_map] using payload


end OwnershipMir
