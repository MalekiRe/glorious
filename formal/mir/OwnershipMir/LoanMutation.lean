import OwnershipMir.Loans
import OwnershipMir.Instructions

namespace OwnershipMir

/-- Replacing a selected resident keeps the containing root present, even when
that root itself is the referent. A reference move writes a declared hole,
whereas an ordinary owning move may remove its whole root. -/
theorem focus_rebuild_present {α : Type} {path : List Direction} {layout : Layout}
    {cell : Cell α} {lens : Lens α} (found : focus path layout cell = some lens) (value : Tree α) :
    ∃ tree, lens.rebuild (some value) = some tree := by
  cases path with
  | nil => cases Option.some.inj found; exact ⟨value, rfl⟩
  | cons direction rest =>
    cases cell with
    | none => cases direction <;> simp [focus] at found
    | some tree =>
      cases direction <;> cases tree <;> simp only [focus] at found
      all_goals try contradiction
      all_goals
        obtain ⟨sub, focused, rfl⟩ := Option.map_eq_some_iff.mp found
        exact ⟨_, rfl⟩

/-- The same focus supplies both selection and replacement; no independent
address walker reconstructs the referent after a write. -/
theorem focus_write_read {α : Type} {path : List Direction} {layout : Layout}
    {cell : Cell α} {lens : Lens α} (found : focus path layout cell = some lens) (value : Tree α) :
    ∃ after, focus path layout (lens.rebuild (some value)) = some after ∧
      after.selected = some value ∧ ∀ replacement, after.rebuild replacement = lens.rebuild replacement := by
  induction path generalizing cell lens with
  | nil =>
    cases Option.some.inj found
    exact ⟨⟨some value, id⟩, rfl, rfl, fun _ => rfl⟩
  | cons direction path ih =>
    let outer := lens.rebuild
    cases cell with
    | none => cases direction <;> simp [focus] at found
    | some tree =>
      cases direction <;> cases tree <;> simp only [focus] at found
      all_goals try contradiction
      all_goals
        obtain ⟨sub, focused, rfl⟩ := Option.map_eq_some_iff.mp found
        obtain ⟨changed, present⟩ := focus_rebuild_present focused value
        obtain ⟨after, located, selected, rebuild⟩ := ih focused
        rw [present] at located
        refine ⟨⟨after.selected, outer⟩, ?_, selected, fun _ => rfl⟩
        simp only [focus, present, Option.getD_some, located, Option.map_some, outer, rebuild]

/-- A reference update retains the selected layout, including at an empty path. -/
def Store.replaceLoan {n : Nat} (store : Store n Atom) (loan : Loan n)
    (slots : Region n Atom) (lens : Lens Atom) (value : Value) (temp : Cell Atom) : Store n Atom :=
  store.replace loan.referent.region ((loan.referent.place loan.target).write slots lens (some value)) temp

def Store.moveLoan {n : Nat} (store : Store n Atom) (identity : Nat) : Option (Store n Atom) := do
  let loan ← store.loans[identity]?
  let slots ← store.region loan.referent.region
  let lens ← (loan.referent.place loan.target).find slots
  let value ← lens.selected
  match store.temp with
  | none => some (store.replaceLoan loan slots lens (.hole loan.target) (some value))
  | some _ => none

def Store.writeLoan {n : Nat} (store : Store n Atom) (identity : Nat) : Option (Store n Atom) := do
  let loan ← store.loans[identity]?
  let slots ← store.region loan.referent.region
  let lens ← (loan.referent.place loan.target).find slots
  let value ← store.temp
  if vacant lens.selected then
    some (store.replaceLoan loan slots lens value none)
  else none

theorem Store.replaceLoan_find {n : Nat} {store : Store n Atom} {loan : Loan n}
    {slots : Region n Atom} {lens : Lens Atom}
    (live : store.region loan.referent.region = some slots)
    (focused : (loan.referent.place loan.target).find slots = some lens)
    (value : Value) (temp : Cell Atom) :
    ∃ after, (store.replaceLoan loan slots lens value temp).find loan.referent loan.target = some after ∧
      after.selected = some value ∧ ∀ replacement, after.rebuild replacement = lens.rebuild replacement := by
  obtain ⟨after, found, selected, rebuilt⟩ := focus_write_read focused value
  refine ⟨after, ?_, selected, rebuilt⟩
  unfold Store.find Store.replaceLoan
  rw [Store.replace_same (Store.region_bound live)]
  simpa [Place.find, Address.place, Place.write] using found

/-- Restoring the extracted value is an actual write, including when the loan
addresses a complete root. This equality includes every region and loan origin. -/
theorem Store.move_write_roundtrip {n : Nat} {store : Store n Atom} {identity : Nat}
    {loan : Loan n} {slots : Region n Atom} {lens : Lens Atom} {value : Value}
    (origin : store.loans[identity]? = some loan) (live : store.region loan.referent.region = some slots)
    (focused : (loan.referent.place loan.target).find slots = some lens)
    (resident : lens.selected = some value) (empty : store.temp = none) :
    ∃ moved, store.moveLoan identity = some moved ∧ moved.writeLoan identity = some store := by
  let changed := (loan.referent.place loan.target).write slots lens (some (.hole loan.target))
  let moved := store.replace loan.referent.region changed (some value)
  obtain ⟨after, found, hole, rebuilt⟩ := store.replaceLoan_find live focused (.hole loan.target) (some value)
  have changedLive : moved.region loan.referent.region = some changed :=
    Store.replace_same (Store.region_bound live) _ _
  have located : (loan.referent.place loan.target).find changed = some after := by
    change moved.find loan.referent loan.target = some after at found
    simpa [Store.find, changedLive] using found
  have restored : (loan.referent.place loan.target).write changed after (some value) = slots := by
    have original := focus_rebuild loan.referent.path loan.target (slots loan.referent.root) lens focused
    rw [resident] at original
    simp only [Place.write, changed, rebuilt, Address.place]
    funext root
    by_cases same : root = loan.referent.root
    · subst root; simpa [update] using original
    · simp [update, same]
  refine ⟨moved, ?_, ?_⟩
  · simp [Store.moveLoan, origin, live, focused, resident, empty, moved, changed, Store.replaceLoan]
  · change (do
      let selected ← moved.loans[identity]?
      let roots ← moved.region selected.referent.region
      let focused ← (selected.referent.place selected.target).find roots
      let value ← moved.temp
      if vacant focused.selected then some (moved.replaceLoan selected roots focused value none) else none) = some store
    have origin' : moved.loans[identity]? = some loan := origin
    simp only [origin']
    simp [changedLive, located, hole, vacant]
    change some (moved.replaceLoan loan changed after value none) = some store
    unfold Store.replaceLoan
    rw [restored, Store.replace_replace, ← empty, Store.replace_self live]

theorem Store.replaceLoan_mass {n : Nat} {store : Store n Atom} {loan : Loan n}
    {slots : Region n Atom} {lens : Lens Atom}
    (live : store.region loan.referent.region = some slots)
    (focused : (loan.referent.place loan.target).find slots = some lens)
    (value : Value) (temp : Cell Atom) (leaf : Atom → Nat) (shell : Shell → Nat) :
    (store.replaceLoan loan slots lens value temp).mass leaf shell +
      cellMass leaf shell lens.selected + cellMass leaf shell store.temp =
      store.mass leaf shell + cellMass leaf shell (some value) + cellMass leaf shell temp := by
  have within := Place.mass_write (State.mk slots store.temp) (loan.referent.place loan.target)
    lens focused (some value) temp leaf shell
  have across := Store.replace_mass_state live
    (State.mk ((loan.referent.place loan.target).write slots lens (some value)) temp) leaf shell
  change (store.replace _ _ _).mass _ _ + _ + _ = _
  dsimp only at within across
  omega

theorem Store.moveLoan_mass {n : Nat} {store : Store n Atom} {loan : Loan n}
    {slots : Region n Atom} {lens : Lens Atom} {value : Value}
    (live : store.region loan.referent.region = some slots)
    (focused : (loan.referent.place loan.target).find slots = some lens)
    (resident : lens.selected = some value) (empty : store.temp = none)
    (leaf : Atom → Nat) (shell : Shell → Nat) :
    (store.replaceLoan loan slots lens (.hole loan.target) (some value)).mass leaf shell = store.mass leaf shell := by
  have balance := store.replaceLoan_mass live focused (.hole loan.target) (some value) leaf shell
  simp only [resident, empty, cellMass, Tree.mass, Nat.add_zero] at balance
  omega

theorem Store.writeLoan_mass {n : Nat} {store : Store n Atom} {loan : Loan n}
    {slots : Region n Atom} {lens : Lens Atom} {value : Value}
    (live : store.region loan.referent.region = some slots)
    (focused : (loan.referent.place loan.target).find slots = some lens)
    (hole : lens.selected = some (.hole loan.target)) (register : store.temp = some value)
    (leaf : Atom → Nat) (shell : Shell → Nat) :
    (store.replaceLoan loan slots lens value none).mass leaf shell = store.mass leaf shell := by
  have balance := store.replaceLoan_mass live focused value none leaf shell
  simp only [hole, register, cellMass, Tree.mass, Nat.add_zero] at balance
  omega

structure MoveLoanReady {n : Nat} (store : Store n Atom) (identity : Nat) : Prop where
  empty : store.temp = none
  initialized : store.LoanReady identity
  permission : ∀ loan, store.loans[identity]? = some loan → store.Permitted (some identity) .unique loan.referent



end OwnershipMir
