import OwnershipMir.CallSafety

namespace OwnershipMir.Calls

def Configuration.mass {n : Nat} (config : Configuration n) (leaf : Atom → Nat) (shell : Shell → Nat) : Nat :=
  config.store.mass leaf shell

def Configuration.count {n : Nat} (config : Configuration n) (identity : Nat) : Nat :=
  config.mass (Atom.weight identity) (fun _ => 0)

def Configuration.Unique {n : Nat} (config : Configuration n) : Prop :=
  ∀ identity, config.count identity ≤ 1

structure Preserves {n : Nat} (signature : Signature) (before after : Configuration n) : Prop where
  bounded : ∀ identity, after.count identity ≤ before.count identity
  exact : ∀ identity, signature identity = .exact → after.count identity = before.count identity

theorem Preserves.refl {n : Nat} (signature : Signature) (config : Configuration n) : Preserves signature config config :=
  ⟨fun _ => Nat.le_refl _, fun _ _ => rfl⟩

theorem Preserves.trans {n : Nat} {signature : Signature} {a b c : Configuration n}
    (first : Preserves signature a b) (last : Preserves signature b c) : Preserves signature a c :=
  ⟨fun i => Nat.le_trans (last.bounded i) (first.bounded i), fun i exact => (last.exact i exact).trans (first.exact i exact)⟩

theorem Preserves.unique {n : Nat} {signature : Signature} {before after : Configuration n}
    (preserved : Preserves signature before after) (unique : before.Unique) : after.Unique :=
  fun i => Nat.le_trans (preserved.bounded i) (unique i)

theorem total_zero (n : Nat) : total (fun _ : Fin n => 0) = 0 := by
  induction n <;> simp_all [total]

theorem argument_mass {n : Nat} (value : Value) (leaf : Atom → Nat) (shell : Shell → Nat) :
    (State.mk (argumentSlots value) none : State (n + 1)).mass leaf shell = cellMass leaf shell (some value) := by
  simp [State.mass, argumentSlots, total, cellMass, total_zero]

theorem empty_mass (n : Nat) (leaf : Atom → Nat) (shell : Shell → Nat) :
    (emptyState n).mass leaf shell = 0 := by
  simp [emptyState, State.mass, cellMass, total_zero]

theorem enter_mass {n : Nat} (store : Store (n + 1) Atom) (argument : Value)
    (resident : store.temp = some argument) (leaf : Atom → Nat) (shell : Shell → Nat) :
    (store.allocate (argumentSlots argument)).mass leaf shell = store.mass leaf shell := by
  have equation := store.allocate_mass (argumentSlots argument) leaf shell
  have argumentEquation : total (fun i : Fin (n + 1) => cellMass leaf shell (argumentSlots argument i)) =
      cellMass leaf shell (some argument) := by
    simpa [State.mass, cellMass] using argument_mass (n := n) argument leaf shell
  rw [argumentEquation, resident] at equation
  omega

theorem local_mass {n : Nat} (store : Store (n + 1) Atom) {active : Nat} {slots : Region (n + 1) Atom}
    (live : store.region active = some slots) (after : State (n + 1)) (leaf : Atom → Nat) (shell : Shell → Nat)
    (same : after.mass leaf shell = (State.mk slots store.temp).mass leaf shell) :
    (store.replace active after.slots after.temp).mass leaf shell = store.mass leaf shell := by
  have equation := store.replace_mass live after.slots after.temp leaf shell
  simp only [State.mass] at same
  omega

theorem handoff_mass {n : Nat} (store : Store (n + 1) Atom) (frame : Frame n)
    {caller slots : Region (n + 1) Atom} (live : store.region frame.region = some caller)
    (installed : (Op.put frame.destination).exec ⟨caller, store.temp⟩ = some ⟨slots, none⟩)
    (leaf : Atom → Nat) (shell : Shell → Nat) :
    (store.replace frame.region slots none).mass leaf shell = store.mass leaf shell := by
  apply local_mass store live ⟨slots, none⟩ leaf shell
  cases Op.effect_of_exec installed with
  | @put _ _ lens value found resident available =>
    have equation := frame.destination.mass_write (State.mk caller store.temp) lens found (some value) none leaf shell
    rw [vacant_mass_zero _ _ available] at equation
    simp only [Nat.add_zero] at equation
    change store.temp = some value at resident
    rw [resident] at equation
    simp only [State.mass, cellMass, resident] at equation ⊢
    omega

theorem Preserves.local {n : Nat} {signature : Signature} (store : Store (n + 1) Atom)
    {active : Nat} {slots : Region (n + 1) Atom} (live : store.region active = some slots)
    {after : State (n + 1)} (preserved : Conserves signature ⟨slots, store.temp⟩ after)
    (beforeControl afterControl : Control n) (stack : List (Frame n)) :
    Preserves signature ⟨beforeControl, store, active, stack⟩
      ⟨afterControl, store.replace active after.slots after.temp, active, stack⟩ := by
  constructor
  · intro i
    have equation := store.replace_mass live after.slots after.temp (Atom.weight i) (fun _ => 0)
    have bound := preserved.bounded i
    change (store.replace active after.slots after.temp).mass _ _ ≤ store.mass _ _
    simp only [State.count, weight] at bound
    omega
  · intro i exact
    have equation := store.replace_mass live after.slots after.temp (Atom.weight i) (fun _ => 0)
    have same := preserved.exact i exact
    change (store.replace active after.slots after.temp).mass _ _ = store.mass _ _
    simp only [State.count, weight] at same
    omega

theorem Preserves.of_mass {n : Nat} {signature : Signature} {before after : Configuration n}
    (same : ∀ leaf shell, after.mass leaf shell = before.mass leaf shell) : Preserves signature before after :=
  ⟨fun i => Nat.le_of_eq (same (Atom.weight i) (fun _ => 0)), fun i _ => same (Atom.weight i) (fun _ => 0)⟩

/-- Every resident is counted once in the store, regardless of how many control
frames refer to a region. Neither allocation nor handoff copies an owner. -/
theorem Safe.ownership_step {n : Nat} {program : Program n} {signature : Signature} {final : Context (n + 1)}
    {before after : Configuration n} (safe : Safe program signature final before)
    (step : Transition program before after) : Preserves signature before after := by
  cases step with
  | operation live step =>
    cases safe with
    | body found typed checked retained =>
      cases Option.some.inj (live.symm.trans found)
      obtain ⟨_, preserved⟩ := OwnershipMir.Safe.step ⟨_, typed, checked⟩ Instruction.Checked.executed step
      exact Preserves.local _ live preserved _ _ _
  | enter resolved resident => exact Preserves.of_mass (enter_mass _ _ resident)
  | handoff live installed => exact Preserves.of_mass (handoff_mass _ _ live installed)
  | clean live step =>
    cases safe with
    | cleaning found typed checked retained =>
      cases Option.some.inj (live.symm.trans found)
      obtain ⟨_, preserved⟩ := OwnershipMir.Safe.step ⟨_, typed, checked⟩ Op.Checked.executed step
      exact Preserves.local _ live preserved _ _ _
  | retire empty register =>
    apply Preserves.of_mass
    intro leaf shell
    have equation := Store.retire_mass _ empty leaf shell
    simpa [Configuration.mass, cellMass, total_zero] using equation

theorem Safe.ownership_execution {n : Nat} {program : Program n} {signature : Signature} {final : Context (n + 1)}
    (functions : program.Checked) {before after : Configuration n} (safe : Safe program signature final before)
    (run : Run (Transition program) before after) : Preserves signature before after := by
  induction run with
  | refl => exact Preserves.refl _ _
  | step head tail ih => exact (safe.ownership_step head).trans (ih (safe.preservation functions head))

theorem ownership_safety {n : Nat} {program : Program n} {signature : Signature} {final : Context (n + 1)}
    (functions : program.Checked) {before after : Configuration n} (safe : Safe program signature final before)
    (unique : before.Unique) (run : Run (Transition program) before after) :
    Safe program signature final after ∧ after.Unique ∧ Preserves signature before after ∧
      (after.Terminal ∨ ∃ next, Transition program after next) := by
  have preserved := safe.execution functions run
  have owned := safe.ownership_execution functions run
  exact ⟨preserved, owned.unique unique, owned, preserved.progress⟩

end OwnershipMir.Calls
