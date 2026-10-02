import OwnershipMir.CallSafety

namespace OwnershipMir.Calls

def stackMass {n : Nat} (leaf : Atom → Nat) (shell : Shell → Nat) : List (Frame n) → Nat
  | [] => 0
  | frame :: rest => frame.state.mass leaf shell + stackMass leaf shell rest

def Configuration.mass {n : Nat} (config : Configuration n) (leaf : Atom → Nat) (shell : Shell → Nat) : Nat :=
  config.state.mass leaf shell + stackMass leaf shell config.stack

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

/-- Fresh activation storage and suspended caller storage partition the old
residents. Argument transfer is equality for every additive tree measure. -/
theorem enter_mass {n : Nat} (state : State (n + 1)) (stack : List (Frame n))
    (next : Body n) (cleanup : Code (n + 1) (Op (n + 1))) (destination : Place (n + 1))
    (argument : Value) (resident : state.temp = some argument) (leaf : Atom → Nat) (shell : Shell → Nat) :
    (State.mk (argumentSlots argument) none : State (n + 1)).mass leaf shell +
        stackMass leaf shell (⟨state.slots, next, cleanup, destination⟩ :: stack) =
      state.mass leaf shell + stackMass leaf shell stack := by
  rw [argument_mass]
  simp [stackMass, Frame.state, State.mass, resident, cellMass, Nat.add_comm, Nat.add_left_comm]

/-- Protecting the result moves its actual resident into the caller before any
callee cleanup. The same equality covers opaque owners and fieldless shells. -/
theorem handoff_mass {n : Nat} (state : State (n + 1)) (frame : Frame n) (stack : List (Frame n))
    {slots : Fin (n + 1) → Option Value}
    (installed : (Op.put frame.destination).exec ⟨frame.slots, state.temp⟩ = some ⟨slots, none⟩)
    (leaf : Atom → Nat) (shell : Shell → Nat) :
    (State.mk state.slots none).mass leaf shell + stackMass leaf shell ({frame with slots := slots} :: stack) =
      state.mass leaf shell + stackMass leaf shell (frame :: stack) := by
  cases Op.effect_of_exec installed with
  | @put _ _ lens value found live available =>
    change state.temp = some value at live
    have equation := frame.destination.mass_write (State.mk frame.slots state.temp) lens found (some value) none leaf shell
    rw [vacant_mass_zero _ _ available, live] at equation
    simp only [State.mass, cellMass, Nat.add_zero] at equation
    simp only [stackMass, Frame.state, State.mass, cellMass, Nat.add_zero, live]
    omega

theorem Preserves.local {n : Nat} {signature : Signature} {state after : State (n + 1)}
    (preserved : Conserves signature state after) (beforeControl afterControl : Control n) (stack : List (Frame n)) :
    Preserves signature ⟨beforeControl, state, stack⟩ ⟨afterControl, after, stack⟩ := by
  exact ⟨fun i => Nat.add_le_add_right (preserved.bounded i) _,
    fun i exact => congrArg (· + stackMass (Atom.weight i) (fun _ => 0) stack) (preserved.exact i exact)⟩

theorem Preserves.of_mass {n : Nat} {signature : Signature} {before after : Configuration n}
    (same : ∀ leaf shell, after.mass leaf shell = before.mass leaf shell) : Preserves signature before after :=
  ⟨fun i => by change after.mass _ _ ≤ before.mass _ _; exact Nat.le_of_eq (same _ _), fun i _ => same _ _⟩

/-- Counts cover the active region AND every suspended caller. Per-frame
uniqueness alone would not prevent a duplicated owner across activations. -/
theorem Safe.ownership_step {n : Nat} {program : Program n} {signature : Signature} {final : Context (n + 1)}
    {before after : Configuration n} (safe : Safe program signature final before)
    (step : Transition program before after) : Preserves signature before after := by
  cases step with
  | operation step =>
    cases safe with
    | body typed checked retained =>
      obtain ⟨_, preserved⟩ :=
        OwnershipMir.Safe.step ⟨_, typed, checked⟩ Instruction.Checked.executed step
      exact Preserves.local preserved _ _ _
  | enter resolved resident =>
    apply Preserves.of_mass
    intro leaf shell
    exact enter_mass _ _ _ _ _ _ resident leaf shell
  | handoff installed =>
    apply Preserves.of_mass
    intro leaf shell
    exact handoff_mass _ _ _ installed leaf shell
  | clean step =>
    cases safe with
    | cleaning typed checked retained =>
      have start : OwnershipMir.Safe signature Op.Checked _ ⟨_, _⟩ := ⟨_, typed, checked⟩
      exact Preserves.local (start.step Op.Checked.executed step).2 _ _ _
  | retire =>
    apply Preserves.of_mass
    intro leaf shell
    simp [Configuration.mass, stackMass, empty_mass]

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
