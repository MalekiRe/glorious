import OwnershipMir.CallOwnership

namespace OwnershipMir.Calls

theorem Execution.trans {n : Nat} {program : Program n} {a b c : Configuration n}
    (first : Execution program a b) (last : Execution program b c) : Execution program a c := by
  induction first with
  | refl => exact last
  | step head tail ih => exact .step head (ih last)

theorem Transition.not_terminal {n : Nat} {program : Program n} {before after : Configuration n}
    (step : Transition program before after) : ¬ before.Terminal := by
  intro ⟨cleanup, halted, empty⟩
  cases step with
  | operation step => cases halted; exact step.not_halt rfl
  | enter => cases halted
  | handoff => cases empty
  | clean => cases halted
  | retire => cases halted

theorem Transition.deterministic {n : Nat} {program : Program n} {before first second : Configuration n}
    (left : Transition program before first) (right : Transition program before second) : first = second := by
  cases left with
  | operation left =>
    cases right with
    | operation right => cases left.deterministic right; rfl
    | enter => cases left with | act executed => cases executed
    | handoff => exact False.elim (left.not_halt rfl)
  | enter resolved resident =>
    cases right with
    | operation right => cases right with | act executed => cases executed
    | enter selected live => cases Option.some.inj (resolved.symm.trans selected); cases Option.some.inj (resident.symm.trans live); rfl
  | handoff installed =>
    cases right with
    | operation right => exact False.elim (right.not_halt rfl)
    | handoff other => cases Option.some.inj (installed.symm.trans other); rfl
  | clean left =>
    cases right with
    | clean right => cases left.deterministic right; rfl
    | retire => exact False.elim (left.not_halt rfl)
  | retire =>
    cases right with
    | clean right => exact False.elim (right.not_halt rfl)
    | retire => rfl

theorem Execution.from_terminal {n : Nat} {program : Program n} {before after : Configuration n}
    (run : Execution program before after) (terminal : before.Terminal) : after = before := by
  cases run with
  | refl => rfl
  | step head _ => exact False.elim (head.not_terminal terminal)

theorem Execution.compare {n : Nat} {program : Program n} {before first second : Configuration n}
    (left : Execution program before first) (right : Execution program before second) :
    Execution program first second ∨ Execution program second first := by
  induction left with
  | refl => exact Or.inl right
  | step head tail ih =>
    cases right with
    | refl => exact Or.inr (.step head tail)
    | step first rest => cases head.deterministic first; exact ih rest

def Diverges {n : Nat} (program : Program n) (start : Configuration n) : Prop :=
  ∃ trace : Nat → Configuration n, trace 0 = start ∧ ∀ i, Transition program (trace i) (trace (i + 1))

theorem Execution.excludes_divergence {n : Nat} {program : Program n} {before after : Configuration n}
    (run : Execution program before after) (terminal : after.Terminal) : ¬ Diverges program before := by
  induction run with
  | refl =>
    rintro ⟨trace, initial, steps⟩
    exact (steps 0).not_terminal (initial.symm ▸ terminal)
  | @step before middle after head tail ih =>
    rintro ⟨trace, initial, steps⟩
    have first : Transition program before (trace 1) := by simpa [initial] using steps 0
    have same := head.deterministic first
    exact ih terminal ⟨fun i => trace (i + 1), same.symm, fun i => by simpa [Nat.add_assoc] using steps (i + 1)⟩

/-- A concrete call or cleanup prefix neither creates nor hides divergence. -/
theorem Execution.diverges_iff {n : Nat} {program : Program n} {before after : Configuration n}
    (run : Execution program before after) : Diverges program before ↔ Diverges program after := by
  induction run with
  | refl => rfl
  | @step before middle after head tail ih =>
    constructor
    · rintro ⟨trace, initial, steps⟩
      have first : Transition program before (trace 1) := by simpa [initial] using steps 0
      have same := head.deterministic first
      exact ih.mp ⟨fun i => trace (i + 1), same.symm, fun i => by simpa [Nat.add_assoc] using steps (i + 1)⟩
    · intro infinite
      obtain ⟨trace, initial, steps⟩ := ih.mpr infinite
      refine ⟨fun i => match i with | 0 => _ | j + 1 => trace j, rfl, ?_⟩
      intro i
      cases i with
      | zero => simpa [initial] using head
      | succ i => exact steps i

/-- Nontermination is an actual infinite transition sequence, not stuckness.
Recursive calls need only their checked declaration/body contracts. -/
theorem Safe.diverges_iff {n : Nat} {program : Program n} {signature : Signature} {final : Context (n + 1)}
    (functions : program.Checked) {start : Configuration n} (safe : Safe program signature final start) :
    Diverges program start ↔ ¬ ∃ result, Execution program start result ∧ result.Terminal := by
  constructor
  · intro infinite ⟨result, run, terminal⟩
    exact run.excludes_divergence terminal infinite
  · intro absent
    classical
    have advances : ∀ config, Execution program start config → ∃ next, Transition program config next := by
      intro config reached
      rcases (safe.execution functions reached).progress with terminal | next
      · exact False.elim (absent ⟨config, reached, terminal⟩)
      · exact next
    let trace : Nat → {config : Configuration n // Execution program start config} :=
      Nat.rec ⟨start, .refl _⟩ (fun _ previous =>
        ⟨Classical.choose (advances previous.val previous.property),
          previous.property.trans (.step (Classical.choose_spec (advances previous.val previous.property)) (.refl _))⟩)
    exact ⟨fun i => (trace i).val, rfl, fun i => Classical.choose_spec (advances (trace i).val (trace i).property)⟩

theorem infinite_prefix_safety {n : Nat} {program : Program n} {signature : Signature} {final : Context (n + 1)}
    (functions : program.Checked) {start : Configuration n} (safe : Safe program signature final start)
    (unique : start.Unique) {trace : Nat → Configuration n} (initial : trace 0 = start)
    (steps : ∀ i, Transition program (trace i) (trace (i + 1))) (i : Nat) :
    Safe program signature final (trace i) ∧ (trace i).Unique ∧ Preserves signature start (trace i) := by
  have reached : ∀ i, Execution program start (trace i) := by
    intro j
    induction j with
    | zero => exact initial.symm ▸ Execution.refl start
    | succ j ih => exact ih.trans (.step (steps j) (.refl _))
  have safety := ownership_safety functions safe unique (reached i)
  exact ⟨safety.1, safety.2.1, safety.2.2.1⟩

end OwnershipMir.Calls
