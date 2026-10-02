import OwnershipMir.CallOwnership

namespace OwnershipMir.Calls


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

/-- Nontermination is an actual infinite transition sequence, not stuckness.
Recursive calls need only their checked declaration/body contracts. -/
theorem Safe.diverges_iff {n : Nat} {program : Program n} {signature : Signature} {final : Context (n + 1)}
    (functions : program.Checked) {start : Configuration n} (safe : Safe program signature final start) :
    Diverges (Transition program) start ↔ ¬ ∃ result, Run (Transition program) start result ∧ result.Terminal := by
  constructor
  · intro infinite ⟨result, run, terminal⟩
    exact run.excludes_divergence Transition.deterministic (fun _ step => step.not_terminal terminal) infinite
  · intro absent
    classical
    have advances : ∀ config, Run (Transition program) start config → ∃ next, Transition program config next := by
      intro config reached
      rcases (safe.execution functions reached).progress with terminal | next
      · exact False.elim (absent ⟨config, reached, terminal⟩)
      · exact next
    exact diverges_of_progress advances

theorem infinite_prefix_safety {n : Nat} {program : Program n} {signature : Signature} {final : Context (n + 1)}
    (functions : program.Checked) {start : Configuration n} (safe : Safe program signature final start)
    (unique : start.Unique) {trace : Nat → Configuration n} (initial : trace 0 = start)
    (steps : ∀ i, Transition program (trace i) (trace (i + 1))) (i : Nat) :
    Safe program signature final (trace i) ∧ (trace i).Unique ∧ Preserves signature start (trace i) := by
  have reached := trace_reachable initial steps
  have safety := ownership_safety functions safe unique (reached i)
  exact ⟨safety.1, safety.2.1, safety.2.2.1⟩

end OwnershipMir.Calls
