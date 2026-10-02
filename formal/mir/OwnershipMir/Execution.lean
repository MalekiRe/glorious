namespace OwnershipMir

/-- Finite execution over any concrete transition relation. -/
inductive Run {σ : Type} (next : σ → σ → Prop) : σ → σ → Prop where
  | refl (state) : Run next state state
  | step {before middle after} (head : next before middle) (tail : Run next middle after) : Run next before after

def Diverges {σ : Type} (next : σ → σ → Prop) (start : σ) : Prop :=
  ∃ trace : Nat → σ, trace 0 = start ∧ ∀ i, next (trace i) (trace (i + 1))

theorem Run.trans {σ : Type} {next : σ → σ → Prop} {a b c : σ}
    (first : Run next a b) (last : Run next b c) : Run next a c := by
  induction first with
  | refl => exact last
  | step head tail ih => exact .step head (ih last)

theorem Run.from_terminal {σ : Type} {next : σ → σ → Prop} {before after : σ}
    (run : Run next before after) (stopped : ∀ state, ¬ next before state) : after = before := by
  cases run with
  | refl => rfl
  | step head _ => exact False.elim (stopped _ head)

theorem Run.compare {σ : Type} {next : σ → σ → Prop} {before left right : σ}
    (a : Run next before left) (b : Run next before right)
    (deterministic : ∀ {s x y}, next s x → next s y → x = y) :
    Run next left right ∨ Run next right left := by
  induction a with
  | refl => exact Or.inl b
  | step head tail ih =>
    cases b with
    | refl => exact Or.inr (.step head tail)
    | step first rest => cases deterministic head first; exact ih rest

theorem Run.terminal_unique {σ : Type} {next : σ → σ → Prop} {start left right : σ}
    (a : Run next start left) (b : Run next start right)
    (deterministic : ∀ {s x y}, next s x → next s y → x = y)
    (leftStopped : ∀ state, ¬ next left state) (rightStopped : ∀ state, ¬ next right state) : left = right := by
  rcases a.compare b deterministic with remaining | remaining
  · exact (remaining.from_terminal leftStopped).symm
  · exact remaining.from_terminal rightStopped

theorem Run.excludes_divergence {σ : Type} {next : σ → σ → Prop} {before after : σ}
    (run : Run next before after) (deterministic : ∀ {s x y}, next s x → next s y → x = y)
    (stopped : ∀ state, ¬ next after state) : ¬ Diverges next before := by
  induction run with
  | refl =>
    rintro ⟨trace, initial, steps⟩
    exact stopped _ (initial ▸ steps 0)
  | @step before middle after head tail ih =>
    rintro ⟨trace, initial, steps⟩
    have first : next before (trace 1) := by simpa [initial] using steps 0
    have same := deterministic head first
    exact ih stopped ⟨fun i => trace (i + 1), same.symm, fun i => by simpa [Nat.add_assoc] using steps (i + 1)⟩

theorem Run.diverges_iff {σ : Type} {next : σ → σ → Prop} {before after : σ}
    (run : Run next before after) (deterministic : ∀ {s x y}, next s x → next s y → x = y) :
    Diverges next before ↔ Diverges next after := by
  induction run with
  | refl => rfl
  | @step before middle after head tail ih =>
    constructor
    · rintro ⟨trace, initial, steps⟩
      have first : next before (trace 1) := by simpa [initial] using steps 0
      have same := deterministic head first
      exact ih.mp ⟨fun i => trace (i + 1), same.symm, fun i => by simpa [Nat.add_assoc] using steps (i + 1)⟩
    · intro infinite
      obtain ⟨trace, initial, steps⟩ := ih.mpr infinite
      refine ⟨fun i => match i with | 0 => before | j + 1 => trace j, rfl, ?_⟩
      intro i
      cases i with
      | zero => simpa [initial] using head
      | succ i => exact steps i

/-- Reachable progress constructs an actual infinite trace; no machine or
ownership interface is required. -/
theorem diverges_of_progress {σ : Type} {next : σ → σ → Prop} {start : σ}
    (advances : ∀ state, Run next start state → ∃ after, next state after) : Diverges next start := by
  classical
  let trace : Nat → {state : σ // Run next start state} :=
    Nat.rec ⟨start, .refl _⟩ (fun _ previous =>
      ⟨Classical.choose (advances previous.val previous.property),
        previous.property.trans (.step (Classical.choose_spec (advances previous.val previous.property)) (.refl _))⟩)
  exact ⟨fun i => (trace i).val, rfl, fun i => Classical.choose_spec (advances (trace i).val (trace i).property)⟩

theorem trace_reachable {σ : Type} {next : σ → σ → Prop} {start : σ} {trace : Nat → σ}
    (initial : trace 0 = start) (steps : ∀ i, next (trace i) (trace (i + 1))) (i : Nat) : Run next start (trace i) := by
  induction i with
  | zero => exact initial.symm ▸ Run.refl start
  | succ i ih => exact ih.trans (.step (steps i) (.refl _))

end OwnershipMir
