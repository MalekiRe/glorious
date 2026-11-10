import Glorious.Machine

/-!
# Forward simulation between deterministic machines

A forward simulation says: whenever the source machine takes a step, the target
machine takes at least one step and the two stay related. Because both machines
are deterministic, this one-directional fact is enough to transfer every
behaviour in both directions.
-/

namespace Glorious

open Machine

variable {σ₁ σ₂ ν : Type}

/--
`R` is a forward simulation from the source machine `stepS` to the target machine
`stepT`. Each source step is matched by one or more target steps.
-/
structure ForwardSim (stepS : σ₁ → Step σ₁ ν) (stepT : σ₂ → Step σ₂ ν)
    (R : σ₁ → σ₂ → Prop) : Prop where
  next : ∀ {s : σ₁} {t : σ₂} {s' : σ₁}, R s t → stepS s = .next s' →
    ∃ k t', run stepT (k + 1) t = .next t' ∧ R s' t'
  halt : ∀ {s : σ₁} {t : σ₂} {v : ν}, R s t → stepS s = .halt v →
    ∃ k, run stepT (k + 1) t = .halt v

namespace ForwardSim

variable {stepS : σ₁ → Step σ₁ ν} {stepT : σ₂ → Step σ₂ ν} {R : σ₁ → σ₂ → Prop}

/-- If the source is still running after `n` steps, the target is still running
after at least `n` steps, in a related state. -/
theorem run_next (sim : ForwardSim stepS stepT R) :
    ∀ (n : Nat) {s : σ₁} {t : σ₂} {s' : σ₁}, R s t → run stepS n s = .next s' →
      ∃ m t', n ≤ m ∧ run stepT m t = .next t' ∧ R s' t' := by
  intro n
  induction n with
  | zero =>
    intro s t s' hR h
    rw [run_zero] at h
    cases h
    exact ⟨0, t, Nat.le_refl 0, rfl, hR⟩
  | succ n ih =>
    intro s t s' hR h
    rw [run_succ] at h
    cases hs : stepS s with
    | next s₁ =>
      rw [hs, Step.bind_next] at h
      obtain ⟨k, t₁, hk, hR₁⟩ := sim.next hR hs
      obtain ⟨m, t', hnm, hm, hR'⟩ := ih hR₁ h
      refine ⟨(k + 1) + m, t', by omega, ?_, hR'⟩
      rw [run_add, hk, Step.bind_next]
      exact hm
    | halt v => rw [hs] at h; simp at h
    | stuck => rw [hs] at h; simp at h

/-- If the source halts within `n` steps, the target halts with the same result. -/
theorem run_halt (sim : ForwardSim stepS stepT R) :
    ∀ (n : Nat) {s : σ₁} {t : σ₂} {v : ν}, R s t → run stepS n s = .halt v →
      ∃ m, run stepT m t = .halt v := by
  intro n
  induction n with
  | zero =>
    intro s t v _ h
    rw [run_zero] at h
    cases h
  | succ n ih =>
    intro s t v hR h
    rw [run_succ] at h
    cases hs : stepS s with
    | next s₁ =>
      rw [hs, Step.bind_next] at h
      obtain ⟨k, t₁, hk, hR₁⟩ := sim.next hR hs
      obtain ⟨m, hm⟩ := ih hR₁ h
      refine ⟨(k + 1) + m, ?_⟩
      rw [run_add, hk, Step.bind_next]
      exact hm
    | halt w =>
      rw [hs, Step.bind_halt] at h
      cases h
      obtain ⟨k, hk⟩ := sim.halt hR hs
      exact ⟨k + 1, hk⟩
    | stuck => rw [hs] at h; simp at h

/-- Halting is preserved. -/
theorem halts (sim : ForwardSim stepS stepT R) {s : σ₁} {t : σ₂} {v : ν} (hR : R s t) :
    Halts stepS s v → Halts stepT t v :=
  fun ⟨n, h⟩ => sim.run_halt n hR h

/-- Divergence is preserved. -/
theorem diverges (sim : ForwardSim stepS stepT R) {s : σ₁} {t : σ₂} (hR : R s t)
    (hd : Diverges stepS s) : Diverges stepT t := by
  intro m
  obtain ⟨s', hs'⟩ := hd m
  obtain ⟨m', _, hle, ht', _⟩ := sim.run_next m hR hs'
  exact run_next_of_le ht' hle

/-- Halting is reflected: a halting target run comes from a source run that
halts with the same result, unless the source goes wrong. -/
theorem halts_reflect (sim : ForwardSim stepS stepT R) {s : σ₁} {t : σ₂} {v : ν} (hR : R s t) :
    Halts stepT t v → Halts stepS s v ∨ GoesWrong stepS s := by
  intro ⟨m, hm⟩
  cases hs : run stepS m s with
  | next s' =>
    obtain ⟨m', _, hle, ht', _⟩ := sim.run_next m hR hs
    rw [run_halt_mono hm hle] at ht'
    cases ht'
  | halt w =>
    obtain ⟨m', hm'⟩ := sim.run_halt m hR hs
    cases halt_unique hm' hm
    exact Or.inl ⟨m, hs⟩
  | stuck => exact Or.inr ⟨m, hs⟩

/-- A source program that never goes wrong compiles to a target that never goes wrong. -/
theorem not_goesWrong (sim : ForwardSim stepS stepT R) {s : σ₁} {t : σ₂} (hR : R s t)
    (safe : ¬ GoesWrong stepS s) : ¬ GoesWrong stepT t := by
  intro ⟨m, hm⟩
  cases hs : run stepS m s with
  | next s' =>
    obtain ⟨m', _, hle, ht', _⟩ := sim.run_next m hR hs
    rw [run_stuck_mono hm hle] at ht'
    cases ht'
  | halt w =>
    obtain ⟨m', hm'⟩ := sim.run_halt m hR hs
    have a := run_stuck_mono hm (Nat.le_max_left m m')
    have b := run_halt_mono hm' (Nat.le_max_right m m')
    rw [a] at b
    cases b
  | stuck => exact safe ⟨m, hs⟩

/-- Divergence is reflected for source programs that never go wrong. -/
theorem diverges_reflect (sim : ForwardSim stepS stepT R) {s : σ₁} {t : σ₂} (hR : R s t)
    (safe : ¬ GoesWrong stepS s) (hd : Diverges stepT t) : Diverges stepS s := by
  intro n
  cases hs : run stepS n s with
  | next s' => exact ⟨s', rfl⟩
  | halt w =>
    obtain ⟨m, hm⟩ := sim.run_halt n hR hs
    obtain ⟨t', ht'⟩ := hd m
    rw [hm] at ht'
    cases ht'
  | stuck => exact absurd ⟨n, hs⟩ safe

end ForwardSim

end Glorious
