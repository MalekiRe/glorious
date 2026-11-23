module

public import Glorious.Machine

/-!
# Forward simulation between deterministic machines

A forward simulation says: whenever the source machine takes a step, the target
machine takes at least one step and the two stay related. Because both machines
are deterministic, this one-directional fact is enough to transfer every
behaviour in both directions.
-/

@[expose] public section

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
    rw [run_zero] at h; cases h
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
    rw [run_zero] at h; cases h
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
      rw [hs, Step.bind_halt] at h; cases h
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
    rw [a] at b; cases b
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

/-- Every state the source reaches is matched by a state the target reaches. -/
theorem reaches (sim : ForwardSim stepS stepT R) {s : σ₁} {t : σ₂} {s' : σ₁} (hR : R s t) :
    Reaches stepS s s' → ∃ t', Reaches stepT t t' ∧ R s' t' := by
  intro ⟨n, h⟩
  obtain ⟨m, t', _, ht', hR'⟩ := sim.run_next n hR h
  exact ⟨t', ⟨m, ht'⟩, hR'⟩

/--
Observations are reflected. Suppose related states have the same observation
and the target's observation only grows. Then whatever the target has observed
at any point is a prefix of what the source observes at some point, or of what
it finally observes when it halts.
-/
theorem obs_reflect {α : Type} (sim : ForwardSim stepS stepT R)
    (obsS : σ₁ → List α) (obsT : σ₂ → List α) (final : ν → List α)
    (hobs : ∀ {s : σ₁} {t : σ₂}, R s t → obsS s = obsT t)
    (hstep : ∀ {t t' : σ₂}, stepT t = .next t' → obsT t <+: obsT t')
    (hhalt : ∀ {t : σ₂} {v : ν}, stepT t = .halt v → obsT t <+: final v)
    {s : σ₁} {t t' : σ₂} (hR : R s t) (safe : ¬ GoesWrong stepS s) (h : Reaches stepT t t') :
    (∃ s', Reaches stepS s s' ∧ obsT t' <+: obsS s')
      ∨ (∃ v, Halts stepS s v ∧ obsT t' <+: final v) := by
  obtain ⟨m, hm⟩ := h
  cases hs : run stepS m s with
  | next s' =>
    obtain ⟨m', t'', hle, ht'', hR'⟩ := sim.run_next m hR hs
    have e : m' = m + (m' - m) := by omega
    rw [e, run_add, hm, Step.bind_next] at ht''
    refine Or.inl ⟨s', ⟨m, hs⟩, ?_⟩
    rw [hobs hR']
    exact run_obs_prefix obsT hstep _ ht''
  | halt v =>
    obtain ⟨m', hm'⟩ := sim.run_halt m hR hs
    by_cases hle : m' ≤ m
    · rw [run_halt_mono hm' hle] at hm; cases hm
    · have e : m' = m + (m' - m) := by omega
      rw [e, run_add, hm, Step.bind_next] at hm'
      exact Or.inr ⟨v, ⟨m, hs⟩, run_obs_prefix_halt obsT final hstep hhalt _ hm'⟩
  | stuck => exact absurd ⟨m, hs⟩ safe

end ForwardSim

/--
A forward simulation that also accounts for the target's intermediate states.
`I s t` says the target state `t` is at source state `s` or on its way there.
A source step is matched by one target step and then a run all of whose states
are on the way to the new source state.
-/
structure ForwardSimThrough (stepS : σ₁ → Step σ₁ ν) (stepT : σ₂ → Step σ₂ ν)
    (R : σ₁ → σ₂ → Prop) (I : σ₁ → σ₂ → Prop) : Prop where
  rel : ∀ {s : σ₁} {t : σ₂}, R s t → I s t
  next : ∀ {s : σ₁} {t : σ₂} {s' : σ₁}, R s t → stepS s = .next s' →
    ∃ k t₀ t', stepT t = .next t₀ ∧ RunsThrough stepT (I s') k t₀ t' ∧ R s' t'
  halt : ∀ {s : σ₁} {t : σ₂} {v : ν}, R s t → stepS s = .halt v → stepT t = .halt v

namespace ForwardSimThrough

variable {stepS : σ₁ → Step σ₁ ν} {stepT : σ₂ → Step σ₂ ν} {R I : σ₁ → σ₂ → Prop}

/-- Every state the target reaches is at, or on its way to, a state the source
reaches, provided the source does not go wrong. -/
theorem reflect (sim : ForwardSimThrough stepS stepT R I) (m : Nat) {s : σ₁} {t d : σ₂}
    (hR : R s t) (safe : ¬ GoesWrong stepS s) (hm : run stepT m t = .next d) :
    ∃ c, Reaches stepS s c ∧ I c d := by
  cases m with
  | zero =>
    rw [run_zero] at hm; cases hm
    exact ⟨s, ⟨0, rfl⟩, sim.rel hR⟩
  | succ m =>
    cases hs : stepS s with
    | stuck => exact absurd ⟨1, by simp [run_succ, hs]⟩ safe
    | halt v =>
      rw [run_succ, sim.halt hR hs] at hm
      simp at hm
    | next s' =>
      obtain ⟨k, t₀, t', h0, hthrough, hR'⟩ := sim.next hR hs
      rw [run_succ, h0, Step.bind_next] at hm
      have safe' : ¬ GoesWrong stepS s' := fun ⟨n, hn⟩ =>
        safe ⟨n + 1, by rw [run_succ, hs, Step.bind_next]; exact hn⟩
      by_cases hle : m ≤ k
      · obtain ⟨tj, htj, hI⟩ := hthrough.2 m hle
        rw [htj] at hm; cases hm
        exact ⟨s', ⟨1, by simp [run_succ, hs]⟩, hI⟩
      · have e : m = k + (m - k) := by omega
        rw [e, run_add, hthrough.1, Step.bind_next] at hm
        obtain ⟨c, ⟨n, hn⟩, hI⟩ := reflect sim (m - k) hR' safe' hm
        exact ⟨c, ⟨n + 1, by rw [run_succ, hs, Step.bind_next]; exact hn⟩, hI⟩
termination_by m
decreasing_by omega

end ForwardSimThrough

end Glorious
