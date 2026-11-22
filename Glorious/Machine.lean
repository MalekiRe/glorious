module

/-!
# Deterministic machines

Both the Core semantics and the bytecode semantics are given as a total step
function. This file defines what it means to run such a machine and the three
observable behaviours of a program: it halts with a value, it goes wrong, or it
runs forever.
-/

@[expose] public section

namespace Glorious

/-- The result of one machine step. -/
inductive Step (σ ν : Type) where
  /-- The machine moved to a new state. -/
  | next (s : σ)
  /-- The machine finished with a result. -/
  | halt (v : ν)
  /-- No rule applies to this state: the program went wrong. -/
  | stuck

namespace Step

variable {σ ν : Type}

instance : Inhabited (Step σ ν) := ⟨.stuck⟩

/-- Continue with `f` if the step produced a new state; otherwise keep the outcome. -/
def bind (r : Step σ ν) (f : σ → Step σ ν) : Step σ ν :=
  match r with
  | .next s => f s
  | .halt v => .halt v
  | .stuck => .stuck

@[simp] theorem bind_next (s : σ) (f : σ → Step σ ν) : (Step.next s).bind f = f s := rfl

@[simp] theorem bind_halt (v : ν) (f : σ → Step σ ν) :
    (Step.halt v : Step σ ν).bind f = .halt v := rfl

@[simp] theorem bind_stuck (f : σ → Step σ ν) : (Step.stuck : Step σ ν).bind f = .stuck := rfl

end Step

namespace Machine

variable {σ ν : Type}

/--
Run at most `n` steps. `.next s` means the machine is still running, in state `s`,
after exactly `n` steps. Halting and getting stuck are final.
-/
def run (step : σ → Step σ ν) : Nat → σ → Step σ ν
  | 0, s => .next s
  | n + 1, s => (step s).bind (run step n)

/-- The machine started in `s` finishes with result `v`. -/
def Halts (step : σ → Step σ ν) (s : σ) (v : ν) : Prop :=
  ∃ n, run step n s = .halt v

/-- The machine started in `s` reaches a state with no applicable rule. -/
def GoesWrong (step : σ → Step σ ν) (s : σ) : Prop :=
  ∃ n, run step n s = .stuck

/-- The machine started in `s` runs forever. -/
def Diverges (step : σ → Step σ ν) (s : σ) : Prop :=
  ∀ n, ∃ s', run step n s = .next s'

/-- The machine started in `s` is in state `s'` after some number of steps. -/
def Reaches (step : σ → Step σ ν) (s s' : σ) : Prop :=
  ∃ n, run step n s = .next s'

variable {step : σ → Step σ ν}

@[simp] theorem run_zero (s : σ) : run step 0 s = .next s := rfl

theorem run_succ (n : Nat) (s : σ) : run step (n + 1) s = (step s).bind (run step n) := rfl

/-- Running `a + b` steps is running `a` steps and then `b` more. -/
theorem run_add (a b : Nat) (s : σ) :
    run step (a + b) s = (run step a s).bind (run step b) := by
  induction a generalizing s with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih =>
    have h : a + 1 + b = (a + b) + 1 := by omega
    rw [h]
    show (step s).bind (run step (a + b)) = ((step s).bind (run step a)).bind (run step b)
    cases step s with
    | next s' => exact ih s'
    | halt v => rfl
    | stuck => rfl

theorem run_one_halt {s : σ} {v : ν} (h : step s = .halt v) : run step (0 + 1) s = .halt v := by
  simp [run_succ, h]

/-- A halted machine stays halted with the same result. -/
theorem run_halt_mono {n m : Nat} {s : σ} {v : ν}
    (h : run step n s = .halt v) (hm : n ≤ m) : run step m s = .halt v := by
  have e : m = n + (m - n) := by omega
  rw [e, run_add, h]
  rfl

/-- A stuck machine stays stuck. -/
theorem run_stuck_mono {n m : Nat} {s : σ}
    (h : run step n s = .stuck) (hm : n ≤ m) : run step m s = .stuck := by
  have e : m = n + (m - n) := by omega
  rw [e, run_add, h]
  rfl

/-- A machine still running after `m` steps was still running after any `n ≤ m` steps. -/
theorem run_next_of_le {n m : Nat} {s t : σ}
    (h : run step m s = .next t) (hm : n ≤ m) : ∃ s', run step n s = .next s' := by
  have e : m = n + (m - n) := by omega
  rw [e, run_add] at h
  cases hr : run step n s with
  | next s' => exact ⟨s', rfl⟩
  | halt v => rw [hr] at h; simp at h
  | stuck => rw [hr] at h; simp at h

/-- The result of a halting run does not depend on how much fuel was supplied. -/
theorem halt_unique {n m : Nat} {s : σ} {v w : ν}
    (h₁ : run step n s = .halt v) (h₂ : run step m s = .halt w) : v = w := by
  have a := run_halt_mono h₁ (Nat.le_max_left n m)
  have b := run_halt_mono h₂ (Nat.le_max_right n m)
  rw [a] at b
  exact Step.halt.inj b

/-- A machine that halts does so in one step from the last state it was in. -/
theorem halt_last {n : Nat} {s : σ} {v : ν} (h : run step n s = .halt v) :
    ∃ m c, run step m s = .next c ∧ step c = .halt v := by
  induction n generalizing s with
  | zero => rw [run_zero] at h; cases h
  | succ n ih =>
    rw [run_succ] at h
    cases hs : step s with
    | next s₁ =>
      rw [hs, Step.bind_next] at h
      obtain ⟨m, c, hm, hc⟩ := ih h
      exact ⟨m + 1, c, by rw [run_succ, hs, Step.bind_next]; exact hm, hc⟩
    | halt w =>
      rw [hs, Step.bind_halt] at h
      cases h
      exact ⟨0, s, rfl, hs⟩
    | stuck => rw [hs] at h; simp at h

/-- A run of `k` steps from `s` to `s'` along which every state, both ends
included, satisfies `I`. -/
def RunsThrough (step : σ → Step σ ν) (I : σ → Prop) (k : Nat) (s s' : σ) : Prop :=
  run step k s = .next s' ∧ ∀ j, j ≤ k → ∃ sj, run step j s = .next sj ∧ I sj

namespace RunsThrough

variable {I : σ → Prop} {s s₁ s₂ s' : σ}

theorem refl (h : I s) : RunsThrough step I 0 s s := by
  refine ⟨rfl, fun j hj => ?_⟩
  have e : j = 0 := by omega
  subst e
  exact ⟨s, rfl, h⟩

theorem cons {k : Nat} (hs : step s = .next s₁) (h : I s) (hr : RunsThrough step I k s₁ s') :
    RunsThrough step I (k + 1) s s' := by
  refine ⟨by rw [run_succ, hs, Step.bind_next]; exact hr.1, fun j hj => ?_⟩
  cases j with
  | zero => exact ⟨s, rfl, h⟩
  | succ j =>
    obtain ⟨sj, hsj, hI⟩ := hr.2 j (by omega)
    exact ⟨sj, by rw [run_succ, hs, Step.bind_next]; exact hsj, hI⟩

theorem trans {a b : Nat} (h₁ : RunsThrough step I a s s₁) (h₂ : RunsThrough step I b s₁ s₂) :
    RunsThrough step I (a + b) s s₂ := by
  refine ⟨by rw [run_add, h₁.1, Step.bind_next]; exact h₂.1, fun j hj => ?_⟩
  by_cases hja : j ≤ a
  · exact h₁.2 j hja
  · obtain ⟨sj, hsj, hI⟩ := h₂.2 (j - a) (by omega)
    have e : j = a + (j - a) := by omega
    exact ⟨sj, by rw [e, run_add, h₁.1, Step.bind_next]; exact hsj, hI⟩

theorem imp {J : σ → Prop} {k : Nat} (h : RunsThrough step I k s s') (hIJ : ∀ x, I x → J x) :
    RunsThrough step J k s s' :=
  ⟨h.1, fun j hj => by
    obtain ⟨sj, hsj, hI⟩ := h.2 j hj
    exact ⟨sj, hsj, hIJ sj hI⟩⟩

end RunsThrough

/-! An observation that only grows along each step only grows along a run. -/

theorem run_obs_prefix {α : Type} (obs : σ → List α)
    (hstep : ∀ {s s' : σ}, step s = .next s' → obs s <+: obs s') :
    ∀ (n : Nat) {s s' : σ}, run step n s = .next s' → obs s <+: obs s' := by
  intro n
  induction n with
  | zero =>
    intro s s' h
    rw [run_zero] at h
    cases h
    exact List.prefix_refl _
  | succ n ih =>
    intro s s' h
    rw [run_succ] at h
    cases hs : step s with
    | next s₁ =>
      rw [hs, Step.bind_next] at h
      exact (hstep hs).trans (ih h)
    | halt v => rw [hs] at h; simp at h
    | stuck => rw [hs] at h; simp at h

theorem run_obs_prefix_halt {α : Type} (obs : σ → List α) (final : ν → List α)
    (hstep : ∀ {s s' : σ}, step s = .next s' → obs s <+: obs s')
    (hhalt : ∀ {s : σ} {v : ν}, step s = .halt v → obs s <+: final v) :
    ∀ (n : Nat) {s : σ} {v : ν}, run step n s = .halt v → obs s <+: final v := by
  intro n
  induction n with
  | zero =>
    intro s v h
    rw [run_zero] at h
    cases h
  | succ n ih =>
    intro s v h
    rw [run_succ] at h
    cases hs : step s with
    | next s₁ =>
      rw [hs, Step.bind_next] at h
      exact (hstep hs).trans (ih h)
    | halt w =>
      rw [hs, Step.bind_halt] at h
      cases h
      exact hhalt hs
    | stuck => rw [hs] at h; simp at h

/-- `run` written as a loop, for executing machines. -/
def exec (step : σ → Step σ ν) : Nat → σ → Step σ ν
  | 0, s => .next s
  | n + 1, s =>
    match step s with
    | .next s' => exec step n s'
    | .halt v => .halt v
    | .stuck => .stuck

end Machine

end Glorious
