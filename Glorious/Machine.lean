/-!
# Deterministic machines

Both the Core semantics and the bytecode semantics are given as a total step
function. This file defines what it means to run such a machine and the three
observable behaviours of a program: it halts with a value, it goes wrong, or it
runs forever.
-/

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

theorem run_one_next {s s' : σ} (h : step s = .next s') : run step (0 + 1) s = .next s' := by
  simp [run_succ, h]

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

/-- `run` written as a loop, for executing machines. -/
def exec (step : σ → Step σ ν) : Nat → σ → Step σ ν
  | 0, s => .next s
  | n + 1, s =>
    match step s with
    | .next s' => exec step n s'
    | .halt v => .halt v
    | .stuck => .stuck

theorem exec_eq_run (n : Nat) (s : σ) : exec step n s = run step n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [run_succ]
    simp only [exec]
    cases step s with
    | next s' => simpa using ih s'
    | halt v => rfl
    | stuck => rfl

end Machine

end Glorious
