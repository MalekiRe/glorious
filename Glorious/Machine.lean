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

variable {step : σ → Step σ ν}

namespace RunsThrough

variable {I : σ → Prop} {s s₁ s₂ s' : σ}

end RunsThrough

/-! An observation that only grows along each step only grows along a run. -/

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
