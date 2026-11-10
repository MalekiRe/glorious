import Glorious.Compile
import Glorious.Core.Semantics
import Glorious.Bytecode.Semantics
import Glorious.Proof.Simulation

/-!
# Compiler correctness

The bytecode produced by `compile` has exactly the behaviour of the Core program
it was compiled from. The final statement is `compile_correct`.
-/

namespace Glorious

open Machine
open Bytecode (Instr Code)

/-! ## Code positions -/

theorem drop_eq_cons {α : Type} {l : List α} {n : Nat} {a : α} {t : List α}
    (h : l.drop n = a :: t) : l[n]? = some a ∧ l.drop (n + 1) = t := by
  induction l generalizing n with
  | nil => simp at h
  | cons x xs ih =>
    cases n with
    | zero =>
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      simp
    | succ n =>
      simp at h
      simpa using ih h

/-- The instructions `is` sit in `code` starting at position `pc`. -/
def CodeAt (code : Code) (pc : Nat) (is : Code) : Prop :=
  ∃ post, code.drop pc = is ++ post

theorem CodeAt.zero (code : Code) : CodeAt code 0 code := ⟨[], by simp⟩

theorem CodeAt.head {code : Code} {pc : Nat} {i : Instr} {is : Code}
    (h : CodeAt code pc (i :: is)) : code[pc]? = some i := by
  obtain ⟨post, h⟩ := h
  have h' : code.drop pc = i :: (is ++ post) := h
  exact (drop_eq_cons h').1

theorem CodeAt.tail {code : Code} {pc : Nat} {i : Instr} {is : Code}
    (h : CodeAt code pc (i :: is)) : CodeAt code (pc + 1) is := by
  obtain ⟨post, h⟩ := h
  have h' : code.drop pc = i :: (is ++ post) := h
  exact ⟨post, (drop_eq_cons h').2⟩

/-! ## The simulation relation -/

/-- Every suspended Core caller has a return frame that resumes its compiled code
with the same locals. -/
inductive MatchFrames : List Core.Frame → List Bytecode.Frame → Prop where
  | nil : MatchFrames [] []
  | cons {body : Core.Tm} {ρ : Env} {stack : List Core.Frame}
      {code : Code} {pc : Nat} {frames : List Bytecode.Frame} :
      CodeAt code pc (compileTm body) → MatchFrames stack frames →
      MatchFrames (⟨ρ, body⟩ :: stack) (⟨code, pc, ρ⟩ :: frames)

/-- The program counter points at the compiled form of the current Core
computation, the locals are the Core environment, and the stacks correspond. -/
inductive Match : Core.State → Bytecode.State → Prop where
  | mk {tm : Core.Tm} {ρ : Env} {stack : List Core.Frame}
      {code : Code} {pc : Nat} {frames : List Bytecode.Frame} :
      CodeAt code pc (compileTm tm) → MatchFrames stack frames →
      Match ⟨tm, ρ, stack⟩ ⟨code, pc, ρ, frames⟩

theorem match_init (p : Core.Program) : Match (Core.init p) (Bytecode.init (compile p)) :=
  .mk (CodeAt.zero _) .nil

/-! ## Calls resolve the same way -/

theorem enter_compile {p : Core.Program} {ρ : Env} {f : Atom} {args : List Atom}
    {callee : Core.Tm} {ρ' : Env} (h : Core.enter p ρ f args = some (callee, ρ')) :
    Bytecode.enter (compile p) ρ f args = some (compileTm callee, ρ') := by
  simp only [Core.enter] at h
  simp only [Bytecode.enter]
  cases hc : evalCall ρ f args with
  | none => simp [hc] at h
  | some r =>
    obtain ⟨fn, captures, vs⟩ := r
    cases hF : p.fns[fn]? with
    | none => simp [hc, hF] at h
    | some F =>
      by_cases hlen : vs.length = F.arity
      · simp [hc, hF, hlen] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [compile, compileFn, hF, hlen]
      · simp [hc, hF, hlen] at h

/-! ## One Core step is one bytecode step -/

theorem step_sim (p : Core.Program) {s : Core.State} {t : Bytecode.State} (hm : Match s t) :
    match Core.step p s with
    | .next s' => ∃ t', Bytecode.step (compile p) t = .next t' ∧ Match s' t'
    | .halt v => Bytecode.step (compile p) t = .halt v
    | .stuck => True := by
  obtain @⟨tm, ρ, stack, code, pc, frames, hcode, hfr⟩ := hm
  cases tm with
  | ret a =>
    have hc : CodeAt code pc [Instr.ret a] := hcode
    have hi := hc.head
    cases ha : a.eval ρ with
    | none => simp [Core.step, ha]
    | some v =>
      cases hfr with
      | nil => simp [Core.step, Bytecode.step, hi, ha]
      | @cons body ρ' stack' fcode fpc frames' hfc hrest =>
        have hcore : Core.step p ⟨.ret a, ρ, ⟨ρ', body⟩ :: stack'⟩
            = .next ⟨body, ρ' ++ [v], stack'⟩ := by
          simp [Core.step, ha]
        rw [hcore]
        exact ⟨⟨fcode, fpc, ρ' ++ [v], frames'⟩, by simp [Bytecode.step, hi, ha], .mk hfc hrest⟩
  | let_ rhs body =>
    have hc : CodeAt code pc (Instr.op rhs :: compileTm body) := hcode
    have hi := hc.head
    cases hr : rhs.eval ρ with
    | none => simp [Core.step, hr]
    | some v =>
      have hcore : Core.step p ⟨.let_ rhs body, ρ, stack⟩ = .next ⟨body, ρ ++ [v], stack⟩ := by
        simp [Core.step, hr]
      rw [hcore]
      exact ⟨⟨code, pc + 1, ρ ++ [v], frames⟩, by simp [Bytecode.step, hi, hr], .mk hc.tail hfr⟩
  | call f args body =>
    have hc : CodeAt code pc (Instr.call f args :: compileTm body) := hcode
    have hi := hc.head
    cases he : Core.enter p ρ f args with
    | none => simp [Core.step, he]
    | some r =>
      obtain ⟨callee, ρ'⟩ := r
      have he' := enter_compile he
      have hcore : Core.step p ⟨.call f args body, ρ, stack⟩
          = .next ⟨callee, ρ', ⟨ρ, body⟩ :: stack⟩ := by
        simp [Core.step, he]
      rw [hcore]
      exact ⟨⟨compileTm callee, 0, ρ', ⟨code, pc + 1, ρ⟩ :: frames⟩,
        by simp [Bytecode.step, hi, he'], .mk (CodeAt.zero _) (.cons hc.tail hfr)⟩
  | tail f args =>
    have hc : CodeAt code pc [Instr.tail f args] := hcode
    have hi := hc.head
    cases he : Core.enter p ρ f args with
    | none => simp [Core.step, he]
    | some r =>
      obtain ⟨callee, ρ'⟩ := r
      have he' := enter_compile he
      have hcore : Core.step p ⟨.tail f args, ρ, stack⟩ = .next ⟨callee, ρ', stack⟩ := by
        simp [Core.step, he]
      rw [hcore]
      exact ⟨⟨compileTm callee, 0, ρ', frames⟩,
        by simp [Bytecode.step, hi, he'], .mk (CodeAt.zero _) hfr⟩

/-- `Match` is a forward simulation from Core to bytecode. -/
theorem forwardSim (p : Core.Program) :
    ForwardSim (Core.step p) (Bytecode.step (compile p)) Match where
  next := by
    intro s t s' hm hs
    have h := step_sim p hm
    rw [hs] at h
    obtain ⟨t', ht', hm'⟩ := h
    exact ⟨0, t', run_one_next ht', hm'⟩
  halt := by
    intro s t v hm hs
    have h := step_sim p hm
    rw [hs] at h
    exact ⟨0, run_one_halt h⟩

/-! ## Behaviour preservation -/

/-- If the Core program halts with `v`, so does its bytecode. -/
theorem compile_halts {p : Core.Program} {v : Value} :
    Core.Halts p v → Bytecode.Halts (compile p) v :=
  (forwardSim p).halts (match_init p)

/-- If the Core program runs forever, so does its bytecode. -/
theorem compile_diverges {p : Core.Program} :
    Core.Diverges p → Bytecode.Diverges (compile p) :=
  (forwardSim p).diverges (match_init p)

/-- A result computed by the bytecode is a result of the Core program, unless
the Core program goes wrong. -/
theorem compile_halts_reflect {p : Core.Program} {v : Value} :
    Bytecode.Halts (compile p) v → Core.Halts p v ∨ Core.GoesWrong p :=
  (forwardSim p).halts_reflect (match_init p)

/--
**Compiler correctness.** For a Core program that does not go wrong, the
compiled bytecode has exactly the same behaviour: it halts with the same values,
it diverges exactly when the Core program does, and it never goes wrong.
-/
theorem compile_correct (p : Core.Program) (safe : ¬ Core.GoesWrong p) :
    (∀ v, Bytecode.Halts (compile p) v ↔ Core.Halts p v)
    ∧ (Bytecode.Diverges (compile p) ↔ Core.Diverges p)
    ∧ ¬ Bytecode.GoesWrong (compile p) := by
  refine ⟨fun v => ⟨fun h => ?_, compile_halts⟩, ⟨?_, compile_diverges⟩, ?_⟩
  · exact (compile_halts_reflect h).resolve_right safe
  · exact (forwardSim p).diverges_reflect (match_init p) safe
  · exact (forwardSim p).not_goesWrong (match_init p) safe

end Glorious
