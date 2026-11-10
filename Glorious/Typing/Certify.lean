import Glorious.Typing.Covers
import Glorious.Typing.Compiled

/-!
# Checking a whole program

`checkProgram` runs the type checker and the coverage check on every function
at every signature the certificate gives it. What it accepts is well typed, so
the safety theorem applies with no assumption left: `checked_safety`.
-/

namespace Glorious.Typing

open Core

variable {C : Cert}

mutual

/-- The number of patterns in a pattern, itself included. -/
def patSize : Pat → Nat
  | .wild => 1
  | .bind => 1
  | .int _ => 1
  | .ctor _ ps => 1 + patsSize ps

def patsSize : List Pat → Nat
  | [] => 0
  | p :: ps => patSize p + patsSize ps

end

/-- The most fields any declared constructor has. -/
def widest (C : Cert) : Nat :=
  C.datas.foldl (fun n d => d.ctors.foldl (fun m c => max m c.2.length) n) 0

/-- Enough depth for the coverage search on these rows. Soundness does not
depend on this number; too small a number only makes the check say no. -/
def coverFuel (C : Cert) (rows : List (List Pat)) (tys : List Ty) : Nat :=
  let size := (rows.map patsSize).foldl (· + ·) 0
  tys.length + (size + 1) * (widest C + size + 1) + 2

/-- Check a function at one of its signatures: each clause is typed, and
together the clauses cover the signature's parameters. -/
def checkFn (C : Cert) (e : SigEntry) (F : Fn) : Bool :=
  checkClauses C e.sig F.clauses e.hints
    && covers C (coverFuel C (F.clauses.map (·.pats)) e.sig.params) (F.clauses.map (·.pats))
        e.sig.params

/-- Check a program against a certificate. -/
def checkProgram (C : Cert) (p : Program) : Bool :=
  C.sigs.all (fun e =>
      match p.fns[e.fn]? with
      | some F => checkFn C e F
      | none => false)
    && checkTm C [] p.main C.mainHints C.mainTy []

/-- A program the checker accepts is well typed. -/
theorem checkProgram_sound {p : Program} (h : checkProgram C p = true) : ProgramOk C.ctx p := by
  simp only [checkProgram, Bool.and_eq_true] at h
  obtain ⟨hfns, hmain⟩ := h
  refine ⟨fun fn sig hsig => ?_, ⟨C.mainTy, checkTm_sound _ hmain⟩⟩
  obtain ⟨e, he, rfl, rfl⟩ := hsig
  have hfn := List.all_eq_true.mp hfns e he
  split at hfn
  · rename_i F hF
    simp only [checkFn, Bool.and_eq_true] at hfn
    obtain ⟨hclauses, hcovers⟩ := hfn
    have htyped := checkClauses_sound hclauses
    refine ⟨F, hF, htyped, fun S vs hv => ?_⟩
    refine select_of_match (fun c hc => ?_) (covers_sound _ hcovers hv)
    obtain ⟨Bs, hpats, _⟩ := htyped c hc
    rw [hpats.length_eq, hv.length_eq]
  · simp at hfn

/--
**Type safety, checked.** If the checker accepts a program with some
certificate and the program goes wrong, the state it could not step from is one
of the four faults. Nothing is assumed about the certificate or the program.
-/
theorem checked_safety {p : Program} (h : checkProgram C p = true) (input : List Int)
    (hw : GoesWrong p input) :
    ∃ c, Machine.Reaches (stepIO p) (initIO p input) c ∧ stepIO p c = .stuck ∧ Fault c.state :=
  type_safety (checkProgram_sound h) input hw

/-- The same for the compiled bytecode. -/
theorem checked_compiled_safety {p : Program} (h : checkProgram C p = true) (input : List Int)
    (hw : Bytecode.GoesWrong (compile p) input) :
    ∃ c, Machine.Reaches (stepIO p) (initIO p input) c ∧ stepIO p c = .stuck ∧ Fault c.state :=
  compiled_type_safety (checkProgram_sound h) input hw

end Glorious.Typing
