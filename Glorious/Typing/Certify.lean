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

/-- A declared type the certificate calls duplicable has only duplicable fields. -/
def dataOk (C : Cert) : Bool :=
  C.datas.all fun d => !d.dup || d.ctors.all fun c => dupTys C c.2

/-- Check a program against a certificate. -/
def checkProgram (C : Cert) (p : Program) : Bool :=
  C.sigs.all (fun e =>
      match p.fns[e.fn]? with
      | some F => checkFn C e F
      | none => false)
    && checkTm C [] p.main C.mainHints C.mainTy []
    && (!C.strict || dataOk C)

/-- A program the checker accepts is well typed. -/
theorem checkProgram_sound {p : Program} (h : checkProgram C p = true) : ProgramOk C.ctx p := by
  simp only [checkProgram, Bool.and_eq_true] at h
  obtain ⟨⟨hfns, hmain⟩, _⟩ := h
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
    obtain ⟨⟨Bs, hpats, _⟩, _⟩ := htyped c hc
    rw [hpats.length_eq, hv.length_eq]
  · simp at hfn

/-! ## Ownership -/

theorem dupTys_all {τs : List Ty} : dupTys C τs = true → ∀ c, c ∈ τs → dupTy C c = true := by
  induction τs with
  | nil => intro _ c hc; cases hc
  | cons t ts ih =>
    intro h c hc
    simp only [dupTys, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1
    · exact ih h.2 c hc

/-- A declared type that is duplicable and has this constructor has duplicable fields. -/
theorem data_fields_dup (hd : dataOk C = true) {name tag : Nat} {args Fs : List Ty}
    (hdup : dataDup C.datas name args = true)
    (hF : (findData C.datas name args).bind (·.lookup tag) = some Fs) :
    ∀ c, c ∈ Fs → dupTy C c = true := by
  simp only [dataDup, findData] at hdup hF
  cases hf : C.datas.find? (fun d => d.name == name && d.args == args) with
  | none => simp [hf] at hdup
  | some d =>
    simp only [hf] at hdup hF
    have hmem : d ∈ C.datas := List.mem_of_find?_eq_some hf
    have hall := List.all_eq_true.mp hd d hmem
    simp only [hdup, Bool.not_true, Bool.false_or] at hall
    have hin : (tag, Fs) ∈ d.ctors := lookup_mem (by simpa using hF)
    exact dupTys_all (List.all_eq_true.mp hall _ hin)

mutual

theorem dup_occ (hs : C.strict = true) (hd : dataOk C = true) :
    ∀ {S : StoreTy} {v : Value} {τ : Ty}, HasVal C.ctx S v τ → dupTy C τ = true →
      ∀ id, occ id v = 0
  | _, _, _, .int, _, id => by simp [occ]
  | _, _, _, .data hc hf, hdup, id => by
    simp only [occ]
    rcases hc with ⟨_, rfl⟩ | ⟨_, name, args, rfl, hF⟩
    · exact dups_occ hs hd hf (dupTys_all (by simpa [dupTy] using hdup)) id
    · exact dups_occ hs hd hf (data_fields_dup hd (by simpa [dupTy] using hdup) hF) id
  | _, _, _, .clo _ hc hq, hdup, id => by
    simp only [occ]
    simp only [dupTy, Bool.not_eq_true'] at hdup
    refine dups_occ hs hd hc (fun c hcm => ?_) id
    rcases hq hdup c hcm with h | h
    · rw [hs] at h
      cases h
    · exact h
  | _, _, _, .cont _, hdup, _ => by simp [dupTy] at hdup
  | _, _, _, .label _, _, id => by simp [occ]
  | _, _, _, .ref _, _, id => by simp [occ]

theorem dups_occ (hs : C.strict = true) (hd : dataOk C = true) :
    ∀ {S : StoreTy} {vs : List Value} {τs : List Ty}, HasVals C.ctx S vs τs →
      (∀ c, c ∈ τs → dupTy C c = true) → ∀ id, occs id vs = 0
  | _, _, _, .nil, _, id => by simp [occs]
  | _, _, _, .cons hv hvs, h, id => by
    simp [occs, dup_occ hs hd hv (h _ (List.mem_cons_self ..)) id,
      dups_occ hs hd hvs (fun c hc => h c (List.mem_cons_of_mem _ hc)) id]

end

/-- Under a certificate checked with the ownership rules, a value of a
duplicable type holds no resumption. -/
theorem dupSound_of_check {p : Program} (h : checkProgram C p = true) (hs : C.strict = true) :
    DupSound C.ctx := by
  simp only [checkProgram, Bool.and_eq_true, hs, Bool.not_true, Bool.false_or] at h
  intro S v τ hv hdup id
  rcases hdup with hf | hd
  · rw [hs] at hf
    cases hf
  · exact dup_occ hs h.2 hv hd id

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

/--
**Ownership, checked.** If the certificate asks for the ownership rules and the
checker accepts, the fault is not a second use of a resumption: three faults
remain.
-/
theorem checked_owned_safety {p : Program} (h : checkProgram C p = true)
    (hs : C.strict = true) (input : List Int) (hw : GoesWrong p input) :
    ∃ c, Machine.Reaches (stepIO p) (initIO p input) c ∧ stepIO p c = .stuck ∧ Fault c.state
      ∧ ¬ Resumed c.state :=
  owned_safety (checkProgram_sound h) (dupSound_of_check h hs) input hw

/-- The same for the compiled bytecode. -/
theorem checked_compiled_owned_safety {p : Program} (h : checkProgram C p = true)
    (hs : C.strict = true) (input : List Int) (hw : Bytecode.GoesWrong (compile p) input) :
    ∃ c, Machine.Reaches (stepIO p) (initIO p input) c ∧ stepIO p c = .stuck ∧ Fault c.state
      ∧ ¬ Resumed c.state :=
  compiled_owned_safety (checkProgram_sound h) (dupSound_of_check h hs) input hw

end Glorious.Typing
