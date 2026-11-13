import Glorious.Typing.Covers
import Glorious.Typing.Compiled
import Glorious.Typing.Loans

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
  e.sig.wf && checkClauses C e.sig F.clauses e.hints
    && covers C (coverFuel C (F.clauses.map (·.pats)) e.sig.params) (F.clauses.map (·.pats))
        (e.sig.params.map (Ty.open e.sig.vars))

/-- A declared type the certificate calls duplicable has only duplicable fields. -/
def dataOk (C : Cert) : Bool :=
  C.datas.all fun d => !d.dup || d.ctors.all fun c => dupTys C c.2

/-- Check a program against a certificate. -/
def checkProgram (C : Cert) (p : Program) : Bool :=
  C.sigs.all (fun e =>
      match p.fns[e.fn]? with
      | some F => checkFn C e F
      | none => false)
    && checkTm C [] [] p.main C.mainHints C.mainTy []
    && (!C.strict || dataOk C)

/-- A program the checker accepts is well typed. -/
theorem checkProgram_sound {p : Program} (h : checkProgram C p = true) : ProgramOk C.ctx p := by
  simp only [checkProgram, Bool.and_eq_true] at h
  obtain ⟨⟨hfns, hmain⟩, _⟩ := h
  refine ⟨C.ctx_stable, fun fn sig hsig => ?_, ⟨C.mainTy, checkTm_sound _ hmain⟩⟩
  obtain ⟨e, he, rfl, rfl⟩ := hsig
  have hfn := List.all_eq_true.mp hfns e he
  split at hfn
  · rename_i F hF
    simp only [checkFn, Bool.and_eq_true] at hfn
    obtain ⟨⟨hwf, hclauses⟩, hcovers⟩ := hfn
    have htyped := checkClauses_sound hclauses
    refine ⟨hwf, F, hF, htyped, fun S vs θ hv => ?_⟩
    refine select_of_match (fun c hc => ?_) (covers_sound _ hcovers θ hv)
    obtain ⟨⟨Bs, hpats, _⟩, _⟩ := htyped c hc
    rw [hpats.length_eq, hv.length_eq]
    simp
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
    (hdup : dupTy C (.data name args) = true)
    (hF : C.fields tag name args = some Fs) :
    ∀ c, c ∈ Fs → dupTy C c = true := by
  simp only [dupTy] at hdup
  simp only [Cert.fields] at hF
  split at hF
  · -- An array of what is duplicable.
    rename_i hname
    simp only [hname, ↓reduceIte] at hdup
    unfold arrayFields at hF
    split at hF
    · split at hF
      · cases hF
        intro c hc
        rw [List.eq_of_mem_replicate hc]
        simpa [dupTys] using hdup
      · cases hF
    · cases hF
  rename_i hname
  simp only [hname, ↓reduceIte] at hdup
  simp only [dataDup, findData] at hdup hF
  cases hf : C.datas.find? (fun d => d.name == name && d.args == args.map Ty.shape) with
  | none => simp [hf] at hdup
  | some d =>
    simp only [hf] at hdup hF
    have hmem : d ∈ C.datas := List.mem_of_find?_eq_some hf
    have hall := List.all_eq_true.mp hd d hmem
    simp only [hdup, Bool.not_true, Bool.false_or] at hall
    have hF' : (instCtors (freesOf args) d.ctors).lookup tag = some Fs := by simpa using hF
    rw [instCtors_lookup] at hF'
    cases hl : d.ctors.lookup tag with
    | none => simp [hl] at hF'
    | some Fs₀ =>
      simp only [hl, Option.map_some, Option.some.injEq] at hF'
      subst hF'
      have hin : (tag, Fs₀) ∈ d.ctors := lookup_mem hl
      have h0 : dupTys C Fs₀ = true := List.all_eq_true.mp hall _ hin
      exact dupTys_all (by rw [dupTys_inst]; exact h0)

mutual

theorem dup_occ (hs : C.strict = true) (hd : dataOk C = true) :
    ∀ {S : StoreTy} {v : Value} {τ : Ty}, HasVal C.ctx S v τ → dupTy C τ = true →
      ∀ id, occ id v = 0
  | _, _, _, .int, _, id => by simp [occ]
  | _, _, _, .data hc hf, hdup, id => by
    simp only [occ]
    rcases hc with ⟨_, rfl⟩ | ⟨_, name, args, rfl, hF⟩
    · exact dups_occ hs hd hf (dupTys_all (by simpa [dupTy] using hdup)) id
    · exact dups_occ hs hd hf (data_fields_dup hd hdup hF) id
  | _, _, _, .clo _ _ hc hq _ hτ, hdup, id => by
    subst hτ
    simp only [occ]
    simp only [FnSig.ty, dupTy, Bool.not_eq_true'] at hdup
    refine dups_occ hs hd hc (fun c hcm => ?_) id
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hcm
    rw [dupTy_inst]
    rcases hq hdup c₀ hc₀ with h | h
    · rw [hs] at h
      cases h
    · exact h
  | _, _, _, .cont _, hdup, _ => by simp [dupTy] at hdup
  | _, _, _, .label _ _, _, id => by simp [occ]
  | _, _, _, .ref _ _ _, _, id => by simp [occ]

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

/--
**Borrow safety, checked.** If the certificate asks for the region rules and
the checker accepts, the program never reaches a state about to read or write a
released cell,
-/
theorem checked_borrow_safety {p : Program} (h : checkProgram C p = true)
    (hr : C.regions = true) (input : List Int) {c : Config}
    (hc : Machine.Reaches (stepIO p) (initIO p input) c) : ¬ Freed c.state :=
  borrow_safety (checkProgram_sound h) hr input hc

/-- nor one about to apply a label whose scope has ended. -/
theorem checked_label_safety {p : Program} (h : checkProgram C p = true)
    (hr : C.regions = true) (input : List Int) {c : Config}
    (hc : Machine.Reaches (stepIO p) (initIO p input) c) : ¬ Dead c.state :=
  label_safety (checkProgram_sound h) hr input hc

/-- So if such a program goes wrong, the fault is neither of those. -/
theorem checked_scoped_safety {p : Program} (h : checkProgram C p = true)
    (hr : C.regions = true) (input : List Int) (hw : GoesWrong p input) :
    ∃ c, Machine.Reaches (stepIO p) (initIO p input) c ∧ stepIO p c = .stuck ∧ Fault c.state
      ∧ ¬ Freed c.state ∧ ¬ Dead c.state :=
  scoped_safety (checkProgram_sound h) hr input hw

/-- The same for the compiled bytecode. -/
theorem checked_compiled_scoped_safety {p : Program} (h : checkProgram C p = true)
    (hr : C.regions = true) (input : List Int) (hw : Bytecode.GoesWrong (compile p) input) :
    ∃ c, Machine.Reaches (stepIO p) (initIO p input) c ∧ stepIO p c = .stuck ∧ Fault c.state
      ∧ ¬ Freed c.state ∧ ¬ Dead c.state :=
  compiled_scoped_safety (checkProgram_sound h) hr input hw

/--
**Exclusive borrows, checked.** If the certificate asks for the region rules
and the rules for borrows and the checker accepts, the program never reaches a
state about to use a reference it may not: it reads, writes and lends a cell
only through a reference that no newer borrow in scope excludes, and through no
borrow whose scope has ended. And no borrow's scope is ever set aside in a
resumption. Nothing is assumed about the certificate or the program.
-/
theorem checked_exclusive_safety {p : Program} (h : checkProgram C p = true)
    (hr : C.regions = true) (hl : C.loans = true) (input : List Int) {c : Config}
    (hc : Machine.Reaches (stepIO p) (initIO p input) c) :
    ¬ Aliased c.state ∧ ¬ Suspended c.state :=
  exclusive_safety (checkProgram_sound h) hr hl input hc

/--
**Soundness, checked.** If the certificate asks for the ownership rules and
the region rules and the checker accepts, the program goes wrong in one way
only: an arithmetic result does not fit in 64 bits. Nothing is assumed about
the certificate or the program.
-/
theorem checked_full_safety {p : Program} (h : checkProgram C p = true) (hs : C.strict = true)
    (hr : C.regions = true) (input : List Int) (hw : GoesWrong p input) :
    ∃ c, Machine.Reaches (stepIO p) (initIO p input) c ∧ stepIO p c = .stuck
      ∧ Overflow c.state :=
  sound_safety (checkProgram_sound h) (dupSound_of_check h hs) hr input hw

/-- The same for the compiled bytecode. -/
theorem checked_compiled_full_safety {p : Program} (h : checkProgram C p = true)
    (hs : C.strict = true) (hr : C.regions = true) (input : List Int)
    (hw : Bytecode.GoesWrong (compile p) input) :
    ∃ c, Machine.Reaches (stepIO p) (initIO p input) c ∧ stepIO p c = .stuck
      ∧ Overflow c.state :=
  compiled_sound_safety (checkProgram_sound h) (dupSound_of_check h hs) hr input hw

end Glorious.Typing
