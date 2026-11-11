import Glorious.Typing.Equality
import Glorious.Typing.Stack

/-!
# A type checker for Core

A function that checks a Core program against a certificate: the signatures of
its functions, the data types it uses, and a few types the program text does
not determine. `checkTm_sound` and its companions say that what the checker
accepts has a typing derivation. The certificate is not trusted: a wrong one is
rejected, or describes another valid typing.
-/

namespace Glorious.Typing

open Core

/-- One use of a declared data type: its type arguments, and each constructor's
field types at those arguments. -/
structure DataInst where
  name : Nat
  args : List Ty
  ctors : List (Nat × List Ty)
  /-- Whether values of this type may be used any number of times. The checker
  accepts this only if every field of every constructor may. -/
  dup : Bool

/-- An operation of an effect used at some type arguments: what it takes, and
what it is resumed with if it can be resumed. -/
structure OpInst where
  op : Nat
  args : List Ty
  payload : List Ty
  result : Option Ty

/-- A type the checker is told rather than left to find. -/
inductive Hint where
  /-- The type of the value a `let` binds. -/
  | ty (σ : Ty)
  /-- What a handler yields, and the operations it serves, in the handler's
  order, each with the type arguments of its effect. -/
  | handler (ρ : Ty) (H : Row)

/-- A signature of a function, with the hints for each of its clauses at that signature. -/
structure SigEntry where
  fn : Nat
  sig : FnSig
  hints : List (List Hint)

/-- Everything the checker needs beyond the program. -/
structure Cert where
  sigs : List SigEntry
  datas : List DataInst
  ops : List OpInst
  mainTy : Ty
  mainHints : List Hint
  /-- Whether the ownership rules are to be checked. If not, every type counts
  as duplicable, and the program is only shown to be well typed. -/
  strict : Bool

def findData (ds : List DataInst) (name : Nat) (args : List Ty) :
    Option (List (Nat × List Ty)) :=
  match ds.find? (fun d => d.name == name && d.args == args) with
  | some d => some d.ctors
  | none => none

def findOp (os : List OpInst) (op : Nat) (args : List Ty) : Option OpTy :=
  match os.find? (fun o => o.op == op && o.args == args) with
  | some o => some (o.payload, o.result)
  | none => none

def dataDup (ds : List DataInst) (name : Nat) (args : List Ty) : Bool :=
  match ds.find? (fun d => d.name == name && d.args == args) with
  | some d => d.dup
  | none => false

mutual

/-- May a value of this type be used any number of times? A callable may if it
is not marked as callable once; a declared type, if the certificate says so. -/
def dupTy (C : Cert) : Ty → Bool
  | .int => true
  | .tuple fs => dupTys C fs
  | .data name args => dataDup C.datas name args
  | .fn _ _ _ once => !once
  | .ref _ => true
  | .never => true
termination_by structural t => t

def dupTys (C : Cert) : List Ty → Bool
  | [] => true
  | t :: ts => dupTy C t && dupTys C ts
termination_by structural ts => ts

end

/-- The typing context a certificate describes. -/
def Cert.ctx (C : Cert) : Ctx where
  fnSig fn sig := ∃ e, e ∈ C.sigs ∧ e.fn = fn ∧ e.sig = sig
  opSig op args := findOp C.ops op args
  dup τ := C.strict = false ∨ dupTy C τ = true
  ctorFields tag name args := (findData C.datas name args).bind (·.lookup tag)

variable {C : Cert}

/-! ## Ownership -/

def dupOk (C : Cert) (τ : Ty) : Bool := !C.strict || dupTy C τ

theorem dupOk_sound {τ : Ty} (h : dupOk C τ = true) : C.ctx.dup τ := by
  simp only [dupOk, Bool.or_eq_true, Bool.not_eq_true'] at h
  exact h

theorem dupOk_all {τs : List Ty} (h : τs.all (dupOk C) = true) : ∀ c, c ∈ τs → C.ctx.dup c :=
  fun c hc => dupOk_sound (List.all_eq_true.mp h c hc)

/-- Is every moved local whose type is not duplicable moved once and not mentioned afterwards? -/
def linearB (C : Cert) (Γ : TEnv) (moved rest : List Nat) : Bool :=
  !C.strict || moved.all fun i =>
    match Γ[i]? with
    | some τ => dupTy C τ || (decide (cnt i moved ≤ 1) && !rest.contains i)
    | none => true

theorem linearB_sound {Γ : TEnv} {moved rest : List Nat} (h : linearB C Γ moved rest = true) :
    Linear C.ctx Γ moved rest := by
  intro i τ hτ hnd
  have hs : C.strict = true := by
    cases hq : C.strict with
    | true => rfl
    | false => exact absurd (Or.inl hq) hnd
  have hd : dupTy C τ = false := by
    cases hq : dupTy C τ with
    | false => rfl
    | true => exact absurd (Or.inr hq) hnd
  by_cases hm : i ∈ moved
  · simp only [linearB, hs, Bool.not_true, Bool.false_or] at h
    have := List.all_eq_true.mp h i hm
    simp only [hτ, hd, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      List.contains_eq_mem, decide_eq_false_iff_not] at this
    exact ⟨this.1, fun _ => this.2⟩
  · exact ⟨by rw [cnt_zero hm]; exact Nat.zero_le _, fun h' => absurd h' hm⟩

/-! ## Rows -/

theorem lookup_mem {β : Type} : ∀ {l : List (Nat × β)} {k : Nat} {v : β},
    l.lookup k = some v → (k, v) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (k', v') :: l, k, v, h => by
    by_cases he : k = k'
    · subst he
      rw [lookup_cons_eq] at h
      cases h
      exact List.mem_cons_self ..
    · rw [lookup_cons_ne he] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

/-- Does `b` offer every operation of `a` at the type `a` gives it? -/
def rowLe (a b : Row) : Bool := a.all fun x => a.lookup x.1 == b.lookup x.1

theorem rowLe_sound {a b : Row} (h : rowLe a b = true) : Row.le a b := by
  intro op sig hl
  have h' := List.all_eq_true.mp h _ (lookup_mem hl)
  simp only [beq_iff_eq] at h'
  rw [← h']
  exact hl

/-! ## Operands -/

def atomTy (Γ : TEnv) : Atom → Option Ty
  | .var i => Γ[i]?
  | .int _ => some .int

theorem atomTy_sound {Γ : TEnv} {a : Atom} {τ : Ty} (h : atomTy Γ a = some τ) : HasAtom Γ a τ := by
  cases a with
  | var i => exact .var h
  | int n =>
    simp only [atomTy, Option.some.injEq] at h
    subst h
    exact .int

def atomsTy (Γ : TEnv) : List Atom → Option (List Ty)
  | [] => some []
  | a :: as =>
    match atomTy Γ a, atomsTy Γ as with
    | some t, some ts => some (t :: ts)
    | _, _ => none

theorem atomsTy_sound {Γ : TEnv} : ∀ {as : List Atom} {τs : List Ty},
    atomsTy Γ as = some τs → HasAtoms Γ as τs
  | [], _, h => by
    simp only [atomsTy, Option.some.injEq] at h
    subst h
    exact .nil
  | a :: as, τs, h => by
    simp only [atomsTy] at h
    split at h
    · rename_i t ts ht hts
      cases h
      exact .cons (atomTy_sound ht) (atomsTy_sound hts)
    · cases h

/-! ## Data -/

/-- The field types of constructor `tag` at a type, if it is a constructor of that type. -/
def ctorFieldsOf (C : Cert) (tag : Nat) : Ty → Option (List Ty)
  | .tuple Fs => if tag = 0 then some Fs else none
  | .data name args =>
    if tag = 0 then none else (findData C.datas name args).bind (·.lookup tag)
  | .int => none
  | .fn _ _ _ _ => none
  | .ref _ => none
  | .never => none

theorem ctorFieldsOf_sound {tag : Nat} {T : Ty} {Fs : List Ty}
    (h : ctorFieldsOf C tag T = some Fs) : CtorOf C.ctx tag T Fs := by
  cases T with
  | tuple Fs' =>
    simp only [ctorFieldsOf] at h
    split at h
    · rename_i h0
      cases h
      exact .inl ⟨h0, rfl⟩
    · cases h
  | data name args =>
    simp only [ctorFieldsOf] at h
    split at h
    · cases h
    · rename_i h0
      exact .inr ⟨h0, name, args, rfl, h⟩
  | int => simp [ctorFieldsOf] at h
  | fn _ _ _ _ => simp [ctorFieldsOf] at h
  | ref _ => simp [ctorFieldsOf] at h
  | never => simp [ctorFieldsOf] at h

theorem ctorFieldsOf_complete {tag : Nat} {T : Ty} {Fs : List Ty}
    (h : CtorOf C.ctx tag T Fs) : ctorFieldsOf C tag T = some Fs := by
  rcases h with ⟨h0, rfl⟩ | ⟨h0, name, args, rfl, hF⟩
  · simp [ctorFieldsOf, h0]
  · simp only [ctorFieldsOf, h0, ↓reduceIte]
    exact hF

/-- The fields that can be read from a value of a type without testing which
constructor built it. -/
def fieldsOf (C : Cert) : Ty → Option (List Ty)
  | .tuple Fs => some Fs
  | .data name args =>
    match findData C.datas name args with
    | some ((_, Fs) :: rest) => if rest.all (fun c => c.2 == Fs) then some Fs else none
    | _ => none
  | .int => none
  | .fn _ _ _ _ => none
  | .ref _ => none
  | .never => none

def placeTy (C : Cert) : Ty → List Nat → Option Ty
  | τ, [] => some τ
  | τ, i :: path =>
    match fieldsOf C τ with
    | some Fs =>
      match Fs[i]? with
      | some σ => placeTy C σ path
      | none => none
    | none => none

theorem placeTy_sound : ∀ {path : List Nat} {σ τ : Ty},
    placeTy C σ path = some τ → PlaceOk C.ctx σ path τ
  | [], σ, τ, h => by
    simp only [placeTy, Option.some.injEq] at h
    subst h
    exact .here
  | i :: path, σ, τ, h => by
    simp only [placeTy] at h
    split at h
    · rename_i Fs hF
      split at h
      · rename_i σ' hi
        have hrest := placeTy_sound h
        cases σ with
        | tuple Fs' =>
          simp only [fieldsOf, Option.some.injEq] at hF
          subst hF
          exact .tuple hi hrest
        | data name args =>
          simp only [fieldsOf] at hF
          split at hF
          · rename_i t Fs₀ rest hfind
            split at hF
            · rename_i hall
              cases hF
              refine .field (fun tag Fs' hc => ?_) hi hrest
              have hc' := ctorFieldsOf_complete hc
              simp only [ctorFieldsOf] at hc'
              split at hc'
              · cases hc'
              · rw [hfind] at hc'
                have hm := lookup_mem (show ((t, Fs) :: rest).lookup tag = some Fs' from hc')
                rcases List.mem_cons.mp hm with he | hm
                · cases he
                  rfl
                · have := List.all_eq_true.mp hall _ hm
                  simpa using this
            · cases hF
          · cases hF
        | int => simp [fieldsOf] at hF
        | fn _ _ _ _ => simp [fieldsOf] at hF
        | ref _ => simp [fieldsOf] at hF
        | never => simp [fieldsOf] at hF
      · cases h
    · cases h

/-! ## Control-free computations -/

def hasSig (C : Cert) (fn : Nat) (sig : FnSig) : Bool :=
  C.sigs.any fun e => e.fn == fn && e.sig == sig

theorem hasSig_sound {fn : Nat} {sig : FnSig} (h : hasSig C fn sig = true) :
    C.ctx.fnSig fn sig := by
  obtain ⟨e, he, hc⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  exact ⟨e, he, hc.1, hc.2⟩

def checkRhs (C : Cert) (Γ : TEnv) : Rhs → Ty → Bool
  | .atom a, σ => atomTy Γ a == some σ
  | .prim _ args, σ =>
    match args with
    | [a, b] => atomTy Γ a == some .int && atomTy Γ b == some .int && σ == .int
    | _ => false
  | .construct tag args, σ =>
    match ctorFieldsOf C tag σ with
    | some Fs => atomsTy Γ args == some Fs
    | none => false
  | .place pl, σ =>
    match Γ[pl.var]? with
    | some t => placeTy C t pl.path == some σ && dupOk C σ
    | none => false
  | .closure fn captures, σ =>
    match σ, atomsTy Γ captures with
    | .fn Ps r e once, some Cs => hasSig C fn ⟨Cs, Ps, r, e⟩ && (once || Cs.all (dupOk C))
    | _, _ => false

theorem checkRhs_sound {Γ : TEnv} {rhs : Rhs} {σ : Ty} (h : checkRhs C Γ rhs σ = true) :
    HasRhs C.ctx Γ rhs σ := by
  cases rhs with
  | atom a =>
    simp only [checkRhs, beq_iff_eq] at h
    exact .atom (atomTy_sound h)
  | prim p args =>
    simp only [checkRhs] at h
    split at h
    · simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨ha, hb⟩, rfl⟩ := h
      exact .prim (atomTy_sound ha) (atomTy_sound hb)
    · cases h
  | construct tag args =>
    simp only [checkRhs] at h
    split at h
    · rename_i Fs hF
      simp only [beq_iff_eq] at h
      exact .construct (ctorFieldsOf_sound hF) (atomsTy_sound h)
    · cases h
  | place pl =>
    simp only [checkRhs] at h
    split at h
    · rename_i t ht
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact .place ht (placeTy_sound h.1) (dupOk_sound h.2)
    · cases h
  | closure fn captures =>
    simp only [checkRhs] at h
    split at h
    · rename_i Ps r e once Cs hcs
      simp only [Bool.and_eq_true, Bool.or_eq_true] at h
      refine .closure (sig := ⟨Cs, Ps, r, e⟩) (hasSig_sound h.1) (atomsTy_sound hcs)
        (fun ho => ?_)
      rcases h.2 with h2 | h2
      · rw [ho] at h2
        cases h2
      · exact dupOk_all h2
    · cases h

/-! ## Handlers -/

/-- Is there a signature of `fn` with these captures, parameters and result
whose operations `ε` offers? -/
def hasSigLe (C : Cert) (fn : Nat) (Cs Ps : List Ty) (ρ : Ty) (ε : Row) : Bool :=
  C.sigs.any fun e =>
    e.fn == fn && e.sig.caps == Cs && e.sig.params == Ps && e.sig.ret == ρ && rowLe e.sig.eff ε

theorem hasSigLe_sound {fn : Nat} {Cs Ps : List Ty} {ρ : Ty} {ε : Row}
    (h : hasSigLe C fn Cs Ps ρ ε = true) :
    ∃ εa, C.ctx.fnSig fn ⟨Cs, Ps, ρ, εa⟩ ∧ Row.le εa ε := by
  obtain ⟨e, he, hc⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨hfn, hcaps⟩, hps⟩, hret⟩, hrow⟩ := hc
  subst hcaps hps hret
  exact ⟨e.sig.eff, ⟨e, he, hfn, rfl⟩, rowLe_sound hrow⟩

def checkArms (C : Cert) (Cs : List Ty) (ρ : Ty) (ε : Row) : List (Nat × Nat) → Row → Bool
  | [], [] => true
  | (op, arm) :: ops, (op', targs) :: H =>
    op == op'
      && (match findOp C.ops op targs with
          | some (Ps, none) => hasSigLe C arm Cs Ps ρ ε
          | some (Ps, some o) => hasSigLe C arm Cs (Ps ++ [.fn [o] ρ ε true]) ρ ε
          | none => false)
      && checkArms C Cs ρ ε ops H
  | [], _ :: _ => false
  | _ :: _, [] => false

theorem checkArms_sound {Cs : List Ty} {ρ : Ty} {ε : Row} :
    ∀ {ops : List (Nat × Nat)} {H : Row}, checkArms C Cs ρ ε ops H = true →
      ArmsOk C.ctx Cs ρ ε ops H
  | [], [], _ => .nil
  | (op, arm) :: ops, (op', targs) :: H, h => by
    simp only [checkArms, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, harm⟩, hrest⟩ := h
    split at harm
    · rename_i Ps hop
      obtain ⟨εa, hsig, hle⟩ := hasSigLe_sound harm
      exact .terminal hop hsig hle (checkArms_sound hrest)
    · rename_i Ps o hop
      obtain ⟨εa, hsig, hle⟩ := hasSigLe_sound harm
      exact .resumptive hop hsig hle (checkArms_sound hrest)
    · simp at harm
  | [], _ :: _, h => by simp [checkArms] at h
  | _ :: _, [], h => by simp [checkArms] at h

def checkHandler (C : Cert) (Cs : List Ty) (ret : Nat) (ops : List (Nat × Nat)) (σ ρ : Ty)
    (H ε : Row) : Bool :=
  hasSigLe C ret Cs [σ] ρ ε && checkArms C Cs ρ ε ops H && Cs.all (dupOk C)

theorem checkHandler_sound {Cs : List Ty} {ret : Nat} {ops : List (Nat × Nat)} {σ ρ : Ty}
    {H ε : Row} (h : checkHandler C Cs ret ops σ ρ H ε = true) :
    HandlerOk C.ctx Cs ret ops σ ρ H ε := by
  simp only [checkHandler, Bool.and_eq_true] at h
  exact ⟨hasSigLe_sound h.1.1, checkArms_sound h.1.2, dupOk_all h.2⟩

/-! ## Computations -/

/-- Check a computation against the type it must give and the operations it
may perform. Hints are used up in order: one by each `let`, one by each handler,
and one by each call of something that does not return, for the type the code
after the call takes its result to have. -/
def checkTm (C : Cert) : TEnv → Tm → List Hint → Ty → Row → Bool
  | Γ, .ret a, _, τ, _ => atomTy Γ a == some τ
  | Γ, .let_ rhs body, hs, τ, ε =>
    match hs with
    | .ty σ :: hs =>
      checkRhs C Γ rhs σ && linearB C Γ (rhsMoves rhs) (fv body)
        && checkTm C (Γ ++ [σ]) body hs τ ε
    | _ => false
  | Γ, .call f args body, hs, τ, ε =>
    match atomTy Γ f with
    | some (.fn Ps σ ε' _) =>
      atomsTy Γ args == some Ps && rowLe ε' ε
        && linearB C Γ (atomVars (f :: args)) (fv body)
        && (if σ = .never then
              match hs with
              | .ty σ' :: hs => checkTm C (Γ ++ [σ']) body hs τ ε
              | _ => false
            else checkTm C (Γ ++ [σ]) body hs τ ε)
    | _ => false
  | Γ, .tail f args, _, τ, ε =>
    match atomTy Γ f with
    | some (.fn Ps σ ε' _) =>
      (σ == τ || σ == .never) && atomsTy Γ args == some Ps && rowLe ε' ε
        && linearB C Γ (atomVars (f :: args)) []
    | _ => false
  | Γ, .handle ret ops captures thunk body, hs, τ, ε =>
    match hs, atomTy Γ thunk, atomsTy Γ captures with
    | .handler ρ H :: hs, some (.fn [] σ εt _), some Cs =>
      checkHandler C Cs ret ops σ ρ H ε && rowLe εt (H ++ ε)
        && linearB C Γ (atomVars [thunk]) (fv body)
        && checkTm C (Γ ++ [ρ]) body hs τ ε
    | _, _, _ => false
  | Γ, .handleTail ret ops captures thunk, hs, τ, ε =>
    match hs, atomTy Γ thunk, atomsTy Γ captures with
    | .handler _ H :: _, some (.fn [] σ εt _), some Cs =>
      checkHandler C Cs ret ops σ τ H ε && rowLe εt (H ++ ε)
    | _, _, _ => false
  | Γ, .raise op args, _, _, ε =>
    match ε.lookup op with
    | some targs =>
      match findOp C.ops op targs with
      | some (Ps, none) => atomsTy Γ args == some Ps && linearB C Γ (atomVars args) []
      | _ => false
    | none => false
  | Γ, .perform op args body, hs, τ, ε =>
    match ε.lookup op with
    | some targs =>
      match findOp C.ops op targs with
      | some (Ps, some σ) =>
        atomsTy Γ args == some Ps && linearB C Γ (atomVars args) (fv body)
          && checkTm C (Γ ++ [σ]) body hs τ ε
      | _ => false
    | none => false
  | Γ, .label thunk body, hs, τ, ε =>
    match atomTy Γ thunk with
    | some (.fn [.fn [σ'] _ _ _] σ εt _) =>
      σ' == σ && rowLe εt ε && linearB C Γ (atomVars [thunk]) (fv body)
        && checkTm C (Γ ++ [σ]) body hs τ ε
    | _ => false
  | Γ, .labelTail thunk, _, τ, ε =>
    match atomTy Γ thunk with
    | some (.fn [.fn [σ'] _ _ _] σ εt _) => σ' == σ && σ == τ && rowLe εt ε
    | _ => false
  | Γ, .guard cleanup thunk body, hs, τ, ε =>
    match atomTy Γ cleanup, atomTy Γ thunk with
    | some (.fn [] _ [] _), some (.fn [] σ εt _) =>
      rowLe εt ε && linearB C Γ (atomVars [cleanup, thunk]) (fv body)
        && checkTm C (Γ ++ [σ]) body hs τ ε
    | _, _ => false
  | Γ, .guardTail cleanup thunk, _, τ, ε =>
    match atomTy Γ cleanup, atomTy Γ thunk with
    | some (.fn [] _ [] _), some (.fn [] σ εt _) =>
      σ == τ && rowLe εt ε && linearB C Γ (atomVars [cleanup, thunk]) []
    | _, _ => false
  | Γ, .cancel k body, hs, τ, ε =>
    match atomTy Γ k with
    | some (.fn [_] _ ε' _) =>
      rowLe ε' ε && linearB C Γ (atomVars [k]) (fv body)
        && checkTm C (Γ ++ [.unit]) body hs τ ε
    | _ => false
  | Γ, .mem op args body, hs, τ, ε =>
    match op, args with
    | .alloc, [a] =>
      match atomTy Γ a with
      | some σ => linearB C Γ (atomVars [a]) (fv body) && checkTm C (Γ ++ [.ref σ]) body hs τ ε
      | none => false
    | .load, [a] =>
      match atomTy Γ a with
      | some (.ref σ) => dupOk C σ && checkTm C (Γ ++ [σ]) body hs τ ε
      | _ => false
    | .store, [a, b] =>
      match atomTy Γ a with
      | some (.ref σ) =>
        atomTy Γ b == some σ && linearB C Γ (atomVars [b]) (fv body)
          && checkTm C (Γ ++ [.unit]) body hs τ ε
      | _ => false
    | .free, [a] =>
      match atomTy Γ a with
      | some (.ref _) => checkTm C (Γ ++ [.unit]) body hs τ ε
      | _ => false
    | .swap, [a, b] =>
      match atomTy Γ a with
      | some (.ref σ) =>
        atomTy Γ b == some σ && linearB C Γ (atomVars [b]) (fv body)
          && checkTm C (Γ ++ [σ]) body hs τ ε
      | _ => false
    | _, _ => false
  | Γ, .host id args body, hs, τ, ε =>
    match id, args with
    | 0, [a] => (atomTy Γ a).isSome && checkTm C (Γ ++ [.unit]) body hs τ ε
    | 1, [] => checkTm C (Γ ++ [.tuple [.int, .int]]) body hs τ ε
    | _, _ => false

theorem checkTm_sound : ∀ (tm : Tm) {Γ : TEnv} {hs : List Hint} {τ : Ty} {ε : Row},
    checkTm C Γ tm hs τ ε = true → HasTm C.ctx Γ tm τ ε := by
  intro tm
  induction tm with
  | ret a =>
    intro Γ hs τ ε h
    simp only [checkTm, beq_iff_eq] at h
    exact .ret (atomTy_sound h)
  | let_ rhs body ih =>
    intro Γ hs τ ε h
    simp only [checkTm] at h
    split at h
    · simp only [Bool.and_eq_true] at h
      exact .let_ (checkRhs_sound h.1.1) (linearB_sound h.1.2) (ih h.2)
    · simp at h
  | call f args body ih =>
    intro Γ hs τ ε h
    simp only [checkTm] at h
    split at h
    · rename_i Ps σ ε' once hf
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨hargs, hrow⟩, hlin⟩, hbody⟩ := h
      split at hbody
      · rename_i hσ
        subst hσ
        split at hbody
        · exact .callNever (atomTy_sound hf) (atomsTy_sound hargs) (rowLe_sound hrow)
            (linearB_sound hlin) (ih hbody)
        · simp at hbody
      · exact .call (atomTy_sound hf) (atomsTy_sound hargs) (rowLe_sound hrow)
          (linearB_sound hlin) (ih hbody)
    · simp at h
  | tail f args =>
    intro Γ hs τ ε h
    simp only [checkTm] at h
    split at h
    · rename_i Ps σ ε' once hf
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨hσ, hargs⟩, hrow⟩, hlin⟩ := h
      rcases hσ with rfl | rfl
      · exact .tail (atomTy_sound hf) (atomsTy_sound hargs) (rowLe_sound hrow)
          (linearB_sound hlin)
      · exact .tailNever (atomTy_sound hf) (atomsTy_sound hargs) (rowLe_sound hrow)
          (linearB_sound hlin)
    · simp at h
  | handle ret ops captures thunk body ih =>
    intro Γ hs τ ε h
    simp only [checkTm] at h
    split at h
    · rename_i ρ H hs' σ εt once Cs hthunk hcaps
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨hh, hrow⟩, hlin⟩, hbody⟩ := h
      exact .handle (atomTy_sound hthunk) (atomsTy_sound hcaps) (checkHandler_sound hh)
        (rowLe_sound hrow) (linearB_sound hlin) (ih hbody)
    · simp at h
  | handleTail ret ops captures thunk =>
    intro Γ hs τ ε h
    simp only [checkTm] at h
    split at h
    · rename_i ρ H hs' σ εt once Cs hthunk hcaps
      simp only [Bool.and_eq_true] at h
      exact .handleTail (atomTy_sound hthunk) (atomsTy_sound hcaps) (checkHandler_sound h.1)
        (rowLe_sound h.2)
    · simp at h
  | raise op args =>
    intro Γ hs τ ε h
    simp only [checkTm] at h
    split at h
    · rename_i targs hl
      split at h
      · rename_i Ps hop
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        exact .raise hl hop (atomsTy_sound h.1) (linearB_sound h.2)
      · simp at h
    · simp at h
  | perform op args body ih =>
    intro Γ hs τ ε h
    simp only [checkTm] at h
    split at h
    · rename_i targs hl
      split at h
      · rename_i Ps σ hop
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        exact .perform hl hop (atomsTy_sound h.1.1) (linearB_sound h.1.2) (ih h.2)
      · simp at h
    · simp at h
  | label thunk body ih =>
    intro Γ hs τ ε h
    simp only [checkTm] at h
    split at h
    · rename_i σ' ρ εl once' σ εt once hthunk
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨rfl, hrow⟩, hlin⟩, hbody⟩ := h
      exact .label (atomTy_sound hthunk) (rowLe_sound hrow) (linearB_sound hlin) (ih hbody)
    · simp at h
  | labelTail thunk =>
    intro Γ hs τ ε h
    simp only [checkTm] at h
    split at h
    · rename_i σ' ρ εl once' σ εt once hthunk
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, rfl⟩, hrow⟩ := h
      exact .labelTail (atomTy_sound hthunk) (rowLe_sound hrow)
    · simp at h
  | guard cleanup thunk body ih =>
    intro Γ hs τ ε h
    simp only [checkTm] at h
    split at h
    · rename_i σc once' σ εt once hcl hthunk
      simp only [Bool.and_eq_true] at h
      exact .guard (atomTy_sound hcl) (atomTy_sound hthunk) (rowLe_sound h.1.1)
        (linearB_sound h.1.2) (ih h.2)
    · simp at h
  | guardTail cleanup thunk =>
    intro Γ hs τ ε h
    simp only [checkTm] at h
    split at h
    · rename_i σc once' σ εt once hcl hthunk
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, hrow⟩, hlin⟩ := h
      exact .guardTail (atomTy_sound hcl) (atomTy_sound hthunk) (rowLe_sound hrow)
        (linearB_sound hlin)
    · simp at h
  | cancel k body ih =>
    intro Γ hs τ ε h
    simp only [checkTm] at h
    split at h
    · rename_i σ ρ ε' once hk
      simp only [Bool.and_eq_true] at h
      exact .cancel (atomTy_sound hk) (rowLe_sound h.1.1) (linearB_sound h.1.2) (ih h.2)
    · simp at h
  | mem op args body ih =>
    intro Γ hs τ ε h
    simp only [checkTm] at h
    split at h
    · split at h
      · rename_i σ ha
        simp only [Bool.and_eq_true] at h
        exact .alloc (atomTy_sound ha) (linearB_sound h.1) (ih h.2)
      · simp at h
    · split at h
      · rename_i σ ha
        simp only [Bool.and_eq_true] at h
        exact .load (atomTy_sound ha) (dupOk_sound h.1) (ih h.2)
      · simp at h
    · split at h
      · rename_i σ ha
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        exact .store (atomTy_sound ha) (atomTy_sound h.1.1) (linearB_sound h.1.2) (ih h.2)
      · simp at h
    · split at h
      · rename_i σ ha
        exact .free (atomTy_sound ha) (ih h)
      · simp at h
    · split at h
      · rename_i σ ha
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        exact .swap (atomTy_sound ha) (atomTy_sound h.1.1) (linearB_sound h.1.2) (ih h.2)
      · simp at h
    · simp at h
  | host id args body ih =>
    intro Γ hs τ ε h
    simp only [checkTm] at h
    split at h
    · simp only [Bool.and_eq_true, Option.isSome_iff_exists] at h
      obtain ⟨⟨σ, ha⟩, hbody⟩ := h
      exact .write (atomTy_sound ha) (ih hbody)
    · exact .read (ih h)
    · simp at h

/-! ## Patterns and clauses -/

mutual

/-- The types of what a pattern binds from a value of a type, if it fits that type. -/
def patTys (C : Cert) : Pat → Ty → Option (List Ty)
  | .wild, _ => some []
  | .bind, τ => some [τ]
  | .int _, τ => if τ = .int then some [] else none
  | .ctor tag ps, T =>
    match ctorFieldsOf C tag T with
    | some Fs => patsTys C ps Fs
    | none => none

def patsTys (C : Cert) : List Pat → List Ty → Option (List Ty)
  | [], [] => some []
  | p :: ps, τ :: τs =>
    match patTys C p τ, patsTys C ps τs with
    | some B, some Bs => some (B ++ Bs)
    | _, _ => none
  | [], _ :: _ => none
  | _ :: _, [] => none

end

mutual

theorem patTys_sound : ∀ {p : Pat} {τ : Ty} {Bs : List Ty},
    patTys C p τ = some Bs → PatOk C.ctx p τ Bs
  | .wild, _, _, h => by
    simp only [patTys, Option.some.injEq] at h
    subst h
    exact .wild
  | .bind, _, _, h => by
    simp only [patTys, Option.some.injEq] at h
    subst h
    exact .bind
  | .int n, τ, _, h => by
    simp only [patTys] at h
    split at h
    · rename_i hτ
      subst hτ
      cases h
      exact .int
    · cases h
  | .ctor tag ps, T, _, h => by
    simp only [patTys] at h
    split at h
    · rename_i Fs hF
      exact .ctor (ctorFieldsOf_sound hF) (patsTys_sound h)
    · cases h

theorem patsTys_sound : ∀ {ps : List Pat} {τs Bs : List Ty},
    patsTys C ps τs = some Bs → PatsOk C.ctx ps τs Bs
  | [], [], _, h => by
    simp only [patsTys, Option.some.injEq] at h
    subst h
    exact .nil
  | p :: ps, τ :: τs, _, h => by
    simp only [patsTys] at h
    split at h
    · rename_i B Bs' hB hBs
      cases h
      exact .cons (patTys_sound hB) (patsTys_sound hBs)
    · cases h
  | [], _ :: _, _, h => by simp [patsTys] at h
  | _ :: _, [], _, h => by simp [patsTys] at h

end

/-- Does a body leave alone every argument its patterns take apart? -/
def wildOk (pats : List Pat) (live : List Nat) : Bool :=
  (List.range pats.length).all fun i =>
    match pats[i]? with
    | some p => isWild p || !live.contains i
    | none => true

theorem wildOk_sound {pats : List Pat} {live : List Nat} (h : wildOk pats live = true) :
    ∀ i p, pats[i]? = some p → isWild p = false → i ∉ live := by
  intro i p hp hw
  have hlt : i < pats.length := by
    rcases Nat.lt_or_ge i pats.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hp
      cases hp
  have := List.all_eq_true.mp h i (List.mem_range.mpr hlt)
  simpa [hp, hw] using this

/-- Check each clause of a function at a signature, with that clause's hints. -/
def checkClauses (C : Cert) (sig : FnSig) : List Clause → List (List Hint) → Bool
  | [], [] => true
  | c :: cs, h :: hs =>
    (match patsTys C c.pats sig.params with
      | some Bs => checkTm C (sig.params ++ sig.caps ++ Bs) c.body h sig.ret sig.eff
      | none => false)
      && wildOk c.pats (fv c.body)
      && checkClauses C sig cs hs
  | [], _ :: _ => false
  | _ :: _, [] => false

theorem checkClauses_sound {sig : FnSig} : ∀ {cs : List Clause} {hs : List (List Hint)},
    checkClauses C sig cs hs = true → ∀ c, c ∈ cs → ClauseOk C.ctx sig c
  | [], _, _, c, hc => by cases hc
  | c :: cs, h :: hs, hcheck, c', hc' => by
    simp only [checkClauses, Bool.and_eq_true] at hcheck
    obtain ⟨⟨hhead, hwild⟩, hrest⟩ := hcheck
    rcases List.mem_cons.mp hc' with rfl | hmem
    · split at hhead
      · rename_i Bs hBs
        exact ⟨⟨Bs, patsTys_sound hBs, checkTm_sound _ hhead⟩, wildOk_sound hwild⟩
      · simp at hhead
    · exact checkClauses_sound hrest c' hmem
  | _ :: _, [], hcheck, _, _ => by simp [checkClauses] at hcheck

end Glorious.Typing
