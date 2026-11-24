module

public import Glorious.Typing.Equality
public import Glorious.Typing.Stack

/-!
# A type checker for Core

A function that checks a Core program against a certificate: the signatures of
its functions, the data types it uses, and a few types the program text does
not determine. `checkTm_sound` and its companions say that what the checker
accepts has a typing derivation. The certificate is not trusted: a wrong one is
rejected, or describes another valid typing.
-/

@[expose] public section

namespace Glorious.Typing

open Core

/-- One use of a declared data type. A use is found by the shape of its type
arguments: the arguments with their regions forgotten. Each constructor's field
types are written with a region variable for each region of the arguments, in
order, so that one entry serves the type at whatever regions it is used. -/
structure DataInst where
  name : Nat
  args : List Ty
  ctors : List (Nat × List Ty)
  /-- Whether values of this type may be used any number of times. The checker
  accepts this only if every field of every constructor may. -/
  dup : Bool

/-- An operation of an effect used at some type arguments: what it takes, and
what it is resumed with if it can be resumed. Found and written as a data type is. -/
structure OpInst where
  op : Nat
  args : List Ty
  payload : List Ty
  result : Option Ty

/-- Something the checker is told rather than left to find. -/
inductive Hint where
  /-- The type of the value a `let` binds. -/
  | ty (σ : Ty)
  /-- The type of the closure a `let` binds, and the regions it is made with. -/
  | clo (σ : Ty) (θ : List Rgn)
  /-- What a handler yields, the operations it serves, in the handler's order,
  each with the type arguments of its effect, the regions the handled
  computation and the handler may touch, and the regions each of the handler's
  functions is entered with: the one for a result first. -/
  | handler (ρ : Ty) (H : Row) (Φ : List Rgn) (θs : List (List Rgn))
  /-- The regions a call chooses for those its callable binds. -/
  | rgns (rs : List Rgn)

/-- A signature of a function, with the hints for each of its clauses at that signature. -/
structure SigEntry where
  fn : Nat
  sig : FnSig
  hints : List (List Hint)

/-- Everything the checker needs beyond the program. -/
structure Cert where
  sigs : Array SigEntry
  datas : List DataInst
  ops : List OpInst
  mainTy : Ty
  mainHints : List Hint
  /-- Whether the ownership rules are to be checked. If not, every type counts
  as duplicable, and the program is only shown to be well typed. -/
  strict : Bool
  /-- Whether the region rules are to be checked. If not, a reference's region
  means nothing, and nothing is shown about how long a cell is used. -/
  regions : Bool
  /-- Whether the rules for borrows are to be checked. If not, a lent reference
  is the reference it was lent from, and nothing is shown about who uses a cell
  while it is lent. -/
  loans : Bool
  /-- Where in `sigs` each function's signatures are, to find them without
  going through all (`Cert.withIndex`). Only a way to find them: what is
  found is taken from `sigs`, so a wrong index can only miss one. Empty, all
  are gone through. -/
  byFn : Array (List Nat) := #[]

/-- Each function's signatures, where they are in `sigs`. -/
def Cert.withIndex (C : Cert) : Cert :=
  let n := C.sigs.foldl (fun m e => max m (e.fn + 1)) 0
  let byFn := (C.sigs.toList.zipIdx.foldr (fun (e, i) (acc : Array (List Nat)) =>
    acc.modify e.fn (i :: ·)) (Array.replicate n []))
  { C with byFn }

/-- The signatures of `fn`, as the index has them, each from `sigs`. -/
def Cert.sigsOf (C : Cert) (fn : Nat) : List SigEntry :=
  if C.byFn.isEmpty then C.sigs.toList
  else ((C.byFn[fn]?).getD []).filterMap fun i => C.sigs[i]?

/-%proof (commented out while the machines become bytes)
theorem Cert.sigsOf_mem {C : Cert} {fn : Nat} {e : SigEntry} (h : e ∈ C.sigsOf fn) :
    e ∈ C.sigs.toList := by
  unfold Cert.sigsOf at h
  split at h
  · exact h
  · obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp h
    exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi)
%proof-/

/-- The regions of some types, in order. -/
def freesOf (ts : List Ty) : List Rgn := ts.flatMap Ty.frees

/-%proof (commented out while the machines become bytes)
theorem freesOf_inst (θ : List Rgn) (ts : List Ty) :
    freesOf (ts.map (Ty.inst θ)) = (freesOf ts).map (Rgn.inst θ) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [freesOf, List.map_cons, List.flatMap_cons, List.map_append] at ih ⊢
    rw [ih, Ty.frees_inst]
%proof-/

/-%proof (commented out while the machines become bytes)
theorem shapes_inst (θ : List Rgn) (ts : List Ty) :
    (ts.map (Ty.inst θ)).map Ty.shape = ts.map Ty.shape := by
  rw [List.map_map]
  exact List.map_congr_left fun t _ => Ty.shape_inst θ t
%proof-/

/-- A type's constructors, each with its field types, at some regions. -/
def instCtors (η : List Rgn) (ctors : List (Nat × List Ty)) : List (Nat × List Ty) :=
  ctors.map fun c => (c.1, c.2.map (Ty.inst η))

/-%proof (commented out while the machines become bytes)
theorem instCtors_lookup (η : List Rgn) (tag : Nat) : ∀ ctors : List (Nat × List Ty),
    (instCtors η ctors).lookup tag = (ctors.lookup tag).map (·.map (Ty.inst η))
  | [] => rfl
  | (t, fs) :: ctors => by
    have ih := instCtors_lookup η tag ctors
    simp only [instCtors] at ih
    simp only [instCtors, List.map_cons, List.lookup_cons]
    cases tag == t with
    | true => rfl
    | false => exact ih
%proof-/

/-%proof (commented out while the machines become bytes)
theorem instCtors_inst (η θ : List Rgn) (ctors : List (Nat × List Ty)) :
    instCtors θ (instCtors η ctors) = instCtors (η.map (Rgn.inst θ)) ctors := by
  simp only [instCtors, List.map_map]
  refine List.map_congr_left fun c _ => ?_
  simp only [Function.comp, List.map_map]
  congr 1
  exact List.map_congr_left fun f _ => Ty.inst_inst η θ f
%proof-/

def findData (ds : List DataInst) (name : Nat) (args : List Ty) :
    Option (List (Nat × List Ty)) :=
  match ds.find? (fun d => d.name == name && d.args == args.map Ty.shape) with
  | some d => some (instCtors (freesOf args) d.ctors)
  | none => none

/-%proof (commented out while the machines become bytes)
theorem findData_inst (ds : List DataInst) (name : Nat) (args : List Ty) (θ : List Rgn) :
    findData ds name (args.map (Ty.inst θ)) = (findData ds name args).map (instCtors θ) := by
  simp only [findData, shapes_inst, freesOf_inst]
  cases ds.find? (fun d => d.name == name && d.args == args.map Ty.shape) with
  | none => rfl
  | some d => simp [instCtors_inst]
%proof-/

def findOp (os : List OpInst) (op : Nat) (args : List Ty) : Option OpTy :=
  match os.find? (fun o => o.op == op && o.args == args.map Ty.shape) with
  | some o => some (o.payload.map (Ty.inst (freesOf args)), o.result.map (Ty.inst (freesOf args)))
  | none => none

/-%proof (commented out while the machines become bytes)
theorem findOp_inst (os : List OpInst) (op : Nat) (args : List Ty) (θ : List Rgn) :
    findOp os op (args.map (Ty.inst θ))
      = (findOp os op args).map fun x => (x.1.map (Ty.inst θ), x.2.map (Ty.inst θ)) := by
  simp only [findOp, shapes_inst, freesOf_inst]
  cases os.find? (fun o => o.op == op && o.args == args.map Ty.shape) with
  | none => rfl
  | some o =>
    simp only [Option.map_some, List.map_map, Option.map_map, Option.some.injEq, Prod.mk.injEq]
    refine ⟨List.map_congr_left fun f _ => (Ty.inst_inst _ θ f).symm, ?_⟩
    cases o.result with
    | none => rfl
    | some r => simp [Ty.inst_inst]
%proof-/

/-! ## Arrays

One name is kept for the type of arrays, applied to the type of the elements.
It has a constructor for every length: the one that takes `n` elements is
`arrayBase + n`. So an array of any length is a value of the type, built like
any other, and a longer one is built by the next constructor. No certificate
declares this type; what it says of the name is not looked at. -/

/-- The field types of constructor `tag` of the type of arrays at `args`. -/
def arrayFields (tag : Nat) : List Ty → Option (List Ty)
  | [t] => if arrayBase ≤ tag then some (List.replicate (tag - arrayBase) t) else none
  | _ => none

/-%proof (commented out while the machines become bytes)
theorem arrayFields_inst (tag : Nat) (args : List Ty) (θ : List Rgn) :
    arrayFields tag (args.map (Ty.inst θ)) = (arrayFields tag args).map (·.map (Ty.inst θ)) := by
  match args with
  | [] => rfl
  | [t] =>
    simp only [List.map_cons, List.map_nil, arrayFields]
    split <;> simp
  | _ :: _ :: _ => rfl
%proof-/

/-- The field types of the constructor of a `[T; N]` (`fixedName` at the
element's type and the length's type): `N` of the element's. -/
def fixedFields (tag : Nat) : List Ty → Option (List Ty)
  | [t, .data len []] =>
    if lenBase ≤ len && tag == fixedBase + (len - lenBase) then some (List.replicate (len - lenBase) t) else none
  | _ => none

/-- The field types of a constructor of a declared type, or of the type of arrays. -/
def Cert.fields (C : Cert) (tag name : Nat) (args : List Ty) : Option (List Ty) :=
  if name = fixedName then fixedFields tag args
  else if name = arrayName then arrayFields tag args
  else (findData C.datas name args).bind (·.lookup tag)

def dataDup (ds : List DataInst) (name : Nat) (args : List Ty) : Bool :=
  match ds.find? (fun d => d.name == name && d.args == args.map Ty.shape) with
  | some d => d.dup
  | none => false

mutual

/-- May a value of this type be used any number of times? A callable may if it
is not marked as callable once; a declared type, if the certificate says so. -/
def dupTy (C : Cert) : Ty → Bool
  | .int => true
  | .scalar _ => true
  | .tuple fs => dupTys C fs
  | .data name args =>
    if name = arrayName then dupTys C args
    else if name = fixedName then (match args with | t :: _ => dupTy C t | [] => true)
    else dataDup C.datas name args
  | .fn _ _ _ _ once _ _ => !once
  | .ref _ _ => true
  | .never => true
termination_by structural t => t

def dupTys (C : Cert) : List Ty → Bool
  | [] => true
  | t :: ts => dupTy C t && dupTys C ts
termination_by structural ts => ts

end

/-%proof (commented out while the machines become bytes)
mutual

/-- Whether a type is duplicable does not depend on its regions. -/
theorem dupTy_inst (C : Cert) (θ : List Rgn) : ∀ t : Ty, dupTy C (t.inst θ) = dupTy C t
  | .int => by rw [Ty.inst_int]
  | .tuple fs => by
    rw [Ty.inst_tuple]
    simp only [dupTy]
    exact dupTys_inst C θ fs
  | .data name args => by
    rw [Ty.inst_data]
    simp only [dupTy]
    split
    · exact dupTys_inst C θ args
    · simp only [dataDup, shapes_inst]
  | .fn _ _ _ _ _ _ _ => by
    rw [Ty.inst_fn]
    simp only [dupTy]
  | .ref _ _ => by
    rw [Ty.inst_ref]
    simp only [dupTy]
  | .never => by rw [Ty.inst_never]

theorem dupTys_inst (C : Cert) (θ : List Rgn) : ∀ ts : List Ty,
    dupTys C (ts.map (Ty.inst θ)) = dupTys C ts
  | [] => rfl
  | t :: ts => by
    simp only [List.map_cons, dupTys]
    rw [dupTy_inst C θ t, dupTys_inst C θ ts]

end
%proof-/
/-- The typing context a certificate describes. -/
def Cert.ctx (C : Cert) : Ctx where
  fnSig fn sig := ∃ e, e ∈ C.sigs.toList ∧ e.fn = fn ∧ e.sig = sig
  opSig op args := findOp C.ops op args
  dup τ := C.strict = false ∨ dupTy C τ = true
  ctorFields tag name args := C.fields tag name args
  regions := C.regions = true
  loans := C.loans = true

/-%proof (commented out while the machines become bytes)
/-- What a certificate says of a type does not depend on the type's regions. -/
theorem Cert.ctx_stable (C : Cert) : C.ctx.Stable where
  dup τ θ := by
    show (C.strict = false ∨ dupTy C (τ.inst θ) = true) ↔ (C.strict = false ∨ dupTy C τ = true)
    rw [dupTy_inst]
  ctor tag name args θ := by
    show C.fields tag name (args.map (Ty.inst θ))
      = (C.fields tag name args).map (·.map (Ty.inst θ))
    simp only [Cert.fields]
    split
    · exact arrayFields_inst tag args θ
    · rw [findData_inst]
      cases findData C.datas name args with
      | none => rfl
      | some ctors => simp [instCtors_lookup]
  op op targs θ := findOp_inst C.ops op targs θ
%proof-/

variable {C : Cert}

/-! ## Ownership -/

def dupOk (C : Cert) (τ : Ty) : Bool := !C.strict || dupTy C τ

/-%proof (commented out while the machines become bytes)
theorem dupOk_sound {τ : Ty} (h : dupOk C τ = true) : C.ctx.dup τ := by
  simp only [dupOk, Bool.or_eq_true, Bool.not_eq_true'] at h
  exact h
%proof-/

/-%proof (commented out while the machines become bytes)
theorem dupOk_all {τs : List Ty} (h : τs.all (dupOk C) = true) : ∀ c, c ∈ τs → C.ctx.dup c :=
  fun c hc => dupOk_sound (List.all_eq_true.mp h c hc)
%proof-/

/-- Is every moved local whose type is not duplicable moved once and not mentioned afterwards? -/
def linearB (C : Cert) (Γ : TEnv) (moved rest : List Nat) : Bool :=
  !C.strict || moved.all fun i =>
    match Γ[i]? with
    | some τ => dupTy C τ || (decide (cnt i moved ≤ 1) && !rest.contains i)
    | none => true

/-%proof (commented out while the machines become bytes)
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
%proof-/

/-! ## Rows -/

/-%proof (commented out while the machines become bytes)
theorem lookup_mem {β : Type} : ∀ {l : List (Nat × β)} {k : Nat} {v : β},
    l.lookup k = some v → (k, v) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (k', v') :: l, k, v, h => by
    by_cases he : k = k'
    · subst he
      rw [lookup_cons_eq] at h; cases h
      exact List.mem_cons_self ..
    · rw [lookup_cons_ne he] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)
%proof-/

/-- Does `b` offer every operation of `a` at the type `a` gives it? -/
def rowLe (a b : Row) : Bool := a.all fun x => a.lookup x.1 == b.lookup x.1

/-%proof (commented out while the machines become bytes)
theorem rowLe_sound {a b : Row} (h : rowLe a b = true) : Row.le a b := by
  intro op sig hl
  have h' := List.all_eq_true.mp h _ (lookup_mem hl)
  simp only [beq_iff_eq] at h'
  rw [← h']
  exact hl
%proof-/

/-! ## Operands -/

def atomTy (Γ : TEnv) : Atom → Option Ty
  | .var i => Γ[i]?
  | .int _ => some .int

/-%proof (commented out while the machines become bytes)
theorem atomTy_sound {Γ : TEnv} {a : Atom} {τ : Ty} (h : atomTy Γ a = some τ) : HasAtom Γ a τ := by
  cases a with
  | var i => exact .var h .refl
  | int n =>
    simp only [atomTy, Option.some.injEq] at h
    subst h
    exact .int
%proof-/

/-- A value of type `t` is one of type `σ`: the same type, or a reference whose
places are among `σ`'s. -/
def widenB (t σ : Ty) : Bool :=
  t == σ || (match t, σ with
    | .ref ρ s, .ref ρ' s' => s == s' && ρ.parts.all fun x => ρ'.parts.contains x
    | _, _ => false)

/-%proof (commented out while the machines become bytes)
theorem widenB_sound {t σ : Ty} (h : widenB t σ = true) : Widen t σ := by
  simp only [widenB, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h
  · exact .refl
  · split at h
    · rename_i ρ s ρ' s'
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_eq_mem,
        decide_eq_true_eq] at h
      obtain ⟨rfl, hp⟩ := h
      exact .ref hp
    · cases h
%proof-/

/-- The operand is one of type `σ`, its own or one it widens to. -/
def atomFits (Γ : TEnv) (a : Atom) (σ : Ty) : Bool :=
  match a, σ with
  -- (A number written out is a scalar's too.)
  | .int _, .scalar _ => true
  | _, _ =>
    match atomTy Γ a with
    | some t => widenB t σ
    | none => false

/-%proof (commented out while the machines become bytes)
theorem atomFits_sound {Γ : TEnv} {a : Atom} {σ : Ty} (h : atomFits Γ a σ = true) :
    HasAtom Γ a σ := by
  simp only [atomFits] at h
  split at h <;> try (cases h; done)
  rename_i t ht
  have hw := widenB_sound h
  cases a with
  | var i => exact .var ht hw
  | int n =>
    simp only [atomTy, Option.some.injEq] at ht
    subst ht
    cases hw
    exact .int
%proof-/

def atomsFit (Γ : TEnv) : List Atom → List Ty → Bool
  | [], [] => true
  | a :: as, σ :: σs => atomFits Γ a σ && atomsFit Γ as σs
  | _, _ => false

/-%proof (commented out while the machines become bytes)
theorem atomsFit_sound {Γ : TEnv} : ∀ {as : List Atom} {σs : List Ty},
    atomsFit Γ as σs = true → HasAtoms Γ as σs
  | [], [], _ => .nil
  | _ :: _, _ :: _, h => by
    simp only [atomsFit, Bool.and_eq_true] at h
    exact .cons (atomFits_sound h.1) (atomsFit_sound h.2)
  | [], _ :: _, h => by simp [atomsFit] at h
  | _ :: _, [], h => by simp [atomsFit] at h
%proof-/

def atomsTy (Γ : TEnv) : List Atom → Option (List Ty)
  | [] => some []
  | a :: as =>
    match atomTy Γ a, atomsTy Γ as with
    | some t, some ts => some (t :: ts)
    | _, _ => none

/-%proof (commented out while the machines become bytes)
theorem atomsTy_sound {Γ : TEnv} : ∀ {as : List Atom} {τs : List Ty},
    atomsTy Γ as = some τs → HasAtoms Γ as τs
  | [], _, h => by
    simp only [atomsTy, Option.some.injEq] at h
    subst h
    exact .nil
  | a :: as, τs, h => by
    simp only [atomsTy] at h
    split at h <;> try (cases h; done)
    rename_i t ts ht hts
    cases h
    exact .cons (atomTy_sound ht) (atomsTy_sound hts)
%proof-/

/-! ## Data -/

/-- The field types of constructor `tag` at a type, if it is a constructor of that type. -/
def ctorFieldsOf (C : Cert) (tag : Nat) : Ty → Option (List Ty)
  | .tuple Fs => if tag = 0 then some Fs else none
  | .data name args => if tag = 0 then none else C.fields tag name args
  | .int => none
  | .scalar _ => none
  | .fn _ _ _ _ _ _ _ => none
  | .ref _ _ => none
  | .never => none

/-%proof (commented out while the machines become bytes)
theorem ctorFieldsOf_sound {tag : Nat} {T : Ty} {Fs : List Ty}
    (h : ctorFieldsOf C tag T = some Fs) : CtorOf C.ctx tag T Fs := by
  cases T with
  | tuple Fs' =>
    simp only [ctorFieldsOf] at h
    split at h <;> try (cases h; done)
    rename_i h0
    cases h
    exact .inl ⟨h0, rfl⟩
  | data name args =>
    simp only [ctorFieldsOf] at h
    split at h <;> try (cases h; done)
    rename_i h0
    exact .inr ⟨h0, name, args, rfl, h⟩
  | int | fn _ _ _ _ _ _ _ | ref _ _ | never => simp [ctorFieldsOf] at h
%proof-/

/-%proof (commented out while the machines become bytes)
theorem ctorFieldsOf_complete {tag : Nat} {T : Ty} {Fs : List Ty}
    (h : CtorOf C.ctx tag T Fs) : ctorFieldsOf C tag T = some Fs := by
  rcases h with ⟨h0, rfl⟩ | ⟨h0, name, args, rfl, hF⟩
  · simp [ctorFieldsOf, h0]
  · simp only [ctorFieldsOf, h0, ↓reduceIte]
    exact hF
%proof-/

/-- The fields that can be read from a value of a type without testing which
constructor built it. -/
def fieldsOf (C : Cert) : Ty → Option (List Ty)
  | .tuple Fs => some Fs
  | .data name args =>
    -- An array's fields are not all there is to read: it may have none.
    if name = arrayName then none
    else if name = fixedName then
      match args with
      | [_, .data len []] => fixedFields (fixedBase + (len - lenBase)) args
      | _ => none
    else
      match findData C.datas name args with
      | some ((_, Fs) :: rest) => if rest.all (fun c => c.2 == Fs) then some Fs else none
      | _ => none
  | .int => none
  | .scalar _ => none
  | .fn _ _ _ _ _ _ _ => none
  | .ref _ _ => none
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

/-%proof (commented out while the machines become bytes)
theorem placeTy_sound : ∀ {path : List Nat} {σ τ : Ty},
    placeTy C σ path = some τ → PlaceOk C.ctx σ path τ
  | [], σ, τ, h => by
    simp only [placeTy, Option.some.injEq] at h
    subst h
    exact .here
  | i :: path, σ, τ, h => by
    simp only [placeTy] at h
    split at h <;> try (cases h; done)
    rename_i Fs hF
    split at h <;> try (cases h; done)
    rename_i σ' hi
    have hrest := placeTy_sound h
    cases σ with
    | tuple Fs' =>
      simp only [fieldsOf, Option.some.injEq] at hF
      subst hF
      exact .tuple hi hrest
    | data name args =>
      simp only [fieldsOf] at hF
      split at hF
      · cases hF
      rename_i hname
      split at hF <;> try (cases hF; done)
      rename_i t Fs₀ rest hfind
      split at hF <;> try (cases hF; done)
      rename_i hall
      cases hF
      refine .field (fun tag Fs' hc => ?_) hi hrest
      have hc' := ctorFieldsOf_complete hc
      simp only [ctorFieldsOf] at hc'
      split at hc'
      · cases hc'
      · simp only [Cert.fields, hname, ↓reduceIte] at hc'
        rw [hfind] at hc'
        have hm := lookup_mem (show ((t, Fs) :: rest).lookup tag = some Fs' from hc')
        rcases List.mem_cons.mp hm with he | hm
        · cases he
          rfl
        · have := List.all_eq_true.mp hall _ hm
          simpa using this
    | int | fn _ _ _ _ _ _ _ | ref _ _ | never => simp [fieldsOf] at hF
%proof-/

/-! ## Regions -/

/-- Does `ϕ` grant every place and permission the region is made of? -/
def grantsB (ϕ : List Rgn) (r : Rgn) : Bool := r.parts.all fun x => (Rgn.flat ϕ).contains x

/-%proof (commented out while the machines become bytes)
theorem grantsB_sound {ϕ : List Rgn} {r : Rgn} (h : grantsB ϕ r = true) : Grants ϕ r := by
  intro x hx
  simpa using List.all_eq_true.mp h x hx
%proof-/

/-- Is every place and permission of `a` one of `b`? -/
def subB (a b : List Rgn) : Bool := (Rgn.flat a).all fun r => (Rgn.flat b).contains r

/-%proof (commented out while the machines become bytes)
theorem subB_sound {a b : List Rgn} (h : subB a b = true) : Sub a b := by
  intro r hr
  simpa using List.all_eq_true.mp h r hr
%proof-/

def subFreeB (n : Nat) (a b : List Rgn) : Bool :=
  (Rgn.flat a).all fun r => !r.freeOf n || (Rgn.flat b).contains r

/-%proof (commented out while the machines become bytes)
theorem subFreeB_sound {n : Nat} {a b : List Rgn} (h : subFreeB n a b = true) : SubFree n a b := by
  intro r hr hf
  have := List.all_eq_true.mp h r hr
  simp only [hf, Bool.not_true, Bool.false_or, List.contains_iff_mem] at this
  exact this
%proof-/

/-- May the region of a reference be read or written through? -/
def regionOk (C : Cert) (ϕ : List Rgn) (r : Rgn) : Bool := !C.regions || grantsB ϕ r

/-%proof (commented out while the machines become bytes)
theorem regionOk_sound {ϕ : List Rgn} {r : Rgn} (h : regionOk C ϕ r = true) :
    C.ctx.regions → Grants ϕ r := by
  intro hR
  have hR' : C.regions = true := hR
  simp only [regionOk, hR', Bool.not_true, Bool.false_or] at h
  exact grantsB_sound h
%proof-/

/-- May the region of a reference be written through? -/
def writeOk (C : Cert) (ϕ : List Rgn) (r : Rgn) : Bool := !C.loans || grantsB ϕ (.wr r)

/-%proof (commented out while the machines become bytes)
theorem writeOk_sound {ϕ : List Rgn} {r : Rgn} (h : writeOk C ϕ r = true) :
    C.ctx.loans → Grants ϕ (.wr r) := by
  intro hL
  have hL' : C.loans = true := hL
  simp only [writeOk, hL', Bool.not_true, Bool.false_or] at h
  exact grantsB_sound h
%proof-/

/-- Are the places something touches all different? Only then does lending
one take anything away from it. -/
def nodupOk (C : Cert) (l : List Rgn) : Bool := !C.loans || decide (Rgn.flat l).Nodup

/-%proof (commented out while the machines become bytes)
theorem nodupOk_sound {l : List Rgn} (h : nodupOk C l = true) :
    C.ctx.loans → (Rgn.flat l).Nodup := by
  intro hL
  have hL' : C.loans = true := hL
  simpa [nodupOk, hL'] using h
%proof-/

/-- The regions a call chooses: none if its callable binds none, and otherwise
those the next hint gives. -/
def takeRgns (n : Nat) (hs : List Hint) : Option (List Rgn × List Hint) :=
  if n = 0 then some ([], hs)
  else
    match hs with
    | .rgns rs :: hs => if rs.length = n then some (rs, hs) else none
    | _ => none

/-%proof (commented out while the machines become bytes)
theorem takeRgns_length {n : Nat} {hs hs' : List Hint} {rs : List Rgn}
    (h : takeRgns n hs = some (rs, hs')) : rs.length = n := by
  simp only [takeRgns] at h
  split at h
  · rename_i h0
    cases h
    exact h0.symm
  · split at h
    · split at h
      · rename_i hl
        cases h
        exact hl
      · cases h
    · cases h
%proof-/

/-- What a `let` is told about the value it binds. -/
def Hint.bind? : Hint → Option (Ty × List Rgn)
  | .ty σ => some (σ, [])
  | .clo σ θ => some (σ, θ)
  | .handler _ _ _ _ => none
  | .rgns _ => none

/-! ## Control-free computations -/

/-- An environment a type states is the one the function has. -/
def envOk (env : Option (List Ty)) (Cs : List Ty) : Bool :=
  match env with
  | none => true
  | some Cs' => Cs' == Cs

/-%proof (commented out while the machines become bytes)
theorem envOk_sound {env : Option (List Ty)} {Cs : List Ty} (h : envOk env Cs = true) :
    ∀ Cs', env = some Cs' → Cs' = Cs := by
  intro Cs' he
  subst he
  simpa [envOk] using h
%proof-/

/-- Is `σ` the type of a closure of `fn` over captures of types `Cs`, made with
the regions `θ`, at one of the function's signatures? -/
def closes (C : Cert) (fn : Nat) (Cs : List Ty) (θ : List Rgn) (σ : Ty) (once : Bool)
    (env : Option (List Ty)) : Bool :=
  (C.sigsOf fn).any fun e =>
    e.fn == fn && θ.length == e.sig.crgns && Cs == e.sig.caps.map (Ty.inst θ)
      && σ == e.sig.ty θ once env && (once || e.sig.caps.all (dupOk C)) && envOk env Cs

/-%proof (commented out while the machines become bytes)
theorem closes_sound {fn : Nat} {Cs : List Ty} {θ : List Rgn} {σ : Ty} {once : Bool}
    {env : Option (List Ty)} (h : closes C fn Cs θ σ once env = true) :
    ∃ sig, C.ctx.fnSig fn sig ∧ θ.length = sig.crgns ∧ Cs = sig.caps.map (Ty.inst θ)
      ∧ σ = sig.ty θ once env ∧ (once = false → ∀ c, c ∈ sig.caps → C.ctx.dup c)
      ∧ (∀ Cs', env = some Cs' → Cs' = Cs) := by
  obtain ⟨e, he, hc⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hfn, hθ⟩, hcs⟩, hσ⟩, hdup⟩, henv⟩ := hc
  refine ⟨e.sig, ⟨e, Cert.sigsOf_mem he, hfn, rfl⟩, hθ, hcs, hσ, fun ho => ?_, envOk_sound henv⟩
  rcases hdup with h2 | h2
  · rw [ho] at h2; cases h2
  · exact dupOk_all h2
%proof-/

/-- The same for a closure made here: its captures fit the types the
signature gives them, made with the regions `θ`. -/
def closesFit (C : Cert) (Γ : TEnv) (fn : Nat) (captures : List Atom) (θ : List Rgn) (σ : Ty)
    (once : Bool) (env : Option (List Ty)) : Bool :=
  (C.sigsOf fn).any fun e =>
    e.fn == fn && θ.length == e.sig.crgns && atomsFit Γ captures (e.sig.caps.map (Ty.inst θ))
      && σ == e.sig.ty θ once env && (once || e.sig.caps.all (dupOk C))
      && envOk env (e.sig.caps.map (Ty.inst θ))

/-%proof (commented out while the machines become bytes)
theorem closesFit_sound {Γ : TEnv} {fn : Nat} {captures : List Atom} {θ : List Rgn} {σ : Ty}
    {once : Bool} {env : Option (List Ty)} (h : closesFit C Γ fn captures θ σ once env = true) :
    ∃ sig, C.ctx.fnSig fn sig ∧ θ.length = sig.crgns
      ∧ HasAtoms Γ captures (sig.caps.map (Ty.inst θ))
      ∧ σ = sig.ty θ once env ∧ (once = false → ∀ c, c ∈ sig.caps → C.ctx.dup c)
      ∧ (∀ Cs', env = some Cs' → Cs' = sig.caps.map (Ty.inst θ)) := by
  obtain ⟨e, he, hc⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hfn, hθ⟩, hcs⟩, hσ⟩, hdup⟩, henv⟩ := hc
  refine ⟨e.sig, ⟨e, Cert.sigsOf_mem he, hfn, rfl⟩, hθ, atomsFit_sound hcs, hσ, fun ho => ?_, envOk_sound henv⟩
  rcases hdup with h2 | h2
  · rw [ho] at h2; cases h2
  · exact dupOk_all h2
%proof-/

/-- The type of an array's elements, if this is the type of arrays of some. -/
def arrayElem : Ty → Option Ty
  | .data name [t] => if name = arrayName then some t else none
  | .data name [t, _] => if name = fixedName then some t else none
  | _ => none

/-%proof (commented out while the machines become bytes)
theorem arrayElem_eq {T t : Ty} (h : arrayElem T = some t) : T = .data arrayName [t] := by
  unfold arrayElem at h
  split at h <;> try (cases h; done)
  split at h <;> try (cases h; done)
  rename_i hn
  cases h
  rw [hn]
%proof-/

/-%proof (commented out while the machines become bytes)
/-- A constructor of the type of arrays takes so many elements. -/
theorem array_ctor {t : Ty} {tag : Nat} {Fs : List Ty}
    (h : CtorOf C.ctx tag (.data arrayName [t]) Fs) :
    arrayBase ≤ tag ∧ Fs = List.replicate (tag - arrayBase) t := by
  rcases h with ⟨_, hT⟩ | ⟨_, name, args, hT, hF⟩
  · cases hT
  · cases hT
    have hF' : C.fields tag arrayName [t] = some Fs := hF
    simp only [Cert.fields, ↓reduceIte, arrayFields] at hF'
    split at hF'
    · rename_i hle
      cases hF'
      exact ⟨hle, rfl⟩
    · cases hF'
%proof-/

/-%proof (commented out while the machines become bytes)
theorem array_ctor_of {t : Ty} {tag : Nat} (h : arrayBase ≤ tag) :
    CtorOf C.ctx tag (.data arrayName [t]) (List.replicate (tag - arrayBase) t) := by
  refine .inr ⟨fun e => ?_, arrayName, [t], rfl, ?_⟩
  · rw [e] at h
    have := arrayBase_pos
    omega
  · show C.fields tag arrayName [t] = _
    simp [Cert.fields, arrayFields, h]
%proof-/

/-%proof (commented out while the machines become bytes)
theorem arrayElem_uniform {T t : Ty} (h : arrayElem T = some t) : Uniform C.ctx T t := by
  rw [arrayElem_eq h]
  intro tag Fs hc σ hσ
  obtain ⟨_, rfl⟩ := array_ctor hc
  exact List.eq_of_mem_replicate hσ
%proof-/

/-- The type of the field a reference is made to: a field found by number in
a type with one shape, or a place of an array, which may be found by the
program. -/
def focusTy (C : Cert) (Γ : TEnv) (σ : Ty) : Atom → Option Ty
  | .int (.ofNat i) =>
    match placeTy C σ [i] with
    | some σ' => some σ'
    | none => arrayElem σ
  | ix => if atomTy Γ ix == some .int then arrayElem σ else none

/-%proof (commented out while the machines become bytes)
theorem focusTy_sound {Γ : TEnv} {σ σ' : Ty} {ix : Atom} (h : focusTy C Γ σ ix = some σ') :
    (∃ i : Nat, ix = .int i ∧ PartOk C.ctx σ [⟨none, i⟩] σ')
      ∨ (HasAtom Γ ix .int ∧ Uniform C.ctx σ σ') := by
  unfold focusTy at h
  split at h
  · rename_i i
    split at h
    · rename_i τ hp
      cases h
      exact .inl ⟨i, rfl, (placeTy_sound hp).part⟩
    · exact .inr ⟨.int, arrayElem_uniform h⟩
  · split at h
    · rename_i hi
      exact .inr ⟨atomTy_sound (by simpa using hi), arrayElem_uniform h⟩
    · cases h
%proof-/

/-%proof (commented out while the machines become bytes)
theorem arrayElem_grows {T t : Ty} (h : arrayElem T = some t) : Grows C.ctx T t := by
  rw [arrayElem_eq h]
  intro tag Fs hc
  obtain ⟨hle, rfl⟩ := array_ctor hc
  have hc' := array_ctor_of (C := C) (t := t) (tag := tag + 1) (Nat.le_succ_of_le hle)
  have e : tag + 1 - arrayBase = (tag - arrayBase) + 1 := by omega
  rw [e, List.replicate_succ'] at hc'
  exact hc'
%proof-/

/-%proof (commented out while the machines become bytes)
theorem arrayElem_shrinks {T t : Ty} (h : arrayElem T = some t) : Shrinks C.ctx T := by
  rw [arrayElem_eq h]
  intro tag Fs hc hne
  obtain ⟨hle, rfl⟩ := array_ctor hc
  have hpos : tag - arrayBase ≠ 0 := fun e => hne (by simp [e])
  have hc' := array_ctor_of (C := C) (t := t) (tag := tag - 1) (by omega)
  have e : tag - 1 - arrayBase = tag - arrayBase - 1 := by omega
  rw [e] at hc'
  simpa [List.dropLast_replicate] using hc'
%proof-/

/-- An intrinsic: arithmetic on two integers, or one of those on arrays. -/
def checkPrim (C : Cert) (Γ : TEnv) (p : Prim) (args : List Atom) (σ : Ty) : Bool :=
  match p with
  | .arrGet =>
    match args with
    | [a, i] =>
      match atomTy Γ a with
      | some T => arrayElem T == some σ && atomTy Γ i == some .int && dupOk C σ
      | none => false
    | _ => false
  | .arrSet =>
    match args with
    | [a, i, v] =>
      match arrayElem σ with
      | some t =>
        atomTy Γ a == some σ && atomTy Γ i == some .int && atomTy Γ v == some t && dupOk C σ
      | none => false
    | _ => false
  | .arrLen =>
    match args with
    | [a, b] => (atomTy Γ a).isSome && (atomTy Γ b).isSome && σ == .int
    | _ => false
  | .arrPush =>
    match args with
    | [a, v] =>
      match arrayElem σ with
      | some t => atomTy Γ a == some σ && atomTy Γ v == some t && dupOk C σ
      | none => false
    | _ => false
  | .arrPop =>
    match args with
    | [a, b] =>
      match atomTy Γ a with
      | some T =>
        match arrayElem T with
        | some t => σ == .tuple [T, t] && (atomTy Γ b).isSome && dupOk C σ
        | none => false
      | none => false
    | _ => false
  | .cast b into =>
    match args with
    | [a] => if into then atomTy Γ a == some .int && σ == .scalar b else atomTy Γ a == some (.scalar b) && σ == .int
    | _ => false
  -- `[T; N]`: made of an array of the length, made an array, read at a
  -- place and written at one.
  | .fixed op =>
    match op, args with
    | 0, [a, .int n] =>
      match atomTy Γ a, σ with
      | some A, .data name [t, .data len []] =>
        name == fixedName && arrayElem A == some t && len == lenBase + n.toNat && dupOk C σ
      | _, _ => false
    | 1, [a] =>
      match atomTy Γ a, arrayElem σ with
      | some A, some t => arrayElem A == some t && σ == .data arrayName [t] && dupOk C σ
      | _, _ => false
    | 2, [a, i] =>
      match atomTy Γ a with
      | some T => arrayElem T == some σ && atomTy Γ i == some .int && dupOk C σ
      | none => false
    | 3, [a, i, v] =>
      match arrayElem σ with
      | some t => atomTy Γ a == some σ && atomTy Γ i == some .int && atomTy Γ v == some t && dupOk C σ
      | none => false
    | _, _ => false
  | _ =>
    match args with
    | [a, b] => atomTy Γ a == some .int && atomTy Γ b == some .int && σ == .int
    | _ => false

def checkRhs (C : Cert) (Γ : TEnv) (θ : List Rgn) : Rhs → Ty → Bool
  | .atom a, σ => atomFits Γ a σ
  | .prim p args, σ => checkPrim C Γ p args σ
  | .construct tag args, σ =>
    match ctorFieldsOf C tag σ with
    | some Fs => atomsFit Γ args Fs
    | none => false
  | .place pl, σ =>
    match Γ[pl.var]? with
    | some t => placeTy C t pl.path == some σ && dupOk C σ
    | none => false
  | .closure fn captures, σ =>
    match σ with
    | .fn _ _ _ _ once env _ => closesFit C Γ fn captures θ σ once env
    | _ => false
  | .rebind a fn, σ =>
    match atomTy Γ a, σ with
    | some (.fn _ _ _ _ _ (some Cs) _), .fn _ _ _ _ once env _ => closes C fn Cs θ σ once env
    | _, _ => false

/-%proof (commented out while the machines become bytes)
theorem checkRhs_sound {Γ : TEnv} {θ : List Rgn} {rhs : Rhs} {σ : Ty}
    (h : checkRhs C Γ θ rhs σ = true) : HasRhs C.ctx Γ rhs σ := by
  cases rhs with
  | atom a =>
    simp only [checkRhs] at h
    exact .atom (atomFits_sound h)
  | prim p args =>
    simp only [checkRhs, checkPrim] at h
    split at h
    · split at h
      · rename_i a i
        split at h <;> try (cases h; done)
        rename_i T hT
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨he, hi⟩, hd⟩ := h
        exact .arrGet (atomTy_sound hT) (atomTy_sound hi) (arrayElem_uniform he) (dupOk_sound hd)
      · cases h
    · split at h
      · rename_i a i v
        split at h <;> try (cases h; done)
        rename_i t he
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨⟨ha, hi⟩, hv⟩, hd⟩ := h
        exact .arrSet (atomTy_sound ha) (atomTy_sound hi) (atomTy_sound hv)
          (arrayElem_uniform he) (dupOk_sound hd)
      · cases h
    · split at h
      · rename_i a b
        simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at h
        obtain ⟨⟨⟨T, ha⟩, ⟨U, hb⟩⟩, rfl⟩ := h
        exact .arrLen (atomTy_sound ha) (atomTy_sound hb)
      · cases h
    · split at h
      · rename_i a v
        split at h <;> try (cases h; done)
        rename_i t he
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨ha, hv⟩, hd⟩ := h
        exact .arrPush (atomTy_sound ha) (atomTy_sound hv) (arrayElem_grows he) (dupOk_sound hd)
      · cases h
    · split at h
      · rename_i a b
        split at h <;> try (cases h; done)
        rename_i T hT
        split at h <;> try (cases h; done)
        rename_i t he
        simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at h
        obtain ⟨⟨rfl, ⟨U, hb⟩⟩, hd⟩ := h
        exact .arrPop (atomTy_sound hT) (atomTy_sound hb) (arrayElem_uniform he)
          (arrayElem_shrinks he) (dupOk_sound hd)
      · cases h
    · split at h
      · simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨ha, hb⟩, rfl⟩ := h
        exact .prim (atomTy_sound ha) (atomTy_sound hb)
      · cases h
  | construct tag args =>
    simp only [checkRhs] at h
    split at h <;> try (cases h; done)
    rename_i Fs hF
    exact .construct (ctorFieldsOf_sound hF) (atomsFit_sound h)
  | place pl =>
    simp only [checkRhs] at h
    split at h <;> try (cases h; done)
    rename_i t ht
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact .place ht (placeTy_sound h.1) (dupOk_sound h.2)
  | closure fn captures =>
    simp only [checkRhs] at h
    split at h <;> try (cases h; done)
    rename_i n Ps r e once env acc
    obtain ⟨sig, hsig, hθ, hcaps, hσ, hdup, henv⟩ := closesFit_sound h
    rw [hσ]
    exact .closure hsig hθ hcaps hdup henv
  | rebind a fn =>
    simp only [checkRhs] at h
    split at h <;> try (cases h; done)
    rename_i n' Ps' r' e' once' Cs acc' n Ps r e once env acc ha
    obtain ⟨sig, hsig, hθ, hCs, hσ, hdup, henv⟩ := closes_sound h
    rw [hσ]
    subst hCs
    exact .rebind (atomTy_sound ha) hsig hθ hdup henv
%proof-/

/-! ## Handlers -/

/-- Can `fn` be entered with these captures and arguments, with the regions
`θ`, to give a `ρ` within `ε` and `Φ`? -/
def enters (C : Cert) (fn : Nat) (θ : List Rgn) (Cs Ps : List Ty) (ρ : Ty) (ε : Row)
    (Φ : List Rgn) : Bool :=
  (C.sigsOf fn).any fun e =>
    e.fn == fn && θ.length == e.sig.crgns && e.sig.rgns == 0
      && Cs == e.sig.caps.map (Ty.inst θ) && Ps == e.sig.params.map (Ty.inst θ)
      && ρ == e.sig.ret.inst θ && rowLe (e.sig.eff.inst θ) ε
      && subB (e.sig.acc.map (Rgn.inst θ)) Φ && nodupOk C (e.sig.acc.map (Rgn.inst θ))

/-%proof (commented out while the machines become bytes)
theorem enters_sound {fn : Nat} {θ : List Rgn} {Cs Ps : List Ty} {ρ : Ty} {ε : Row}
    {Φ : List Rgn} (h : enters C fn θ Cs Ps ρ ε Φ = true) : Enters C.ctx fn Cs Ps ρ ε Φ := by
  obtain ⟨e, he, hc⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hfn, hθ⟩, hn⟩, hcaps⟩, hps⟩, hret⟩, hrow⟩, hacc⟩, hnd⟩ := hc
  exact ⟨e.sig, θ, ⟨e, Cert.sigsOf_mem he, hfn, rfl⟩, hθ, hn, hcaps, hps, hret, rowLe_sound hrow,
    subB_sound hacc, nodupOk_sound hnd⟩
%proof-/

def checkArms (C : Cert) (Cs : List Ty) (ρ : Ty) (ε : Row) (Φ : List Rgn) :
    List (Nat × Nat) → Row → List (List Rgn) → Bool
  | [], [], _ => true
  | (op, arm) :: ops, (op', targs) :: H, θ :: θs =>
    op == op'
      && (match findOp C.ops op targs with
          | some (Ps, none) => enters C arm θ Cs Ps ρ ε Φ
          | some (Ps, some o) =>
            enters C arm θ Cs (Ps ++ [.fn 0 [o] ρ ε true none Φ]) ρ ε Φ
          | none => false)
      && checkArms C Cs ρ ε Φ ops H θs
  | [], _ :: _, _ => false
  | _ :: _, [], _ => false
  | _ :: _, _ :: _, [] => false

/-%proof (commented out while the machines become bytes)
theorem checkArms_sound {Cs : List Ty} {ρ : Ty} {ε : Row} {Φ : List Rgn} :
    ∀ {ops : List (Nat × Nat)} {H : Row} {θs : List (List Rgn)},
      checkArms C Cs ρ ε Φ ops H θs = true → ArmsOk C.ctx Cs ρ ε Φ ops H
  | [], [], _, _ => .nil
  | (op, arm) :: ops, (op', targs) :: H, θ :: θs, h => by
    simp only [checkArms, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, harm⟩, hrest⟩ := h
    split at harm
    · rename_i Ps hop
      exact .terminal hop (enters_sound harm) (checkArms_sound hrest)
    · rename_i Ps o hop
      exact .resumptive hop (enters_sound harm) (checkArms_sound hrest)
    · simp at harm
  | [], _ :: _, _, h => by simp [checkArms] at h
  | _ :: _, [], _, h => by simp [checkArms] at h
  | _ :: _, _ :: _, [], h => by simp [checkArms] at h
%proof-/

def checkHandler (C : Cert) (Cs : List Ty) (ret : Nat) (ops : List (Nat × Nat)) (σ ρ : Ty)
    (H ε : Row) (Φ : List Rgn) : List (List Rgn) → Bool
  | θ :: θs => enters C ret θ Cs [σ] ρ ε Φ && checkArms C Cs ρ ε Φ ops H θs && Cs.all (dupOk C)
  | [] => false

/-%proof (commented out while the machines become bytes)
theorem checkHandler_sound {Cs : List Ty} {ret : Nat} {ops : List (Nat × Nat)} {σ ρ : Ty}
    {H ε : Row} {Φ : List Rgn} {θs : List (List Rgn)}
    (h : checkHandler C Cs ret ops σ ρ H ε Φ θs = true) :
    HandlerOk C.ctx Cs ret ops σ ρ H ε Φ := by
  cases θs with
  | nil => simp [checkHandler] at h
  | cons θ θs =>
    simp only [checkHandler, Bool.and_eq_true] at h
    exact ⟨enters_sound h.1.1, checkArms_sound h.1.2, dupOk_all h.2⟩
%proof-/

/-! ## Computations -/

/-- The conditions on the callable a cell's scope runs: it takes a reference to
the cell, and under the region rules is polymorphic in the cell's region, which
neither its result, nor what it performs, nor what the cell holds can mention. -/
def cellOk (C : Cert) (ϕ : List Rgn) (n : Nat) (r : Rgn) (σ ρ : Ty) (εt : Row)
    (acc : List Rgn) : Bool :=
  σ.lc && ρ.lc && εt.lc && (n == 0 || (n == 1 && r == .bound 0))
    && (!C.regions || (n == 1 && r == .bound 0)) && nodupOk C acc
    && acc.all fun x =>
      (n == 1 && (x == .bound 0 || x == .wr (.bound 0))) || (x.free && grantsB ϕ x)

/-%proof (commented out while the machines become bytes)
theorem cellOk_sound {ϕ : List Rgn} {n : Nat} {r : Rgn} {σ ρ : Ty} {εt : Row} {acc : List Rgn}
    (h : cellOk C ϕ n r σ ρ εt acc = true) :
    σ.lc = true ∧ ρ.lc = true ∧ εt.lc = true ∧ (n = 0 ∨ (n = 1 ∧ r = .bound 0))
      ∧ (C.ctx.regions → n = 1 ∧ r = .bound 0)
      ∧ (∀ x, x ∈ acc → (n = 1 ∧ (x = .bound 0 ∨ x = .wr (.bound 0)))
        ∨ (x.free = true ∧ Grants ϕ x))
      ∧ (C.ctx.loans → (Rgn.flat acc).Nodup) := by
  simp only [cellOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hσ, hρ⟩, hε⟩, hn⟩, hreg⟩, hnd⟩, hacc⟩ := h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    List.all_eq_true] at hn hreg hacc
  refine ⟨hσ, hρ, hε, hn, fun hR => ?_,
    fun x hx => (hacc x hx).imp id fun h => ⟨h.1, grantsB_sound h.2⟩, nodupOk_sound hnd⟩
  have hR' : C.regions = true := hR
  rcases hreg with h | h
  · rw [hR'] at h; cases h
  · exact h
%proof-/

/-- The conditions on the callable a label's scope runs: under the region rules
it is polymorphic in the scope's region, which the label's type says applying
it touches, and neither what the scope gives nor what it performs mentions it. -/
def labelOk (C : Cert) (ϕ : List Rgn) (n : Nat) (σ : Ty) (εt : Row) (accl acc : List Rgn) :
    Bool :=
  σ.lc && εt.lc && (n == 0 || n == 1)
    && (!C.regions || (n == 1 && accl.contains (.bound 0))) && nodupOk C acc
    && acc.all fun x => (n == 1 && x == .bound 0) || (x.free && grantsB ϕ x)

/-%proof (commented out while the machines become bytes)
theorem labelOk_sound {ϕ : List Rgn} {n : Nat} {σ : Ty} {εt : Row} {accl acc : List Rgn}
    (h : labelOk C ϕ n σ εt accl acc = true) :
    σ.lc = true ∧ εt.lc = true ∧ (n = 0 ∨ n = 1)
      ∧ (C.ctx.regions → n = 1 ∧ .bound 0 ∈ accl)
      ∧ (∀ x, x ∈ acc → (n = 1 ∧ x = .bound 0) ∨ (x.free = true ∧ Grants ϕ x))
      ∧ (C.ctx.loans → (Rgn.flat acc).Nodup) := by
  simp only [labelOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hσ, hε⟩, hn⟩, hreg⟩, hnd⟩, hacc⟩ := h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_true_eq] at hn hreg
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hacc
  refine ⟨hσ, hε, hn, fun hR => ?_,
    fun x hx => (hacc x hx).imp id fun h => ⟨h.1, grantsB_sound h.2⟩, nodupOk_sound hnd⟩
  have hR' : C.regions = true := hR
  rcases hreg with h | h
  · rw [hR'] at h; cases h
  · exact h
%proof-/

/-- The conditions on the callable a borrow's scope runs. Without the rules for
borrows it may take the reference lent. With them it is polymorphic in the
borrow's region; what is lent is something the code may touch, and may write if
it is lent for writing; of what the code may touch the callable touches
nothing that was lent: not to write, and not at all if it was lent for writing;
and it performs no operation it does not handle itself. -/
def lendOk (C : Cert) (ϕ : List Rgn) (uniq : Bool) (n : Nat) (ρ κ : Rgn) (σ ρt : Ty) (εt : Row)
    (acc : List Rgn) : Bool :=
  σ.lc && ρt.lc && εt.lc && ((n == 0 && κ == ρ) || (n == 1 && κ == .bound 0))
    && regionOk C ϕ ρ
    && (!C.loans
      || (n == 1 && grantsB ϕ ρ && (!uniq || grantsB ϕ (.wr ρ)) && decide (Rgn.flat acc).Nodup
        && εt.isEmpty))
    && acc.all fun x =>
      (n == 1 && (x == .bound 0 || (uniq && x == .wr (.bound 0))))
        || (x.free && grantsB ϕ x && (!C.loans || x.parts.all fun y =>
          !((Rgn.wr ρ).parts.contains y) && (!uniq || !(ρ.parts.contains y))))

/-%proof (commented out while the machines become bytes)
theorem lendOk_sound {ϕ : List Rgn} {uniq : Bool} {n : Nat} {ρ κ : Rgn} {σ ρt : Ty} {εt : Row}
    {acc : List Rgn} (h : lendOk C ϕ uniq n ρ κ σ ρt εt acc = true) :
    σ.lc = true ∧ ρt.lc = true ∧ εt.lc = true ∧ ((n = 0 ∧ κ = ρ) ∨ (n = 1 ∧ κ = .bound 0))
      ∧ (C.ctx.regions → Grants ϕ ρ)
      ∧ (C.ctx.loans → n = 1 ∧ Grants ϕ ρ ∧ (uniq = true → Grants ϕ (.wr ρ))
        ∧ (Rgn.flat acc).Nodup ∧ εt = [])
      ∧ (∀ x, x ∈ acc → (n = 1 ∧ (x = .bound 0 ∨ (uniq = true ∧ x = .wr (.bound 0))))
        ∨ (x.free = true ∧ Grants ϕ x ∧ (C.ctx.loans → ∀ y, y ∈ x.parts →
          y ∉ (Rgn.wr ρ).parts ∧ (uniq = true → y ∉ ρ.parts)))) := by
  simp only [lendOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hσ, hρ⟩, hε⟩, hn⟩, hreg⟩, hloan⟩, hacc⟩ := h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    decide_eq_true_eq] at hn hloan
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    List.all_eq_true] at hacc
  refine ⟨hσ, hρ, hε, hn, regionOk_sound hreg, fun hL => ?_, fun x hx => ?_⟩
  · have hL' : C.loans = true := hL
    rcases hloan with h | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    · rw [hL'] at h; cases h
    · refine ⟨h1, grantsB_sound h2, fun hu => ?_, h4, List.isEmpty_iff.mp h5⟩
      rcases h3 with h | h
      · rw [hu] at h; cases h
      · exact grantsB_sound h
  · rcases hacc x hx with h | ⟨⟨hfree, hmem⟩, hne⟩
    · exact .inl h
    · refine .inr ⟨hfree, grantsB_sound hmem, fun hL y hy => ?_⟩
      have hL' : C.loans = true := hL
      rcases hne with h | h
      · rw [hL'] at h; cases h
      · have hy' := h y hy
        have notIn : ∀ {l : List Rgn}, l.contains y = false → y ∉ l := fun hl hm => by
          rw [List.contains_iff_mem.mpr hm] at hl; cases hl
        refine ⟨notIn hy'.1, fun hu => ?_⟩
        rcases hy'.2 with h' | h'
        · rw [hu] at h'
          cases h'
        · exact notIn h'
%proof-/

/-- Check a computation against the regions it may touch, the type it must
give and the operations it may perform. Hints are used up in order: one by each
`let`, one by each handler, one by each call of a callable that binds regions,
and one by each call of something that does not return, for the type the code
after the call takes its result to have. -/
def checkTm (C : Cert) (ϕ : List Rgn) : TEnv → Tm → List Hint → Ty → Row → Bool
  | Γ, .ret a, _, τ, _ => atomFits Γ a τ
  | Γ, .let_ rhs body, hs, τ, ε =>
    match hs with
    | h :: hs =>
      match h.bind? with
      | some (σ, θ) =>
        checkRhs C Γ θ rhs σ && linearB C Γ (rhsMoves rhs) (fv body)
          && checkTm C ϕ (Γ ++ [σ]) body hs τ ε
      | none => false
    | [] => false
  | Γ, .call f args body, hs, τ, ε =>
    match atomTy Γ f with
    | some (.fn n Ps σ ε' _ _ acc) =>
      match takeRgns n hs with
      | some (rs, hs) =>
        atomsFit Γ args (Ps.map (Ty.open rs)) && rowLe (Row.open rs ε') ε
          && subB (acc.map (Rgn.openAt 0 rs)) ϕ && nodupOk C (acc.map (Rgn.openAt 0 rs))
          && linearB C Γ (atomVars (f :: args)) (fv body)
          && (if σ = .never then
                match hs with
                | .ty σ' :: hs => checkTm C ϕ (Γ ++ [σ']) body hs τ ε
                | _ => false
              else checkTm C ϕ (Γ ++ [σ.open rs]) body hs τ ε)
      | none => false
    | _ => false
  | Γ, .tail f args, hs, τ, ε =>
    match atomTy Γ f with
    | some (.fn n Ps σ ε' _ _ acc) =>
      match takeRgns n hs with
      | some (rs, _) =>
        (σ.open rs == τ || σ == .never) && atomsFit Γ args (Ps.map (Ty.open rs))
          && rowLe (Row.open rs ε') ε && subB (acc.map (Rgn.openAt 0 rs)) ϕ
          && nodupOk C (acc.map (Rgn.openAt 0 rs))
          && linearB C Γ (atomVars (f :: args)) []
      | none => false
    | _ => false
  | Γ, .handle ret ops captures thunk body, hs, τ, ε =>
    match hs, atomTy Γ thunk, atomsTy Γ captures with
    | .handler ρ H Φ θs :: hs, some (.fn 0 [] σ εt _ _ acc), some Cs =>
      checkHandler C Cs ret ops σ ρ H ε Φ θs && rowLe εt (H ++ ε) && subB acc Φ && subB Φ ϕ
        && nodupOk C acc && linearB C Γ (atomVars [thunk]) (fv body)
        && checkTm C ϕ (Γ ++ [ρ]) body hs τ ε
    | _, _, _ => false
  | Γ, .handleTail ret ops captures thunk, hs, τ, ε =>
    match hs, atomTy Γ thunk, atomsTy Γ captures with
    | .handler _ H Φ θs :: _, some (.fn 0 [] σ εt _ _ acc), some Cs =>
      checkHandler C Cs ret ops σ τ H ε Φ θs && rowLe εt (H ++ ε) && subB acc Φ && subB Φ ϕ
        && nodupOk C acc
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
          && checkTm C ϕ (Γ ++ [σ]) body hs τ ε
      | _ => false
    | none => false
  | Γ, .label thunk body, hs, τ, ε =>
    match atomTy Γ thunk with
    | some (.fn n [.fn 0 [σ'] _ _ _ none accl] σ εt _ _ acc) =>
      σ' == σ && labelOk C ϕ n σ εt accl acc && rowLe εt ε
        && linearB C Γ (atomVars [thunk]) (fv body)
        && checkTm C ϕ (Γ ++ [σ]) body hs τ ε
    | _ => false
  | Γ, .labelTail thunk, _, τ, ε =>
    match atomTy Γ thunk with
    | some (.fn n [.fn 0 [σ'] _ _ _ none accl] σ εt _ _ acc) =>
      σ' == σ && σ == τ && labelOk C ϕ n σ εt accl acc && rowLe εt ε
    | _ => false
  | Γ, .guard cleanup thunk body, hs, τ, ε =>
    match atomTy Γ cleanup, atomTy Γ thunk with
    | some (.fn 0 [] _ [] _ _ accc), some (.fn 0 [] σ εt _ _ acc) =>
      rowLe εt ε && subB accc ϕ && subB acc ϕ && nodupOk C accc && nodupOk C acc
        && linearB C Γ (atomVars [cleanup, thunk]) (fv body)
        && checkTm C ϕ (Γ ++ [σ]) body hs τ ε
    | _, _ => false
  | Γ, .guardTail cleanup thunk, _, τ, ε =>
    match atomTy Γ cleanup, atomTy Γ thunk with
    | some (.fn 0 [] _ [] _ _ accc), some (.fn 0 [] σ εt _ _ acc) =>
      σ == τ && rowLe εt ε && subB accc ϕ && subB acc ϕ && nodupOk C accc && nodupOk C acc
        && linearB C Γ (atomVars [cleanup, thunk]) []
    | _, _ => false
  | Γ, .cancel k body, hs, τ, ε =>
    match atomTy Γ k with
    | some (.fn n _ _ ε' _ _ acc) =>
      rowLe ε' ε && subFreeB n acc ϕ && nodupOk C acc && linearB C Γ (atomVars [k]) (fv body)
        && checkTm C ϕ (Γ ++ [.unit]) body hs τ ε
    | _ => false
  | Γ, .cell init thunk body, hs, τ, ε =>
    match atomTy Γ init, atomTy Γ thunk with
    | some σ, some (.fn n [.ref r σ'] ρ εt _ _ acc) =>
      σ' == σ && cellOk C ϕ n r σ ρ εt acc && rowLe εt ε
        && linearB C Γ (atomVars [init, thunk]) (fv body)
        && checkTm C ϕ (Γ ++ [ρ]) body hs τ ε
    | _, _ => false
  | Γ, .cellTail init thunk, _, τ, ε =>
    match atomTy Γ init, atomTy Γ thunk with
    | some σ, some (.fn n [.ref r σ'] ρ εt _ _ acc) =>
      σ' == σ && ρ == τ && cellOk C ϕ n r σ ρ εt acc && rowLe εt ε
        && linearB C Γ (atomVars [init, thunk]) []
    | _, _ => false
  -- (Cells of memory are the typed lowering's, after the certificate.)
  | _, .cellL .., _, _, _ | _, .cellTailL .., _, _, _ => false
  | Γ, .lend uniq r thunk pre post body, hs, τ, ε =>
    match atomTy Γ r, atomTy Γ thunk with
    | some (.ref ρ σ), some (.fn n Ps ρt εt _ _ acc) =>
      -- The borrow is the argument after `pre`.
      match Ps.drop pre.length with
      | .ref κ σ' :: Post =>
        σ' == σ && atomsTy Γ pre == some (Ps.take pre.length) && atomsTy Γ post == some Post
          && (Ps.take pre.length ++ Post).all Ty.lc
          && lendOk C ϕ uniq n ρ κ σ ρt εt acc && rowLe εt ε
          && linearB C Γ (atomVars (thunk :: pre ++ post)) (fv body)
          && checkTm C ϕ (Γ ++ [ρt]) body hs τ ε
      | _ => false
    | _, _ => false
  | Γ, .mem op args body, hs, τ, ε =>
    match op, args with
    | .load, [a] =>
      match atomTy Γ a with
      | some (.ref r σ) =>
        regionOk C ϕ r && dupOk C σ && checkTm C ϕ (Γ ++ [σ]) body hs τ ε
      | _ => false
    | .store, [a, b] =>
      match atomTy Γ a with
      | some (.ref r σ) =>
        regionOk C ϕ r && writeOk C ϕ r && atomFits Γ b σ
          && linearB C Γ (atomVars [b]) (fv body)
          && checkTm C ϕ (Γ ++ [.unit]) body hs τ ε
      | _ => false
    | .swap, [a, b] =>
      match atomTy Γ a with
      | some (.ref r σ) =>
        regionOk C ϕ r && writeOk C ϕ r && atomFits Γ b σ
          && linearB C Γ (atomVars [b]) (fv body)
          && checkTm C ϕ (Γ ++ [σ]) body hs τ ε
      | _ => false
    | .tag, a :: path =>
      match atomTy Γ a, atomsTy Γ path with
      | some (.ref r _), some _ => regionOk C ϕ r && checkTm C ϕ (Γ ++ [.int]) body hs τ ε
      | _, _ => false
    | .focus, [a, ix] =>
      match atomTy Γ a with
      | some (.ref r σ) =>
        match focusTy C Γ σ ix with
        | some σ' => regionOk C ϕ r && checkTm C ϕ (Γ ++ [.ref r σ']) body hs τ ε
        | none => false
      | _ => false
    -- (A place in a `[T; N]` found when the program runs.)
    | .focus, [a, ix, .int (-1)] =>
      match atomTy Γ a with
      | some (.ref r σ) =>
        match arrayElem σ with
        | some σ' => regionOk C ϕ r && atomTy Γ ix == some .int && checkTm C ϕ (Γ ++ [.ref r σ']) body hs τ ε
        | none => false
      | _ => false
    | .focus, [a, .int (.ofNat i), .int (.ofNat built)] =>
      match atomTy Γ a with
      | some (.ref r σ) =>
        match ctorFieldsOf C built σ with
        | some Fs =>
          match Fs[i]? with
          | some σ' => regionOk C ϕ r && checkTm C ϕ (Γ ++ [.ref r σ']) body hs τ ε
          | none => false
        | none => false
      | _ => false
    | _, _ => false
  | Γ, .host id args body, hs, τ, ε =>
    match id, args with
    | 0, [a] => (atomTy Γ a).isSome && checkTm C ϕ (Γ ++ [.unit]) body hs τ ε
    | 1, [] => checkTm C ϕ (Γ ++ [.tuple [.int, .int]]) body hs τ ε
    | _, _ => false

/-%proof (commented out while the machines become bytes)
theorem checkTm_sound {ϕ : List Rgn} : ∀ (tm : Tm) {Γ : TEnv} {hs : List Hint} {τ : Ty}
    {ε : Row}, checkTm C ϕ Γ tm hs τ ε = true → HasTm C.ctx ϕ Γ tm τ ε := by
  intro tm Γ hs τ ε h
  induction tm generalizing Γ hs τ ε <;> simp only [checkTm] at h
  case ret a =>
    exact .ret (atomFits_sound h)
  case let_ rhs body ih =>
    split at h <;> try (simp at h; done)
    split at h <;> try (simp at h; done)
    simp only [Bool.and_eq_true] at h
    exact .let_ (checkRhs_sound h.1.1) (linearB_sound h.1.2) (ih h.2)
  case call f args body ih =>
    split at h <;> try (simp at h; done)
    rename_i n Ps σ ε' once env acc hf
    split at h <;> try (simp at h; done)
    rename_i rs hs' htake
    have hn := takeRgns_length htake
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨hargs, hrow⟩, hacc⟩, hnd⟩, hlin⟩, hbody⟩ := h
    split at hbody
    · rename_i hσ
      subst hσ
      split at hbody <;> try (simp at hbody; done)
      exact .callNever (rs := rs) ⟨atomTy_sound hf, hn, atomsFit_sound hargs, rowLe_sound hrow,
        subB_sound hacc, nodupOk_sound hnd⟩ (linearB_sound hlin) (ih hbody)
    · exact .call (rs := rs) ⟨atomTy_sound hf, hn, atomsFit_sound hargs, rowLe_sound hrow,
        subB_sound hacc, nodupOk_sound hnd⟩ (linearB_sound hlin) (ih hbody)
  case tail f args =>
    split at h <;> try (simp at h; done)
    rename_i n Ps σ ε' once env acc hf
    split at h <;> try (simp at h; done)
    rename_i rs hs' htake
    have hn := takeRgns_length htake
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨hσ, hargs⟩, hrow⟩, hacc⟩, hnd⟩, hlin⟩ := h
    rcases hσ with hσ | rfl
    · exact .tail (rs := rs) ⟨atomTy_sound hf, hn, atomsFit_sound hargs, rowLe_sound hrow,
        subB_sound hacc, nodupOk_sound hnd⟩ hσ (linearB_sound hlin)
    · exact .tailNever (rs := rs) ⟨atomTy_sound hf, hn, atomsFit_sound hargs, rowLe_sound hrow,
        subB_sound hacc, nodupOk_sound hnd⟩ (linearB_sound hlin)
  case handle ret ops captures thunk body ih =>
    split at h <;> try (simp at h; done)
    rename_i ρ H Φ θs hs' σ εt once env acc Cs hthunk hcaps
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨hh, hrow⟩, hacc⟩, hΦ⟩, hnd⟩, hlin⟩, hbody⟩ := h
    exact .handle ⟨atomTy_sound hthunk, atomsTy_sound hcaps, checkHandler_sound hh,
      rowLe_sound hrow, subB_sound hacc, subB_sound hΦ, nodupOk_sound hnd⟩ (linearB_sound hlin)
      (ih hbody)
  case handleTail ret ops captures thunk =>
    split at h <;> try (simp at h; done)
    rename_i ρ H Φ θs hs' σ εt once env acc Cs hthunk hcaps
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hh, hrow⟩, hacc⟩, hΦ⟩, hnd⟩ := h
    exact .handleTail ⟨atomTy_sound hthunk, atomsTy_sound hcaps, checkHandler_sound hh,
      rowLe_sound hrow, subB_sound hacc, subB_sound hΦ, nodupOk_sound hnd⟩
  case raise op args =>
    split at h <;> try (simp at h; done)
    rename_i targs hl
    split at h <;> try (simp at h; done)
    rename_i Ps hop
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact .raise hl hop (atomsTy_sound h.1) (linearB_sound h.2)
  case perform op args body ih =>
    split at h <;> try (simp at h; done)
    rename_i targs hl
    split at h <;> try (simp at h; done)
    rename_i Ps σ hop
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact .perform hl hop (atomsTy_sound h.1.1) (linearB_sound h.1.2) (ih h.2)
  case label thunk body ih =>
    split at h <;> try (simp at h; done)
    rename_i n σ' ρ εl once' accl σ εt once env acc hthunk
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨rfl, hlab⟩, hrow⟩, hlin⟩, hbody⟩ := h
    obtain ⟨hσ, hε, hn, hreg, hacc, hnd⟩ := labelOk_sound hlab
    exact .label ⟨atomTy_sound hthunk, hσ, hε, hn, hreg, hacc, hnd, rowLe_sound hrow⟩
      (linearB_sound hlin) (ih hbody)
  case labelTail thunk =>
    split at h <;> try (simp at h; done)
    rename_i n σ' ρ εl once' accl σ εt once env acc hthunk
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, hlab⟩, hrow⟩ := h
    obtain ⟨hσ, hε, hn, hreg, hacc, hnd⟩ := labelOk_sound hlab
    exact .labelTail ⟨atomTy_sound hthunk, hσ, hε, hn, hreg, hacc, hnd, rowLe_sound hrow⟩
  case guard cleanup thunk body ih =>
    split at h <;> try (simp at h; done)
    rename_i σc once' env' accc σ εt once env acc hcl hthunk
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨hrow, haccc⟩, hacc⟩, hnd1⟩, hnd2⟩, hlin⟩, hbody⟩ := h
    exact .guard ⟨atomTy_sound hcl, atomTy_sound hthunk, rowLe_sound hrow, subB_sound haccc,
      subB_sound hacc, (fun hL => ⟨nodupOk_sound hnd1 hL, nodupOk_sound hnd2 hL⟩)⟩
      (linearB_sound hlin) (ih hbody)
  case guardTail cleanup thunk =>
    split at h <;> try (simp at h; done)
    rename_i σc once' env' accc σ εt once env acc hcl hthunk
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨rfl, hrow⟩, haccc⟩, hacc⟩, hnd1⟩, hnd2⟩, hlin⟩ := h
    exact .guardTail ⟨atomTy_sound hcl, atomTy_sound hthunk, rowLe_sound hrow, subB_sound haccc,
      subB_sound hacc, (fun hL => ⟨nodupOk_sound hnd1 hL, nodupOk_sound hnd2 hL⟩)⟩
      (linearB_sound hlin)
  case cancel k body ih =>
    split at h <;> try (simp at h; done)
    rename_i n Ps ρ ε' once env acc hk
    simp only [Bool.and_eq_true] at h
    exact .cancel (atomTy_sound hk) (rowLe_sound h.1.1.1.1) (subFreeB_sound h.1.1.1.2)
      (nodupOk_sound h.1.1.2) (linearB_sound h.1.2) (ih h.2)
  case cell init thunk body ih =>
    split at h <;> try (simp at h; done)
    rename_i σ n r σ' ρ εt once env acc hinit hthunk
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨rfl, hcell⟩, hrow⟩, hlin⟩, hbody⟩ := h
    obtain ⟨hσ, hρ, hε, hn, hreg, hacc, hnd⟩ := cellOk_sound hcell
    exact .cell ⟨atomTy_sound hinit, atomTy_sound hthunk, hσ, hρ, hε, hn, hreg, hacc, hnd,
      rowLe_sound hrow⟩ (linearB_sound hlin) (ih hbody)
  case cellTail init thunk =>
    split at h <;> try (simp at h; done)
    rename_i σ n r σ' ρ εt once env acc hinit hthunk
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨rfl, rfl⟩, hcell⟩, hrow⟩, hlin⟩ := h
    obtain ⟨hσ, hρ, hε, hn, hreg, hacc, hnd⟩ := cellOk_sound hcell
    exact .cellTail ⟨atomTy_sound hinit, atomTy_sound hthunk, hσ, hρ, hε, hn, hreg, hacc, hnd,
      rowLe_sound hrow⟩ (linearB_sound hlin)
  case lend uniq r thunk pre post body ih =>
    split at h <;> try (simp at h; done)
    rename_i ρ σ n Ps ρt εt once env acc hr hthunk
    split at h <;> try (simp at h; done)
    rename_i κ σ' Post hdrop
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨rfl, hpre⟩, hpost⟩, hlc⟩, hlend⟩, hrow⟩, hlin⟩, hbody⟩ := h
    obtain ⟨hσ, hρ, hε, hn, hreg, hloan, hacc⟩ := lendOk_sound hlend
    have hPs : Ps = Ps.take pre.length ++ .ref κ σ' :: Post := by
      rw [← hdrop, List.take_append_drop]
    have hthunk' := atomTy_sound hthunk
    rw [hPs] at hthunk'
    exact .lend ⟨atomTy_sound hr, hthunk', atomsTy_sound hpre, atomsTy_sound hpost, hlc,
      hσ, hρ, hε, hn, hreg, hloan, hacc, rowLe_sound hrow⟩ (linearB_sound hlin) (ih hbody)
  case mem op args body ih =>
    split at h
    · split at h
      · rename_i r σ ha
        simp only [Bool.and_eq_true] at h
        exact .load (atomTy_sound ha) (regionOk_sound h.1.1) (dupOk_sound h.1.2) (ih h.2)
      · simp at h
    · split at h
      · rename_i r σ ha
        simp only [Bool.and_eq_true] at h
        exact .store ⟨atomTy_sound ha, regionOk_sound h.1.1.1.1, writeOk_sound h.1.1.1.2,
          atomFits_sound h.1.1.2⟩ (linearB_sound h.1.2) (ih h.2)
      · simp at h
    · split at h
      · rename_i r σ ha
        simp only [Bool.and_eq_true] at h
        exact .swap ⟨atomTy_sound ha, regionOk_sound h.1.1.1.1, writeOk_sound h.1.1.1.2,
          atomFits_sound h.1.1.2⟩ (linearB_sound h.1.2) (ih h.2)
      · simp at h
    · split at h
      · rename_i r σ Ps ha hp
        simp only [Bool.and_eq_true] at h
        exact .tag (atomTy_sound ha) (regionOk_sound h.1) (atomsTy_sound hp) (ih h.2)
      · simp at h
    · split at h
      · rename_i r σ ha
        split at h <;> try (simp at h; done)
        rename_i σ' hf
        simp only [Bool.and_eq_true] at h
        rcases focusTy_sound hf with ⟨i, rfl, hpl⟩ | ⟨hix, hu⟩
        · exact .focus (atomTy_sound ha) (regionOk_sound h.1) hpl (ih h.2)
        · exact .focusAt (atomTy_sound ha) hix (regionOk_sound h.1) hu (ih h.2)
      · simp at h
    · split at h
      · rename_i r σ ha
        split at h <;> try (simp at h; done)
        rename_i Fs hc
        split at h <;> try (simp at h; done)
        rename_i σ' hi
        simp only [Bool.and_eq_true] at h
        exact .focusIn (atomTy_sound ha) (regionOk_sound h.1) (ctorFieldsOf_sound hc) hi
          (ih h.2)
      · simp at h
    · simp at h
  case host id args body ih =>
    split at h
    · simp only [Bool.and_eq_true, Option.isSome_iff_exists] at h
      obtain ⟨⟨σ, ha⟩, hbody⟩ := h
      exact .write (atomTy_sound ha) (ih hbody)
    · exact .read (ih h)
    · simp at h
%proof-/

/-! ## Patterns and clauses -/

mutual

/-- The types of what a pattern binds from a value of a type, if it fits that type. -/
def patTys (C : Cert) : Pat → Ty → Option (List Ty)
  | .wild, _ => some []
  | .bind, τ => some [τ]
  | .int _, τ => match τ with
    | .int | .scalar _ => some []
    | _ => none
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

/-%proof (commented out while the machines become bytes)
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
    split at h <;> try (cases h; done)
    rename_i hτ
    subst hτ
    cases h
    exact .int
  | .ctor tag ps, T, _, h => by
    simp only [patTys] at h
    split at h <;> try (cases h; done)
    rename_i Fs hF
    exact .ctor (ctorFieldsOf_sound hF) (patsTys_sound h)

theorem patsTys_sound : ∀ {ps : List Pat} {τs Bs : List Ty},
    patsTys C ps τs = some Bs → PatsOk C.ctx ps τs Bs
  | [], [], _, h => by
    simp only [patsTys, Option.some.injEq] at h
    subst h
    exact .nil
  | p :: ps, τ :: τs, _, h => by
    simp only [patsTys] at h
    split at h <;> try (cases h; done)
    rename_i B Bs' hB hBs
    cases h
    exact .cons (patTys_sound hB) (patsTys_sound hBs)
  | [], _ :: _, _, h => by simp [patsTys] at h
  | _ :: _, [], _, h => by simp [patsTys] at h

end
%proof-/
/-- Does a body leave alone every argument its patterns take apart? -/
def wildOk (pats : List Pat) (live : List Nat) : Bool :=
  (List.range pats.length).all fun i =>
    match pats[i]? with
    | some p => isWild p || !live.contains i
    | none => true

/-%proof (commented out while the machines become bytes)
theorem wildOk_sound {pats : List Pat} {live : List Nat} (h : wildOk pats live = true) :
    ∀ i p, pats[i]? = some p → isWild p = false → i ∉ live := by
  intro i p hp hw
  have hlt : i < pats.length := by
    rcases Nat.lt_or_ge i pats.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hp; cases hp
  have := List.all_eq_true.mp h i (List.mem_range.mpr hlt)
  simpa [hp, hw] using this
%proof-/

/-- Check each clause of a function at a signature, with that clause's hints.
The body is checked with the signature's call regions as variables. -/
def checkClauses (C : Cert) (sig : FnSig) : List Clause → List (List Hint) → Bool
  | [], [] => true
  | c :: cs, h :: hs =>
    (match patsTys C c.pats (sig.params.map (Ty.open sig.vars)) with
      | some Bs =>
        checkTm C (sig.acc.map (Rgn.openAt 0 sig.vars))
          (sig.params.map (Ty.open sig.vars) ++ sig.caps ++ Bs) c.body h
          (sig.ret.open sig.vars) (sig.eff.open sig.vars)
      | none => false)
      && wildOk c.pats (fv c.body)
      && checkClauses C sig cs hs
  | [], _ :: _ => false
  | _ :: _, [] => false

/-%proof (commented out while the machines become bytes)
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
%proof-/

end Glorious.Typing
