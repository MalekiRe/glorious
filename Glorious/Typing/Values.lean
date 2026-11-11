import Glorious.Typing.Runtime

/-!
# Typed values evaluate

Operands, control-free computations and patterns of a typed activation evaluate
to values of their types, and entering a function at one of its signatures
gives a typed activation.
-/

namespace Glorious.Typing

open Core

variable {Δ : Ctx}

/-! ## Rows and store typings -/

theorem Row.le_refl (ε : Row) : Row.le ε ε := fun _ _ h => h

theorem Row.le_trans {a b c : Row} (h₁ : Row.le a b) (h₂ : Row.le b c) : Row.le a c :=
  fun op sig h => h₂ op sig (h₁ op sig h)

theorem Row.nil_le (ε : Row) : Row.le [] ε := fun op sig h => by simp [List.lookup] at h

/-- Putting more handlers below does not change what the nearest ones offer. -/
theorem Row.le_append_left (a b : Row) : Row.le a (a ++ b) := fun op sig h => by
  rw [List.lookup_append, h]
  rfl

theorem StoreTy.Le.refl (S : StoreTy) : S.Le S :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩

theorem StoreTy.Le.trans {S₁ S₂ S₃ : StoreTy} (h₁ : S₁.Le S₂) (h₂ : S₂.Le S₃) : S₁.Le S₃ :=
  ⟨fun id x h => h₂.conts id x (h₁.conts id x h), fun id x h => h₂.labels id x (h₁.labels id x h),
    fun id x h => h₂.handlers id x (h₁.handlers id x h),
    fun id x h => h₂.cells id x (h₁.cells id x h)⟩

/-! ## Values -/

mutual

/-- A value keeps its type when the store typing grows. -/
theorem HasVal.mono {S S' : StoreTy} (hle : S.Le S') :
    ∀ {v : Value} {τ : Ty}, HasVal Δ S v τ → HasVal Δ S' v τ
  | _, _, .int => .int
  | _, _, .data hc hf => .data hc (HasVals.mono hle hf)
  | _, _, .clo hsig hc => .clo hsig (HasVals.mono hle hc)
  | _, _, .cont h => .cont (hle.conts _ _ h)
  | _, _, .label h => .label (hle.labels _ _ h)
  | _, _, .ref h => .ref (hle.cells _ _ h)

theorem HasVals.mono {S S' : StoreTy} (hle : S.Le S') :
    ∀ {vs : List Value} {τs : List Ty}, HasVals Δ S vs τs → HasVals Δ S' vs τs
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (HasVal.mono hle h) (HasVals.mono hle hs)

end

theorem HasVals.append {S : StoreTy} :
    ∀ {vs ws : List Value} {τs σs : List Ty}, HasVals Δ S vs τs → HasVals Δ S ws σs →
      HasVals Δ S (vs ++ ws) (τs ++ σs)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons h hs, h' => .cons h (HasVals.append hs h')

theorem HasVals.snoc {S : StoreTy} {vs : List Value} {τs : List Ty} {v : Value} {τ : Ty}
    (hs : HasVals Δ S vs τs) (h : HasVal Δ S v τ) : HasVals Δ S (vs ++ [v]) (τs ++ [τ]) :=
  hs.append (.cons h .nil)

theorem HasVals.length_eq {S : StoreTy} :
    ∀ {vs : List Value} {τs : List Ty}, HasVals Δ S vs τs → vs.length = τs.length
  | _, _, .nil => rfl
  | _, _, .cons _ hs => by simp [HasVals.length_eq hs]

theorem HasVals.get {S : StoreTy} :
    ∀ {vs : List Value} {τs : List Ty} {i : Nat} {τ : Ty}, HasVals Δ S vs τs → τs[i]? = some τ →
      ∃ v, vs[i]? = some v ∧ HasVal Δ S v τ
  | _, _, _, _, .nil, h => by simp at h
  | _, _, 0, _, .cons hv _, h => by
    simp at h
    subst h
    exact ⟨_, by simp, hv⟩
  | _, _, i + 1, _, .cons _ hs, h => by
    simp at h
    simpa using HasVals.get hs h

/-! What a value of each kind of type looks like. -/

theorem CtorOf.not_int {tag : Nat} {Fs : List Ty} (h : CtorOf Δ tag .int Fs) : False := by
  rcases h with ⟨_, hT⟩ | ⟨_, _, _, hT, _⟩ <;> cases hT

theorem CtorOf.not_fn {tag : Nat} {Fs Ps : List Ty} {σ : Ty} {ε : Row}
    (h : CtorOf Δ tag (.fn Ps σ ε) Fs) : False := by
  rcases h with ⟨_, hT⟩ | ⟨_, _, _, hT, _⟩ <;> cases hT

theorem CtorOf.not_ref {tag : Nat} {Fs : List Ty} {τ : Ty} (h : CtorOf Δ tag (.ref τ) Fs) :
    False := by
  rcases h with ⟨_, hT⟩ | ⟨_, _, _, hT, _⟩ <;> cases hT

theorem CtorOf.not_never {tag : Nat} {Fs : List Ty} (h : CtorOf Δ tag .never Fs) : False := by
  rcases h with ⟨_, hT⟩ | ⟨_, _, _, hT, _⟩ <;> cases hT

/-- No value is the result of a call that does not return. -/
theorem HasVal.not_never {S : StoreTy} {v : Value} (h : HasVal Δ S v .never) : False := by
  cases h with
  | data hc _ => exact hc.not_never

theorem HasVal.int_inv {S : StoreTy} {v : Value} (h : HasVal Δ S v .int) : ∃ n, v = .int n := by
  cases h with
  | int => exact ⟨_, rfl⟩
  | data hc _ => exact hc.not_int.elim

theorem HasVal.ref_inv {S : StoreTy} {v : Value} {τ : Ty} (h : HasVal Δ S v (.ref τ)) :
    ∃ a, v = .ref a ∧ S.cells a = some τ := by
  cases h with
  | ref ha => exact ⟨_, rfl, ha⟩
  | data hc _ => exact hc.not_ref.elim

/-- A value of a callable type is a function at a signature of that type, a
resumption or a label. -/
theorem HasVal.fn_inv {S : StoreTy} {v : Value} {Ps : List Ty} {σ : Ty} {ε : Row}
    (h : HasVal Δ S v (.fn Ps σ ε)) :
    (∃ fn captures Cs, v = .clo fn captures ∧ Δ.fnSig fn ⟨Cs, Ps, σ, ε⟩
        ∧ HasVals Δ S captures Cs)
      ∨ (∃ id o, v = .cont id ∧ Ps = [o] ∧ S.conts id = some (o, σ, ε))
      ∨ (∃ id τ, v = .label id ∧ Ps = [τ] ∧ S.labels id = some τ) := by
  cases h with
  | data hc _ => exact hc.not_fn.elim
  | clo hsig hc => exact .inl ⟨_, _, _, rfl, hsig, hc⟩
  | cont hk => exact .inr (.inl ⟨_, _, rfl, rfl, hk⟩)
  | label hl => exact .inr (.inr ⟨_, _, rfl, rfl, hl⟩)

/-- A value of a type some constructor builds is built by a constructor of that type. -/
theorem HasVal.ctor_inv {S : StoreTy} {v : Value} {T : Ty} {tag : Nat} {Fs : List Ty}
    (h : HasVal Δ S v T) (hc : CtorOf Δ tag T Fs) :
    ∃ t fields Fs', v = .data t fields ∧ CtorOf Δ t T Fs' ∧ HasVals Δ S fields Fs' := by
  cases h with
  | int => exact hc.not_int.elim
  | data hc' hf => exact ⟨_, _, _, rfl, hc', hf⟩
  | clo _ _ => exact hc.not_fn.elim
  | cont _ => exact hc.not_fn.elim
  | label _ => exact hc.not_fn.elim
  | ref _ => exact hc.not_ref.elim

theorem HasVal.unit {S : StoreTy} : HasVal Δ S Value.unit Ty.unit :=
  .data (.inl ⟨rfl, rfl⟩) .nil

/-! ## Operands and control-free computations -/

theorem atom_ok {S : StoreTy} {env : Env} {Γ : TEnv} {a : Atom} {τ : Ty}
    (henv : HasVals Δ S env Γ) (h : HasAtom Γ a τ) :
    ∃ v, a.eval env = some v ∧ HasVal Δ S v τ := by
  cases h with
  | var hi =>
    obtain ⟨v, hv, ht⟩ := henv.get hi
    exact ⟨v, by simp [Atom.eval, hv], ht⟩
  | int => exact ⟨_, rfl, .int⟩

theorem atoms_ok {S : StoreTy} {env : Env} {Γ : TEnv} (henv : HasVals Δ S env Γ)
    {as : List Atom} {τs : List Ty} (h : HasAtoms Γ as τs) :
    ∃ vs, evalAtoms env as = some vs ∧ HasVals Δ S vs τs := by
  induction h with
  | nil => exact ⟨[], rfl, .nil⟩
  | cons ha _ ih =>
    obtain ⟨v, hv, hvt⟩ := atom_ok henv ha
    obtain ⟨vs, hvs, hvst⟩ := ih
    exact ⟨v :: vs, by simp [evalAtoms, hv, hvs], .cons hvt hvst⟩

/-- Following a typed field path through a typed value finds a typed value. -/
theorem follow_ok {S : StoreTy} {σ τ : Ty} {path : List Nat} (h : PlaceOk Δ σ path τ) :
    ∀ {v : Value}, HasVal Δ S v σ → ∃ w, v.follow path = some w ∧ HasVal Δ S w τ := by
  induction h with
  | here => intro v hv; exact ⟨v, by simp [Value.follow], hv⟩
  | tuple hi _ ih =>
    intro v hv
    obtain ⟨t, fields, Fs', rfl, hc, hf⟩ := hv.ctor_inv (tag := 0) (.inl ⟨rfl, rfl⟩)
    have e := CtorOf.unique hc (.inl ⟨(by
      rcases hc with ⟨h0, _⟩ | ⟨_, _, _, hT, _⟩
      · exact h0
      · cases hT), rfl⟩)
    subst e
    obtain ⟨x, hx, hxt⟩ := hf.get hi
    obtain ⟨w, hw, hwt⟩ := ih hxt
    exact ⟨w, by simp [Value.follow, hx, hw], hwt⟩
  | @field name args Fs i path σ τ hall hi _ ih =>
    intro v hv
    cases hv with
    | data hc hf =>
      have e := hall _ _ hc
      subst e
      obtain ⟨x, hx, hxt⟩ := hf.get hi
      obtain ⟨w, hw, hwt⟩ := ih hxt
      exact ⟨w, by simp [Value.follow, hx, hw], hwt⟩

/-- An arithmetic intrinsic on two integers gives an integer, when it gives anything. -/
theorem prim_int {p : Prim} {m n : Int} {v : Value} (h : p.eval [.int m, .int n] = some v) :
    ∃ k, v = .int k := by
  cases p <;> simp only [Prim.eval, checked] at h
  all_goals first
    | (cases h; exact ⟨_, rfl⟩)
    | (split at h <;> first | (cases h; exact ⟨_, rfl⟩) | cases h)

/-- A typed control-free computation gives a value of its type, unless it is
arithmetic that overflows. -/
theorem rhs_ok {S : StoreTy} {env : Env} {Γ : TEnv} {rhs : Rhs} {τ : Ty}
    (henv : HasVals Δ S env Γ) (h : HasRhs Δ Γ rhs τ) :
    (∃ v, rhs.eval env = some v ∧ HasVal Δ S v τ)
      ∨ (∃ p args m n, rhs = .prim p args ∧ evalAtoms env args = some [.int m, .int n]
          ∧ p.eval [.int m, .int n] = none ∧ rhs.eval env = none) := by
  cases h with
  | atom ha =>
    obtain ⟨v, hv, hvt⟩ := atom_ok henv ha
    exact .inl ⟨v, by simp [Rhs.eval, hv], hvt⟩
  | @prim p a b ha hb =>
    obtain ⟨va, hva, hvat⟩ := atom_ok henv ha
    obtain ⟨vb, hvb, hvbt⟩ := atom_ok henv hb
    obtain ⟨m, rfl⟩ := hvat.int_inv
    obtain ⟨n, rfl⟩ := hvbt.int_inv
    have hargs : evalAtoms env [a, b] = some [.int m, .int n] := by simp [evalAtoms, hva, hvb]
    cases hp : p.eval [.int m, .int n] with
    | none => exact .inr ⟨p, [a, b], m, n, rfl, hargs, hp, by simp [Rhs.eval, hargs, hp]⟩
    | some v =>
      obtain ⟨k, rfl⟩ := prim_int hp
      exact .inl ⟨.int k, by simp [Rhs.eval, hargs, hp], .int⟩
  | construct hc hargs =>
    obtain ⟨vs, hvs, hvst⟩ := atoms_ok henv hargs
    exact .inl ⟨_, by simp [Rhs.eval, hvs], .data hc hvst⟩
  | place hv hpl =>
    obtain ⟨v, hv', hvt⟩ := henv.get hv
    obtain ⟨w, hw, hwt⟩ := follow_ok hpl hvt
    exact .inl ⟨w, by simp [Rhs.eval, Place.eval, hv', hw], hwt⟩
  | closure hsig hcaps =>
    obtain ⟨vs, hvs, hvst⟩ := atoms_ok henv hcaps
    exact .inl ⟨_, by simp [Rhs.eval, hvs], .clo hsig hvst⟩

/-! ## Patterns and entering a function -/

mutual

/-- What a typed pattern binds from a typed value has the types the pattern says. -/
theorem PatOk.binds {S : StoreTy} :
    ∀ {p : Pat} {τ : Ty} {Bs : List Ty}, PatOk Δ p τ Bs → ∀ {v : Value} {bs : List Value},
      HasVal Δ S v τ → p.matchVal v = some bs → HasVals Δ S bs Bs
  | _, _, _, .wild, _, _, _, hm => by
    simp [Pat.matchVal] at hm
    subst hm
    exact .nil
  | _, _, _, .bind, _, _, hv, hm => by
    simp [Pat.matchVal] at hm
    subst hm
    exact .cons hv .nil
  | _, _, _, .int, _, _, hv, hm => by
    obtain ⟨m, rfl⟩ := hv.int_inv
    simp [Pat.matchVal] at hm
    obtain ⟨_, rfl⟩ := hm
    exact .nil
  | _, _, _, .ctor hc hps, _, _, hv, hm => by
    obtain ⟨t, fields, Fs', rfl, hc', hf⟩ := hv.ctor_inv hc
    simp [Pat.matchVal] at hm
    obtain ⟨rfl, hm⟩ := hm
    have e := CtorOf.unique hc' hc
    subst e
    exact PatsOk.binds hps hf hm

theorem PatsOk.binds {S : StoreTy} :
    ∀ {ps : List Pat} {τs Bs : List Ty}, PatsOk Δ ps τs Bs → ∀ {vs bs : List Value},
      HasVals Δ S vs τs → Pat.matchVals ps vs = some bs → HasVals Δ S bs Bs
  | _, _, _, .nil, _, _, .nil, hm => by
    simp [Pat.matchVals] at hm
    subst hm
    exact .nil
  | _, _, _, .cons hp hps, _, _, .cons hv hvs, hm => by
    simp only [Pat.matchVals] at hm
    split at hm
    · rename_i b bs' hb hbs
      cases hm
      exact (PatOk.binds hp hv hb).append (PatsOk.binds hps hvs hbs)
    · cases hm

end

theorem PatsOk.length_eq :
    ∀ {ps : List Pat} {τs Bs : List Ty}, PatsOk Δ ps τs Bs → ps.length = τs.length
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ hps => by simp [PatsOk.length_eq hps]

/-- The clause selected for typed arguments has a typed body, in the
environment the machine starts it in. -/
theorem select_ok {S : StoreTy} {sig : FnSig} {vs : List Value}
    (hvs : HasVals Δ S vs sig.params) :
    ∀ (cs : List Clause), (∀ c, c ∈ cs → ClauseOk Δ sig c) → ∀ {body : Tm} {bs : List Value},
      selectClause cs vs = some (body, bs) →
      ∃ Bs, HasVals Δ S bs Bs ∧ HasTm Δ (sig.params ++ sig.caps ++ Bs) body sig.ret sig.eff := by
  intro cs
  induction cs with
  | nil => intro _ body bs h; simp [selectClause] at h
  | cons c cs ih =>
    intro hall body bs h
    obtain ⟨Bs, hpats, hbody⟩ := hall c (List.mem_cons_self ..)
    have hlen : c.pats.length = vs.length := by
      rw [hpats.length_eq, hvs.length_eq]
    cases hm : Pat.matchVals c.pats vs with
    | none =>
      simp [selectClause, hlen, hm] at h
      exact ih (fun c' hc' => hall c' (List.mem_cons_of_mem _ hc')) h
    | some bs' =>
      simp [selectClause, hlen, hm] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨Bs, hpats.binds hvs hm, hbody⟩

/-- A step that leaves a well-typed state, or a result: not a stuck machine. -/
def Safe (Δ : Ctx) (S : StoreTy) : Step State Value → Prop
  | .next s => TypedAt Δ S s
  | .halt _ => True
  | .stuck => False

/-- Entering a function at one of its signatures, on a stack that takes its
result and serves its operations, gives a well-typed state. -/
theorem callFn_safe {p : Program} {S : StoreTy} {fn : Nat} {sig : FnSig}
    {captures vs : List Value} {st : List Frame} {store : Store Frame} {ε : Row}
    (hp : ProgramOk Δ p) (hsig : Δ.fnSig fn sig) (hc : HasVals Δ S captures sig.caps)
    (hv : HasVals Δ S vs sig.params) (hle : Row.le sig.eff ε) (hst : StackOk Δ S st sig.ret ε)
    (hs : StoreOk Δ S store) : Safe Δ S (callFn p fn captures vs st store) := by
  obtain ⟨F, hF, hty, hex⟩ := hp.fns fn sig hsig
  cases hsel : selectClause F.clauses vs with
  | none => exact absurd hsel (hex S vs hv)
  | some r =>
    obtain ⟨body, bs⟩ := r
    obtain ⟨Bs, hbs, hbody⟩ := select_ok hv F.clauses hty hsel
    have h1 : callFn p fn captures vs st store = .next ⟨body, vs ++ captures ++ bs, st, store⟩ := by
      simp [callFn, invoke, hF, hsel]
    rw [h1]
    exact .mk ((hv.append hc).append hbs) hbody hle hst hs

end Glorious.Typing
