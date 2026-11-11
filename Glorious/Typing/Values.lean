import Glorious.Typing.Owned

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
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩

theorem StoreTy.Le.trans {S₁ S₂ S₃ : StoreTy} (h₁ : S₁.Le S₂) (h₂ : S₂.Le S₃) : S₁.Le S₃ :=
  ⟨fun id x h => h₂.conts id x (h₁.conts id x h), fun id x h => h₂.labels id x (h₁.labels id x h),
    fun id x h => h₂.handlers id x (h₁.handlers id x h),
    fun id x h => h₂.cells id x (h₁.cells id x h),
    fun id x h => h₂.loans id x (h₁.loans id x h)⟩

/-! ## Values -/

mutual

/-- A value keeps its type when the store typing grows. -/
theorem HasVal.mono {S S' : StoreTy} (hle : S.Le S') :
    ∀ {v : Value} {τ : Ty}, HasVal Δ S v τ → HasVal Δ S' v τ
  | _, _, .int => .int
  | _, _, .data hc hf => .data hc (HasVals.mono hle hf)
  | _, _, .clo hsig hθ hc hq he hτ => .clo hsig hθ (HasVals.mono hle hc) hq he hτ
  | _, _, .cont h => .cont (hle.conts _ _ h)
  | _, _, .label h hr => .label (hle.labels _ _ h) hr
  | _, _, .ref h hr hl =>
    .ref (hle.cells _ _ h) (fun hR => (hr hR).mono hle) (fun hR hL => (hl hR hL).mono hle)

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

theorem CtorOf.not_fn {tag n : Nat} {Fs Ps : List Ty} {σ : Ty} {ε : Row} {once : Bool}
    {env : Option (List Ty)} {acc : List Rgn}
    (h : CtorOf Δ tag (.fn n Ps σ ε once env acc) Fs) : False := by
  rcases h with ⟨_, hT⟩ | ⟨_, _, _, hT, _⟩ <;> cases hT

theorem CtorOf.not_ref {tag : Nat} {Fs : List Ty} {r : Rgn} {τ : Ty}
    (h : CtorOf Δ tag (.ref r τ) Fs) : False := by
  rcases h with ⟨_, hT⟩ | ⟨_, _, _, hT, _⟩ <;> cases hT

theorem CtorOf.not_never {tag : Nat} {Fs : List Ty} (h : CtorOf Δ tag .never Fs) : False := by
  rcases h with ⟨_, hT⟩ | ⟨_, _, _, hT, _⟩ <;> cases hT

/-- No value is the result of a call that does not return. -/
theorem HasVal.not_never {S : StoreTy} {v : Value} (h : HasVal Δ S v .never) : False := by
  cases h with
  | data hc _ => exact hc.not_never
  | clo _ _ _ _ _ hτ => cases hτ

theorem HasVal.int_inv {S : StoreTy} {v : Value} (h : HasVal Δ S v .int) : ∃ n, v = .int n := by
  cases h with
  | int => exact ⟨_, rfl⟩
  | data hc _ => exact hc.not_int.elim
  | clo _ _ _ _ _ hτ => cases hτ

theorem HasVal.ref_inv {S : StoreTy} {v : Value} {r : Rgn} {τ : Ty}
    (h : HasVal Δ S v (.ref r τ)) :
    ∃ a b, v = .ref a b ∧ S.cells a = some τ ∧ (Δ.regions → OnCell S r a)
      ∧ (Δ.regions → Δ.loans → Tagged S r a b) := by
  cases h with
  | ref ha hr hl => exact ⟨_, _, rfl, ha, hr, hl⟩
  | data hc _ => exact hc.not_ref.elim
  | clo _ _ _ _ _ hτ => cases hτ

/-- A value of a callable type is a closure of a function at a signature whose
type, made with some regions, is that type; or a resumption; or a label. -/
theorem HasVal.fn_inv {S : StoreTy} {v : Value} {n : Nat} {Ps : List Ty} {σ : Ty} {ε : Row}
    {once : Bool} {env : Option (List Ty)} {acc : List Rgn}
    (h : HasVal Δ S v (.fn n Ps σ ε once env acc)) :
    (∃ fn captures sig θ, v = .clo fn captures ∧ Δ.fnSig fn sig ∧ θ.length = sig.crgns
        ∧ HasVals Δ S captures (sig.caps.map (Ty.inst θ)) ∧ n = sig.rgns
        ∧ Ps = sig.params.map (Ty.inst θ) ∧ σ = sig.ret.inst θ ∧ ε = sig.eff.inst θ
        ∧ acc = sig.acc.map (Rgn.inst θ))
      ∨ (∃ id o, v = .cont id ∧ n = 0 ∧ Ps = [o] ∧ S.conts id = some (o, σ, ε, acc))
      ∨ (∃ id τ, v = .label id ∧ n = 0 ∧ Ps = [τ] ∧ S.labels id = some τ
          ∧ (Δ.regions → .lab id ∈ acc)) := by
  cases h with
  | data hc _ => exact hc.not_fn.elim
  | clo hsig hθ hc _ _ hτ =>
    injection hτ with h1 h2 h3 h4 h5 h6 h7
    exact .inl ⟨_, _, _, _, rfl, hsig, hθ, hc, h1, h2, h3, h4, h7⟩
  | cont hk => exact .inr (.inl ⟨_, _, rfl, rfl, rfl, hk⟩)
  | label hl hr => exact .inr (.inr ⟨_, _, rfl, rfl, rfl, hl, hr⟩)

/-- A value whose type states an environment is a function that captured
values of those types. -/
theorem HasVal.env_inv {S : StoreTy} {v : Value} {n : Nat} {Ps Cs : List Ty} {σ : Ty} {ε : Row}
    {once : Bool} {acc : List Rgn} (h : HasVal Δ S v (.fn n Ps σ ε once (some Cs) acc)) :
    ∃ fn captures, v = .clo fn captures ∧ HasVals Δ S captures Cs := by
  cases h with
  | data hc _ => exact hc.not_fn.elim
  | clo hsig hθ hc _ he hτ =>
    injection hτ with h1 h2 h3 h4 h5 h6 h7
    rw [he Cs h6.symm]
    exact ⟨_, _, rfl, hc⟩

/-- A value of a type some constructor builds is built by a constructor of that type. -/
theorem HasVal.ctor_inv {S : StoreTy} {v : Value} {T : Ty} {tag : Nat} {Fs : List Ty}
    (h : HasVal Δ S v T) (hc : CtorOf Δ tag T Fs) :
    ∃ t fields Fs', v = .data t fields ∧ CtorOf Δ t T Fs' ∧ HasVals Δ S fields Fs' := by
  cases h with
  | int => exact hc.not_int.elim
  | data hc' hf => exact ⟨_, _, _, rfl, hc', hf⟩
  | clo _ _ _ _ _ hτ =>
    subst hτ
    exact hc.not_fn.elim
  | cont _ => exact hc.not_fn.elim
  | label _ _ => exact hc.not_fn.elim
  | ref _ _ => exact hc.not_ref.elim

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
    | clo _ _ _ _ _ hτ => cases hτ
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
  | place hv hpl _ =>
    obtain ⟨v, hv', hvt⟩ := henv.get hv
    obtain ⟨w, hw, hwt⟩ := follow_ok hpl hvt
    exact .inl ⟨w, by simp [Rhs.eval, Place.eval, hv', hw], hwt⟩
  | closure hsig hθ hcaps hq he =>
    obtain ⟨vs, hvs, hvst⟩ := atoms_ok henv hcaps
    exact .inl ⟨_, by simp [Rhs.eval, hvs], .clo hsig hθ hvst hq he rfl⟩
  | rebind ha hsig hθ hq he =>
    obtain ⟨v, hv, hvt⟩ := atom_ok henv ha
    obtain ⟨fn', captured, rfl, hcaps⟩ := hvt.env_inv
    exact .inl ⟨_, by simp [Rhs.eval, hv], .clo hsig hθ hcaps hq he rfl⟩

/-- The value of a control-free computation holds no more than the locals it moves. -/
theorem rhs_occ {S : StoreTy} {env : Env} {Γ : TEnv} {rhs : Rhs} {σ : Ty} {v : Value}
    (hD : DupSound Δ) (henv : HasVals Δ S env Γ) (h : HasRhs Δ Γ rhs σ)
    (hv : rhs.eval env = some v) (id : Nat) : occ id v ≤ sumAt id env (rhsMoves rhs) := by
  cases h with
  | atom ha => exact Nat.le_of_eq (occ_eval id env hv)
  | @prim p a b ha hb =>
    obtain ⟨va, hva, hvat⟩ := atom_ok henv ha
    obtain ⟨vb, hvb, hvbt⟩ := atom_ok henv hb
    obtain ⟨m, rfl⟩ := hvat.int_inv
    obtain ⟨n, rfl⟩ := hvbt.int_inv
    simp [Rhs.eval, evalAtoms, hva, hvb] at hv
    obtain ⟨k, rfl⟩ := prim_int hv
    simp [occ]
  | construct hc hargs =>
    obtain ⟨vs, hvs, _⟩ := atoms_ok (S := S) henv hargs
    simp [Rhs.eval, hvs] at hv
    subst hv
    exact Nat.le_of_eq (by simpa [occ, rhsMoves] using occs_evalAtoms id env _ hvs)
  | place hx hpl hdup =>
    obtain ⟨x, hx', hxt⟩ := henv.get hx
    obtain ⟨w, hw, hwt⟩ := follow_ok hpl hxt
    simp [Rhs.eval, Place.eval, hx', hw] at hv
    subst hv
    simp [hD _ _ _ hwt hdup id]
  | closure hsig hθ hcaps hq he =>
    obtain ⟨vs, hvs, _⟩ := atoms_ok (S := S) henv hcaps
    simp [Rhs.eval, hvs] at hv
    subst hv
    exact Nat.le_of_eq (by simpa [occ, rhsMoves] using occs_evalAtoms id env _ hvs)
  | rebind ha hsig hθ hq he =>
    obtain ⟨w, hw, hwt⟩ := atom_ok henv ha
    obtain ⟨fn', captured, rfl, _⟩ := hwt.env_inv
    simp [Rhs.eval, hw] at hv
    subst hv
    exact Nat.le_of_eq (by simpa [occ, rhsMoves] using occ_eval id env hw)

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

/-- The clause the machine selects is one of the function's clauses, and its
patterns match the arguments. -/
theorem select_mem {vs : List Value} : ∀ (cs : List Clause) {body : Tm} {bs : List Value},
    selectClause cs vs = some (body, bs) →
    ∃ c, c ∈ cs ∧ c.body = body ∧ Pat.matchVals c.pats vs = some bs
      ∧ c.pats.length = vs.length := by
  intro cs
  induction cs with
  | nil => intro body bs h; simp [selectClause] at h
  | cons c cs ih =>
    intro body bs h
    by_cases hlen : c.pats.length = vs.length
    · cases hm : Pat.matchVals c.pats vs with
      | none =>
        simp [selectClause, hlen, hm] at h
        obtain ⟨c', hc', hrest⟩ := ih h
        exact ⟨c', List.mem_cons_of_mem _ hc', hrest⟩
      | some bs' =>
        simp [selectClause, hlen, hm] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨c, List.mem_cons_self .., rfl, hm, hlen⟩
    · simp [selectClause, hlen] at h

/-- `after` is `store` once some cells have been released: the resumptions are
the same, and its cells hold no more than before. -/
structure Kept (store after : Store Frame) : Prop where
  conts : after.conts = store.conts
  cells : ∀ id, occCells id after.cells ≤ occCells id store.cells

theorem Kept.refl (store : Store Frame) : Kept store store :=
  ⟨rfl, fun _ => Nat.le_refl _⟩

theorem Kept.release {store after : Store Frame} (a : Nat) (h : Kept (store.release a) after) :
    Kept store after :=
  ⟨h.conts, fun id => Nat.le_trans (h.cells id) (occCells_release_le id store.cells a)⟩

/-- A step that leaves a well-typed state, or a result: not a stuck machine. The
state it leaves has the given store, less the cells whose scopes the step left,
and its locals and stack hold each resumption no more often than `budget` allows. -/
def Safe (Δ : Ctx) (S : StoreTy) (budget : Nat → Nat) (store : Store Frame) :
    Step State Value → Prop
  | .next s =>
    TypedAt Δ S s ∧ Kept store s.store
      ∧ ∀ id, occEnv id s.env (fv s.tm) + occStack id s.stack ≤ budget id
  | .halt _ => True
  | .stuck => False

theorem Safe.weaken {S : StoreTy} {b b' : Nat → Nat} {store : Store Frame}
    {r : Step State Value} (h : Safe Δ S b store r) (hb : ∀ id, b id ≤ b' id) :
    Safe Δ S b' store r := by
  cases r with
  | next s => exact ⟨h.1, h.2.1, fun id => Nat.le_trans (h.2.2 id) (hb id)⟩
  | halt v => exact True.intro
  | stuck => exact h.elim

/-- What is safe once a cell is released is safe counting from before. -/
theorem Safe.release {S : StoreTy} {b : Nat → Nat} {store : Store Frame} {a : Nat}
    {r : Step State Value} (h : Safe Δ S b (store.release a) r) : Safe Δ S b store r := by
  cases r with
  | next s => exact ⟨h.1, h.2.1.release a, h.2.2⟩
  | halt v => exact True.intro
  | stuck => exact h.elim

/-- Entering a function at one of its signatures, with regions for those the
signature leaves open, on a stack that takes its result, serves its operations
and grants its regions, gives a well-typed state, which holds no more than the
arguments, the captures and the stack did. The body's typing is the one
derivation the signature has, with those regions put for its variables. -/
theorem callFn_safe {p : Program} {S : StoreTy} {fn : Nat} {sig : FnSig} {θ rs : List Rgn}
    {captures vs : List Value} {st : List Frame} {store : Store Frame} {ε : Row}
    {ϕ : List Rgn} (hp : ProgramOk Δ p) (hsig : Δ.fnSig fn sig) (hθ : θ.length = sig.crgns)
    (hrs : rs.length = sig.rgns) (hc : HasVals Δ S captures (sig.caps.map (Ty.inst θ)))
    (hv : HasVals Δ S vs ((sig.params.map (Ty.inst θ)).map (Ty.open rs)))
    (hle : Row.le ((sig.eff.inst θ).open rs) ε)
    (hacc : Sub ((sig.acc.map (Rgn.inst θ)).map (Rgn.openAt 0 rs)) ϕ)
    (hnd : Δ.loans → ((sig.acc.map (Rgn.inst θ)).map (Rgn.openAt 0 rs)).Nodup)
    (hst : StackOk Δ S st ((sig.ret.inst θ).open rs) ε ϕ) (hs : StoreOk Δ S store) :
    Safe Δ S (fun id => occs id vs + occs id captures + occStack id st) store
      (callFn p fn captures vs st store) := by
  obtain ⟨hwf, F, hF, hty, hex⟩ := hp.fns fn sig hsig
  simp only [FnSig.wf, Bool.and_eq_true, List.all_eq_true] at hwf
  obtain ⟨⟨⟨⟨⟨hwc, hwp⟩, hwr⟩, hwe⟩, hwa⟩, hcl⟩ := hwf
  have hvars : sig.vars = Rgn.callVars θ.length rs.length := by simp [FnSig.vars, hθ, hrs]
  have hparams : (sig.params.map (Ty.open sig.vars)).map (Ty.inst (θ ++ rs))
      = (sig.params.map (Ty.inst θ)).map (Ty.open rs) := by
    rw [List.map_map, List.map_map, hvars]
    exact List.map_congr_left fun t ht =>
      Ty.open_callVars_inst (by rw [hθ]; exact hwp t ht) rs
  have hcaps : sig.caps.map (Ty.inst (θ ++ rs)) = sig.caps.map (Ty.inst θ) :=
    List.map_congr_left fun t ht => Ty.inst_append (by rw [hθ]; exact hwc t ht) rs
  have hret : (sig.ret.open sig.vars).inst (θ ++ rs) = (sig.ret.inst θ).open rs := by
    rw [hvars]
    exact Ty.open_callVars_inst (by rw [hθ]; exact hwr) rs
  have heff : (sig.eff.open sig.vars).inst (θ ++ rs) = (sig.eff.inst θ).open rs := by
    rw [hvars]
    exact Row.open_callVars_inst (by rw [hθ]; exact hwe) rs
  have hac : (sig.acc.map (Rgn.openAt 0 sig.vars)).map (Rgn.inst (θ ++ rs))
      = (sig.acc.map (Rgn.inst θ)).map (Rgn.openAt 0 rs) := by
    rw [List.map_map, List.map_map, hvars]
    exact List.map_congr_left fun r hr =>
      Rgn.open_callVars_inst 0 θ rs r (by rw [hθ]; exact hwa r hr)
  have hv' : HasVals Δ S vs ((sig.params.map (Ty.open sig.vars)).map (Ty.inst (θ ++ rs))) := by
    rw [hparams]
    exact hv
  cases hsel : selectClause F.clauses vs with
  | none => exact absurd hsel (hex S vs (θ ++ rs) hv')
  | some r =>
    obtain ⟨body, bs⟩ := r
    obtain ⟨c, hcm, rfl, hm, hlen⟩ := select_mem F.clauses hsel
    obtain ⟨⟨Bs, hpats, hbody⟩, hwild⟩ := hty c hcm
    have hbs := (hpats.inst hp.stable (θ ++ rs)).binds hv' hm
    have hb := hbody.inst hp.stable (θ ++ rs) fun hL =>
      ⟨InjOn.of_nodup (by rw [hac]; exact hnd hL), closed_open (by simpa [closed] using hcl) _ _⟩
    rw [List.map_append, List.map_append, hcaps, hret, heff, hac] at hb
    have h1 : callFn p fn captures vs st store = .next ⟨c.body, vs ++ captures ++ bs, st, store⟩ := by
      simp [callFn, invoke, hF, hsel]
    rw [h1]
    refine ⟨.mk ((hv'.append hc).append hbs) hb hle hacc hst hs, Kept.refl _, fun id => ?_⟩
    have := clause_env_le id (captures := captures) (live := fv c.body) hm hlen hwild
    show occEnv id (vs ++ captures ++ bs) (fv c.body) + occStack id st
      ≤ occs id vs + occs id captures + occStack id st
    omega

/-- Entering a function that has no regions of its own to choose: a handler's
function, or a cleanup. -/
theorem enter_safe {p : Program} {S : StoreTy} {fn : Nat} {Cs Ps : List Ty} {ρ : Ty}
    {ε₀ ε : Row} {Φ ϕ : List Rgn} {captures vs : List Value} {st : List Frame}
    {store : Store Frame} (hp : ProgramOk Δ p) (he : Enters Δ fn Cs Ps ρ ε₀ Φ)
    (hc : HasVals Δ S captures Cs) (hv : HasVals Δ S vs Ps) (hle : Row.le ε₀ ε) (hΦ : Sub Φ ϕ)
    (hst : StackOk Δ S st ρ ε ϕ) (hs : StoreOk Δ S store) :
    Safe Δ S (fun id => occs id vs + occs id captures + occStack id st) store
      (callFn p fn captures vs st store) := by
  obtain ⟨sig, θ, hsig, hθ, hr, rfl, rfl, rfl, hrow, hsub, hnd⟩ := he
  have hps : (sig.params.map (Ty.inst θ)).map (Ty.open []) = sig.params.map (Ty.inst θ) := by
    rw [List.map_map]
    exact List.map_congr_left fun t _ => Ty.open_nil _
  have hac : (sig.acc.map (Rgn.inst θ)).map (Rgn.openAt 0 []) = sig.acc.map (Rgn.inst θ) := by
    rw [List.map_map]
    exact List.map_congr_left fun r _ => Rgn.openAt_nil 0 _
  exact callFn_safe (rs := []) (ε := ε) (ϕ := ϕ) hp hsig hθ (by simp [hr]) hc
    (by rw [hps]; exact hv) (by rw [Row.open_nil]; exact Row.le_trans hrow hle)
    (by rw [hac]; exact hsub.trans hΦ) (by rw [hac]; exact hnd)
    (by rw [Ty.open_nil]; exact hst) hs

end Glorious.Typing
