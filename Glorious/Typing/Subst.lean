import Glorious.Typing.Static

/-!
# Typing does not depend on which regions stand for a function's region variables

A function's body is typed once, with its regions as variables. Whatever
regions it is entered with, the same derivation types it with those regions in
place of the variables. So at run time every type is one whose regions are
cells, and nothing has to carry an assignment of regions to variables around.
-/

namespace Glorious.Typing

open Core

variable {Δ : Ctx}

theorem Sub.map {a b : List Rgn} (h : Sub a b) (f : Rgn → Rgn) : Sub (a.map f) (b.map f) := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  exact List.mem_map.mpr ⟨x, h x hx, rfl⟩

theorem Sub.refl (a : List Rgn) : Sub a a := fun _ h => h

theorem Sub.trans {a b c : List Rgn} (h₁ : Sub a b) (h₂ : Sub b c) : Sub a c :=
  fun r h => h₂ r (h₁ r h)

theorem Row.inst_cons (θ : List Rgn) (op : Nat) (targs : List Ty) (H : Row) :
    Row.inst θ ((op, targs) :: H) = (op, targs.map (Ty.inst θ)) :: Row.inst θ H := by
  simp only [Row.inst, Ty.mapRow, Ty.mapEntry, Ty.mapRs_eq]
  rfl

theorem Row.inst_append (θ : List Rgn) : ∀ (a b : Row),
    Row.inst θ (a ++ b) = Row.inst θ a ++ Row.inst θ b
  | [], b => by simp [Row.inst, Ty.mapRow]
  | e :: a, b => by
    have ih := Row.inst_append θ a b
    simp only [Row.inst] at ih
    simp [Row.inst, Ty.mapRow, ih]

theorem Row.inst_nil (θ : List Rgn) : Row.inst θ [] = [] := by simp [Row.inst, Ty.mapRow]

theorem FnSig.ty_inst (sig : FnSig) (θ' θ : List Rgn) (once : Bool) (env : Option (List Ty)) :
    (sig.ty θ' once env).inst θ
      = sig.ty (θ'.map (Rgn.inst θ)) once (env.map (·.map (Ty.inst θ))) := by
  simp only [FnSig.ty, Ty.inst_fn, List.map_map, Ty.inst_inst, Row.inst_inst]
  congr 1
  · exact List.map_congr_left fun t _ => Ty.inst_inst θ' θ t
  · exact List.map_congr_left fun r _ => Rgn.inst_inst θ' θ r

theorem caps_inst (caps : List Ty) (θ' θ : List Rgn) :
    (caps.map (Ty.inst θ')).map (Ty.inst θ) = caps.map (Ty.inst (θ'.map (Rgn.inst θ))) := by
  rw [List.map_map]
  exact List.map_congr_left fun t _ => Ty.inst_inst θ' θ t

theorem opens_inst (Ps : List Ty) (rs θ : List Rgn) :
    (Ps.map (Ty.open rs)).map (Ty.inst θ)
      = (Ps.map (Ty.inst θ)).map (Ty.open (rs.map (Rgn.inst θ))) := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun t _ => Ty.open_inst rs θ t

theorem acc_open_inst (acc rs θ : List Rgn) :
    (acc.map (Rgn.openAt 0 rs)).map (Rgn.inst θ)
      = (acc.map (Rgn.inst θ)).map (Rgn.openAt 0 (rs.map (Rgn.inst θ))) := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun r _ => Rgn.openAt_inst 0 rs θ r

/-! ## Values of a declared type -/

theorem CtorOf.inst (hΔ : Δ.Stable) {tag : Nat} {T : Ty} {Fs : List Ty} (θ : List Rgn)
    (h : CtorOf Δ tag T Fs) : CtorOf Δ tag (T.inst θ) (Fs.map (Ty.inst θ)) := by
  rcases h with ⟨h0, rfl⟩ | ⟨h0, name, args, rfl, hF⟩
  · exact .inl ⟨h0, Ty.inst_tuple θ Fs⟩
  · refine .inr ⟨h0, name, args.map (Ty.inst θ), Ty.inst_data θ name args, ?_⟩
    rw [hΔ.ctor, hF]
    rfl

/-- A constructor of an instantiated type is one of the type. -/
theorem CtorOf.of_inst (hΔ : Δ.Stable) {tag name : Nat} {args Fs' : List Ty} {θ : List Rgn}
    (h : CtorOf Δ tag (.data name (args.map (Ty.inst θ))) Fs') :
    ∃ Fs, CtorOf Δ tag (.data name args) Fs ∧ Fs' = Fs.map (Ty.inst θ) := by
  rcases h with ⟨_, hT⟩ | ⟨h0, name', args', hT, hF⟩
  · cases hT
  · injection hT with hn ha
    subst hn
    subst ha
    rw [hΔ.ctor] at hF
    cases hc : Δ.ctorFields tag name args with
    | none =>
      rw [hc] at hF
      cases hF
    | some Fs =>
      rw [hc] at hF
      exact ⟨Fs, .inr ⟨h0, name, args, rfl, hc⟩, (Option.some.inj hF).symm⟩

theorem HasAtom.inst {Γ : TEnv} {a : Atom} {τ : Ty} (θ : List Rgn) (h : HasAtom Γ a τ) :
    HasAtom (Γ.map (Ty.inst θ)) a (τ.inst θ) := by
  cases h with
  | var h => exact .var (by simp [h])
  | int =>
    rw [Ty.inst_int]
    exact .int

theorem HasAtoms.inst {Γ : TEnv} (θ : List Rgn) : ∀ {as : List Atom} {τs : List Ty},
    HasAtoms Γ as τs → HasAtoms (Γ.map (Ty.inst θ)) as (τs.map (Ty.inst θ))
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (h.inst θ) (HasAtoms.inst θ hs)

theorem PlaceOk.inst (hΔ : Δ.Stable) (θ : List Rgn) : ∀ {σ : Ty} {path : List Nat} {τ : Ty},
    PlaceOk Δ σ path τ → PlaceOk Δ (σ.inst θ) path (τ.inst θ)
  | _, _, _, .here => .here
  | _, _, _, .tuple (Fs := Fs) hi hp => by
    rw [Ty.inst_tuple]
    exact .tuple (by simp [hi]) (PlaceOk.inst hΔ θ hp)
  | _, _, _, .field (Fs := Fs) hall hi hp => by
    rw [Ty.inst_data]
    refine .field (Fs := Fs.map (Ty.inst θ)) (fun tag Fs' hc => ?_) (by simp [hi])
      (PlaceOk.inst hΔ θ hp)
    obtain ⟨Fs₀, hc₀, rfl⟩ := CtorOf.of_inst hΔ hc
    rw [hall tag Fs₀ hc₀]

theorem Linear.inst (hΔ : Δ.Stable) {Γ : TEnv} {moved rest : List Nat} (θ : List Rgn)
    (h : Linear Δ Γ moved rest) : Linear Δ (Γ.map (Ty.inst θ)) moved rest := by
  intro i τ' hi hnd
  rw [List.getElem?_map] at hi
  cases hg : Γ[i]? with
  | none => simp [hg] at hi
  | some τ =>
    simp [hg] at hi
    subst hi
    exact h i τ hg (fun hd => hnd ((hΔ.dup τ θ).mpr hd))

theorem HasRhs.inst (hΔ : Δ.Stable) {Γ : TEnv} {rhs : Rhs} {τ : Ty} (θ : List Rgn)
    (h : HasRhs Δ Γ rhs τ) : HasRhs Δ (Γ.map (Ty.inst θ)) rhs (τ.inst θ) := by
  cases h with
  | atom ha => exact .atom (ha.inst θ)
  | prim ha hb =>
    have ha' := ha.inst θ
    have hb' := hb.inst θ
    rw [Ty.inst_int] at ha' hb' ⊢
    exact .prim ha' hb'
  | construct hc hargs => exact .construct (hc.inst hΔ θ) (hargs.inst θ)
  | place hv hp hd =>
    exact .place (by simp [hv]) (hp.inst hΔ θ) ((hΔ.dup _ θ).mpr hd)
  | @closure fn captures sig θ' once env hsig hlen hcaps hq he =>
    rw [FnSig.ty_inst]
    refine .closure hsig (by simpa using hlen) ?_ hq ?_
    · rw [← caps_inst]
      exact hcaps.inst θ
    · intro Cs hCs
      cases env with
      | none => cases hCs
      | some Cs₀ =>
        simp at hCs
        subst hCs
        rw [he Cs₀ rfl, caps_inst]
  | @rebind a fn sig θ' n Ps σ ε acc once once' env ha hsig hlen hq he =>
    rw [FnSig.ty_inst]
    have ha' := ha.inst θ
    rw [Ty.inst_fn] at ha'
    simp only [Option.map_some, caps_inst] at ha'
    refine .rebind ha' hsig (by simpa using hlen) hq ?_
    intro Cs hCs
    cases env with
    | none => cases hCs
    | some Cs₀ =>
      simp at hCs
      subst hCs
      rw [he Cs₀ rfl, caps_inst]

/-! ## Patterns -/

mutual

theorem PatOk.inst (hΔ : Δ.Stable) (θ : List Rgn) : ∀ {p : Pat} {τ : Ty} {Bs : List Ty},
    PatOk Δ p τ Bs → PatOk Δ p (τ.inst θ) (Bs.map (Ty.inst θ))
  | _, _, _, .wild => .wild
  | _, _, _, .bind => .bind
  | _, _, _, .int => by
    rw [Ty.inst_int]
    exact .int
  | _, _, _, .ctor hc hps => .ctor (hc.inst hΔ θ) (PatsOk.inst hΔ θ hps)

theorem PatsOk.inst (hΔ : Δ.Stable) (θ : List Rgn) :
    ∀ {ps : List Pat} {τs : List Ty} {Bs : List Ty},
    PatsOk Δ ps τs Bs → PatsOk Δ ps (τs.map (Ty.inst θ)) (Bs.map (Ty.inst θ))
  | _, _, _, .nil => .nil
  | _, _, _, .cons hp hps => by
    rw [List.map_append]
    exact .cons (PatOk.inst hΔ θ hp) (PatsOk.inst hΔ θ hps)

end

/-! ## Handlers -/

theorem Enters.inst {fn : Nat} {Cs Ps : List Ty} {ρ : Ty} {ε : Row} {Φ : List Rgn}
    (θ : List Rgn) (h : Enters Δ fn Cs Ps ρ ε Φ) :
    Enters Δ fn (Cs.map (Ty.inst θ)) (Ps.map (Ty.inst θ)) (ρ.inst θ) (ε.inst θ)
      (Φ.map (Rgn.inst θ)) := by
  obtain ⟨sig, θ', hsig, hlen, hr, rfl, rfl, rfl, hle, hsub⟩ := h
  refine ⟨sig, θ'.map (Rgn.inst θ), hsig, by simpa using hlen, hr, caps_inst _ _ _,
    caps_inst _ _ _, Ty.inst_inst _ _ _, ?_, ?_⟩
  · rw [← Row.inst_inst]
    exact Row.le_inst hle θ
  · have := hsub.map (Rgn.inst θ)
    rw [List.map_map] at this
    intro r hr'
    refine this r ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr'
    exact List.mem_map.mpr ⟨x, hx, (Rgn.inst_inst _ _ _)⟩

theorem ArmsOk.inst (hΔ : Δ.Stable) {Cs : List Ty} {ρ : Ty} {ε : Row} {Φ : List Rgn}
    (θ : List Rgn) : ∀ {ops : List (Nat × Nat)} {H : Row}, ArmsOk Δ Cs ρ ε Φ ops H →
    ArmsOk Δ (Cs.map (Ty.inst θ)) (ρ.inst θ) (ε.inst θ) (Φ.map (Rgn.inst θ)) ops (H.inst θ)
  | _, _, .nil => by
    rw [Row.inst_nil]
    exact .nil
  | _, _, .terminal (Ps := Ps) hop hent hrest => by
    rw [Row.inst_cons]
    refine .terminal (Ps := Ps.map (Ty.inst θ)) ?_ (hent.inst θ) (ArmsOk.inst hΔ θ hrest)
    rw [hΔ.op, hop]
    rfl
  | _, _, .resumptive (Ps := Ps) (o := o) hop hent hrest => by
    rw [Row.inst_cons]
    refine .resumptive (Ps := Ps.map (Ty.inst θ)) (o := o.inst θ) ?_ ?_ (ArmsOk.inst hΔ θ hrest)
    · rw [hΔ.op, hop]
      rfl
    · have := hent.inst θ
      simpa [Ty.inst_fn] using this

theorem HandlerOk.inst (hΔ : Δ.Stable) {Cs : List Ty} {ret : Nat} {ops : List (Nat × Nat)}
    {σ ρ : Ty} {H ε : Row} {Φ : List Rgn} (θ : List Rgn)
    (h : HandlerOk Δ Cs ret ops σ ρ H ε Φ) :
    HandlerOk Δ (Cs.map (Ty.inst θ)) ret ops (σ.inst θ) (ρ.inst θ) (H.inst θ) (ε.inst θ)
      (Φ.map (Rgn.inst θ)) := by
  refine ⟨by simpa using h.ret.inst θ, h.arms.inst hΔ θ, fun c hc => ?_⟩
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc
  exact (hΔ.dup c₀ θ).mpr (h.dup c₀ hc₀)

/-! ## Computations -/

theorem snoc_inst (Γ : TEnv) (σ : Ty) (θ : List Rgn) :
    (Γ ++ [σ]).map (Ty.inst θ) = Γ.map (Ty.inst θ) ++ [σ.inst θ] := by simp

/-- **Typing is closed under instantiating regions.** -/
theorem HasTm.inst (hΔ : Δ.Stable) (θ : List Rgn) {ϕ : List Rgn} {Γ : TEnv} {tm : Tm} {τ : Ty}
    {ε : Row} (h : HasTm Δ ϕ Γ tm τ ε) :
    HasTm Δ (ϕ.map (Rgn.inst θ)) (Γ.map (Ty.inst θ)) tm (τ.inst θ) (ε.inst θ) := by
  induction h with
  | ret ha => exact .ret (ha.inst θ)
  | let_ hrhs hlin _ ih =>
    rw [snoc_inst] at ih
    exact .let_ (hrhs.inst hΔ θ) (hlin.inst hΔ θ) ih
  | @call Γ f args body n rs Ps σ τ ε' ε once env acc hf hn hargs hrow hacc hlin _ ih =>
    have hf' := hf.inst θ
    rw [Ty.inst_fn] at hf'
    rw [snoc_inst, Ty.open_inst] at ih
    refine .call (rs := rs.map (Rgn.inst θ)) hf' (by simpa using hn) ?_ ?_ ?_ (hlin.inst hΔ θ) ih
    · rw [← opens_inst]
      exact hargs.inst θ
    · rw [← Row.open_inst]
      exact Row.le_inst hrow θ
    · rw [← acc_open_inst]
      exact hacc.map _
  | @tail Γ f args n rs Ps σ τ ε' ε once env acc hf hn hret hargs hrow hacc hlin =>
    have hf' := hf.inst θ
    rw [Ty.inst_fn] at hf'
    refine .tail (rs := rs.map (Rgn.inst θ)) hf' (by simpa using hn) ?_ ?_ ?_ ?_ (hlin.inst hΔ θ)
    · rw [← Ty.open_inst, hret]
    · rw [← opens_inst]
      exact hargs.inst θ
    · rw [← Row.open_inst]
      exact Row.le_inst hrow θ
    · rw [← acc_open_inst]
      exact hacc.map _
  | @callNever Γ f args body n rs Ps σ τ ε' ε once env acc hf hn hargs hrow hacc hlin _ ih =>
    have hf' := hf.inst θ
    rw [Ty.inst_fn, Ty.inst_never] at hf'
    rw [snoc_inst] at ih
    refine .callNever (rs := rs.map (Rgn.inst θ)) hf' (by simpa using hn) ?_ ?_ ?_
      (hlin.inst hΔ θ) ih
    · rw [← opens_inst]
      exact hargs.inst θ
    · rw [← Row.open_inst]
      exact Row.le_inst hrow θ
    · rw [← acc_open_inst]
      exact hacc.map _
  | @tailNever Γ f args n rs Ps τ ε' ε once env acc hf hn hargs hrow hacc hlin =>
    have hf' := hf.inst θ
    rw [Ty.inst_fn, Ty.inst_never] at hf'
    refine .tailNever (rs := rs.map (Rgn.inst θ)) hf' (by simpa using hn) ?_ ?_ ?_
      (hlin.inst hΔ θ)
    · rw [← opens_inst]
      exact hargs.inst θ
    · rw [← Row.open_inst]
      exact Row.le_inst hrow θ
    · rw [← acc_open_inst]
      exact hacc.map _
  | handle hthunk hcaps hok hrow hacc hΦ hlin _ ih =>
    have ht' := hthunk.inst θ
    rw [Ty.inst_fn] at ht'
    rw [snoc_inst] at ih
    have hrow' := Row.le_inst hrow θ
    rw [Row.inst_append] at hrow'
    exact .handle (by simpa using ht') (hcaps.inst θ) (hok.inst hΔ θ) hrow' (hacc.map _)
      (hΦ.map _) (hlin.inst hΔ θ) ih
  | handleTail hthunk hcaps hok hrow hacc hΦ =>
    have ht' := hthunk.inst θ
    rw [Ty.inst_fn] at ht'
    have hrow' := Row.le_inst hrow θ
    rw [Row.inst_append] at hrow'
    exact .handleTail (by simpa using ht') (hcaps.inst θ) (hok.inst hΔ θ) hrow' (hacc.map _)
      (hΦ.map _)
  | @raise Γ op args targs Ps τ ε hl hop hargs hlin =>
    refine .raise (targs := targs.map (Ty.inst θ)) (Ps := Ps.map (Ty.inst θ)) ?_ ?_
      (hargs.inst θ) (hlin.inst hΔ θ)
    · rw [Row.lookup_inst, hl]
      rfl
    · rw [hΔ.op, hop]
      rfl
  | @perform Γ op args body targs Ps σ τ ε hl hop hargs hlin _ ih =>
    rw [snoc_inst] at ih
    refine .perform (targs := targs.map (Ty.inst θ)) (Ps := Ps.map (Ty.inst θ)) ?_ ?_
      (hargs.inst θ) (hlin.inst hΔ θ) ih
    · rw [Row.lookup_inst, hl]
      rfl
    · rw [hΔ.op, hop]
      rfl
  | label hthunk hσ hε hn hreg hacc hrow hlin _ ih =>
    have ht' := hthunk.inst θ
    simp only [Ty.inst_fn, List.map_cons, List.map_nil, Option.map_none] at ht'
    rw [snoc_inst] at ih
    refine .label ht' (Ty.lc_inst hσ θ) (Row.lc_inst hε θ) hn ?_ ?_ (Row.le_inst hrow θ)
      (hlin.inst hΔ θ) ih
    · intro hr
      exact ⟨(hreg hr).1, List.mem_map.mpr ⟨_, (hreg hr).2, rfl⟩⟩
    · intro x hx
      obtain ⟨x₀, hx₀, rfl⟩ := List.mem_map.mp hx
      rcases hacc x₀ hx₀ with ⟨h1, rfl⟩ | ⟨hfree, hmem⟩
      · exact .inl ⟨h1, rfl⟩
      · exact .inr ⟨by rw [Rgn.inst_free]; exact hfree, List.mem_map.mpr ⟨x₀, hmem, rfl⟩⟩
  | labelTail hthunk hσ hε hn hreg hacc hrow =>
    have ht' := hthunk.inst θ
    simp only [Ty.inst_fn, List.map_cons, List.map_nil, Option.map_none] at ht'
    refine .labelTail ht' (Ty.lc_inst hσ θ) (Row.lc_inst hε θ) hn ?_ ?_ (Row.le_inst hrow θ)
    · intro hr
      exact ⟨(hreg hr).1, List.mem_map.mpr ⟨_, (hreg hr).2, rfl⟩⟩
    · intro x hx
      obtain ⟨x₀, hx₀, rfl⟩ := List.mem_map.mp hx
      rcases hacc x₀ hx₀ with ⟨h1, rfl⟩ | ⟨hfree, hmem⟩
      · exact .inl ⟨h1, rfl⟩
      · exact .inr ⟨by rw [Rgn.inst_free]; exact hfree, List.mem_map.mpr ⟨x₀, hmem, rfl⟩⟩
  | guard hcl hthunk hrow haccc hacc hlin _ ih =>
    have hc' := hcl.inst θ
    have ht' := hthunk.inst θ
    simp only [Ty.inst_fn, List.map_nil, Row.inst_nil] at hc' ht'
    rw [snoc_inst] at ih
    exact .guard hc' ht' (Row.le_inst hrow θ) (haccc.map _) (hacc.map _) (hlin.inst hΔ θ) ih
  | guardTail hcl hthunk hrow haccc hacc hlin =>
    have hc' := hcl.inst θ
    have ht' := hthunk.inst θ
    simp only [Ty.inst_fn, List.map_nil, Row.inst_nil] at hc' ht'
    exact .guardTail hc' ht' (Row.le_inst hrow θ) (haccc.map _) (hacc.map _) (hlin.inst hΔ θ)
  | cancel hk hrow hacc hlin _ ih =>
    have hk' := hk.inst θ
    simp only [Ty.inst_fn, List.map_cons, List.map_nil] at hk'
    rw [snoc_inst] at ih
    have hu : Ty.unit.inst θ = Ty.unit := by simp [Ty.unit, Ty.inst_tuple]
    rw [hu] at ih
    exact .cancel hk' (Row.le_inst hrow θ) (hacc.map _) (hlin.inst hΔ θ) ih
  | @cell Γ init thunk body n r σ ρ τ εt ε once env acc hinit hthunk hσ hρ hε hn hreg hacc hrow
      hlin _ ih =>
    have ht' := hthunk.inst θ
    simp only [Ty.inst_fn, List.map_cons, List.map_nil, Ty.inst_ref] at ht'
    rw [snoc_inst] at ih
    refine .cell (hinit.inst θ) ht' (Ty.lc_inst hσ θ) (Ty.lc_inst hρ θ) (Row.lc_inst hε θ) ?_ ?_ ?_
      (Row.le_inst hrow θ) (hlin.inst hΔ θ) ih
    · rcases hn with h0 | ⟨h1, rfl⟩
      · exact .inl h0
      · exact .inr ⟨h1, rfl⟩
    · intro hr
      obtain ⟨h1, rfl⟩ := hreg hr
      exact ⟨h1, rfl⟩
    · intro x hx
      obtain ⟨x₀, hx₀, rfl⟩ := List.mem_map.mp hx
      rcases hacc x₀ hx₀ with ⟨h1, rfl⟩ | ⟨hfree, hmem⟩
      · exact .inl ⟨h1, rfl⟩
      · exact .inr ⟨by rw [Rgn.inst_free]; exact hfree, List.mem_map.mpr ⟨x₀, hmem, rfl⟩⟩
  | @cellTail Γ init thunk n r σ τ εt ε once env acc hinit hthunk hσ hτ hε hn hreg hacc hrow
      hlin =>
    have ht' := hthunk.inst θ
    simp only [Ty.inst_fn, List.map_cons, List.map_nil, Ty.inst_ref] at ht'
    refine .cellTail (hinit.inst θ) ht' (Ty.lc_inst hσ θ) (Ty.lc_inst hτ θ) (Row.lc_inst hε θ)
      ?_ ?_ ?_ (Row.le_inst hrow θ) (hlin.inst hΔ θ)
    · rcases hn with h0 | ⟨h1, rfl⟩
      · exact .inl h0
      · exact .inr ⟨h1, rfl⟩
    · intro hr
      obtain ⟨h1, rfl⟩ := hreg hr
      exact ⟨h1, rfl⟩
    · intro x hx
      obtain ⟨x₀, hx₀, rfl⟩ := List.mem_map.mp hx
      rcases hacc x₀ hx₀ with ⟨h1, rfl⟩ | ⟨hfree, hmem⟩
      · exact .inl ⟨h1, rfl⟩
      · exact .inr ⟨by rw [Rgn.inst_free]; exact hfree, List.mem_map.mpr ⟨x₀, hmem, rfl⟩⟩
  | load ha hr hd _ ih =>
    have ha' := ha.inst θ
    rw [Ty.inst_ref] at ha'
    rw [snoc_inst] at ih
    exact .load ha' (fun h => List.mem_map.mpr ⟨_, hr h, rfl⟩) ((hΔ.dup _ θ).mpr hd) ih
  | store ha hr hb hlin _ ih =>
    have ha' := ha.inst θ
    rw [Ty.inst_ref] at ha'
    rw [snoc_inst] at ih
    have hu : Ty.unit.inst θ = Ty.unit := by simp [Ty.unit, Ty.inst_tuple]
    rw [hu] at ih
    exact .store ha' (fun h => List.mem_map.mpr ⟨_, hr h, rfl⟩) (hb.inst θ) (hlin.inst hΔ θ) ih
  | swap ha hr hb hlin _ ih =>
    have ha' := ha.inst θ
    rw [Ty.inst_ref] at ha'
    rw [snoc_inst] at ih
    exact .swap ha' (fun h => List.mem_map.mpr ⟨_, hr h, rfl⟩) (hb.inst θ) (hlin.inst hΔ θ) ih
  | write ha _ ih =>
    rw [snoc_inst] at ih
    have hu : Ty.unit.inst θ = Ty.unit := by simp [Ty.unit, Ty.inst_tuple]
    rw [hu] at ih
    exact .write (ha.inst θ) ih
  | read _ ih =>
    rw [snoc_inst] at ih
    have hp : (Ty.tuple [.int, .int]).inst θ = .tuple [.int, .int] := by
      simp [Ty.inst_tuple, Ty.inst_int]
    rw [hp] at ih
    exact .read ih

end Glorious.Typing
