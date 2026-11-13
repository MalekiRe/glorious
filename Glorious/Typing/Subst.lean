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

/-! ## Regions that stay apart -/

/-- Different regions among `ϕ` stay different when `θ` is put in. -/
def InjOn (ϕ θ : List Rgn) : Prop :=
  ∀ x y, x ∈ ϕ → y ∈ ϕ → x.inst θ = y.inst θ → x = y

theorem InjOn.mono {ϕ ϕ' θ : List Rgn} (h : InjOn ϕ θ) (hsub : Sub ϕ' ϕ) : InjOn ϕ' θ :=
  fun x y hx hy => h x y (hsub x hx) (hsub y hy)

/-- A list without repeats, of regions that stay apart, has none afterwards. -/
theorem InjOn.nodup {ϕ θ : List Rgn} (h : InjOn ϕ θ) : ∀ {l : List Rgn}, Sub l ϕ → l.Nodup →
    (l.map (Rgn.inst θ)).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hsub, hnd => by
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hnd
    refine List.nodup_cons.mpr ⟨fun hm => ?_, h.nodup (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) hl⟩
    obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
    have := h b a (hsub b (List.mem_cons_of_mem _ hb)) (hsub a (List.mem_cons_self ..)) he
    subst this
    exact ha hb

/-- The same when some of the list is bound, which instantiating leaves alone. -/
theorem InjOn.nodup_scope {ϕ θ : List Rgn} (h : InjOn ϕ θ) : ∀ {l : List Rgn},
    (∀ x, x ∈ l → x.free = false ∨ x ∈ ϕ) → l.Nodup → (l.map (Rgn.inst θ)).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hin, hnd => by
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hnd
    refine List.nodup_cons.mpr
      ⟨fun hm => ?_, h.nodup_scope (fun x hx => hin x (List.mem_cons_of_mem _ hx)) hl⟩
    obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
    have hfree : (b.inst θ).free = (a.inst θ).free := by rw [he]
    rw [Rgn.inst_free, Rgn.inst_free] at hfree
    rcases hin a (List.mem_cons_self ..) with hfa | hpa
    · rw [hfa] at hfree
      rw [Rgn.inst_bound hfree, Rgn.inst_bound hfa] at he
      subst he
      exact ha hb
    · rcases hin b (List.mem_cons_of_mem _ hb) with hfb | hpb
      · rw [hfb] at hfree
        rw [Rgn.inst_bound hfb, Rgn.inst_bound hfree.symm] at he
        subst he
        exact ha hb
      · have := h b a hpb hpa he
        subst this
        exact ha hb

/-- A region that becomes leave to write was leave to write. -/
theorem Rgn.inst_eq_wr {θ : List Rgn} {x z : Rgn} (h : x.inst θ = .wr z) :
    ∃ y, x = .wr y ∧ y.inst θ = z := by
  cases x with
  | var i =>
    have hc : Rgn.clean θ[i]? = .wr z := h
    cases hθ : θ[i]? with
    | none => rw [hθ] at hc; cases hc
    | some w => rw [hθ] at hc; cases w <;> cases hc
  | bound k => cases h
  | cell a => cases h
  | lab id => cases h
  | loan b => cases h
  | wr y => exact ⟨y, rfl, Rgn.wr.inj h⟩

/-- Among regions that stay apart and say that what may be written may be
read, nothing becomes leave to write `ρ` that was not. -/
theorem InjOn.ne_wr {ϕ θ : List Rgn} (h : InjOn ϕ θ) (hc : closed ϕ = true) {x ρ : Rgn}
    (hx : x ∈ ϕ) (hρ : ρ ∈ ϕ) (hne : x ≠ .wr ρ) : x.inst θ ≠ .wr (ρ.inst θ) := by
  intro he
  obtain ⟨y, rfl, hy⟩ := Rgn.inst_eq_wr he
  exact hne (congrArg Rgn.wr (h y ρ (closed_mem hc hx) hρ hy))

/-- Regions whose images do not repeat stay apart. -/
theorem InjOn.of_nodup {θ : List Rgn} : ∀ {l : List Rgn}, (l.map (Rgn.inst θ)).Nodup → InjOn l θ
  | [], _ => fun x _ hx => by cases hx
  | a :: l, h => by
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp h
    intro x y hx hy he
    rcases List.mem_cons.mp hx with hxa | hxl
    · rcases List.mem_cons.mp hy with hya | hyl
      · rw [hxa, hya]
      · subst hxa
        exact absurd (List.mem_map.mpr ⟨y, hyl, he.symm⟩) ha
    · rcases List.mem_cons.mp hy with hya | hyl
      · subst hya
        exact absurd (List.mem_map.mpr ⟨x, hxl, he⟩) ha
      · exact InjOn.of_nodup hl x y hxl hyl he

theorem Rgn.openAt_eq_wr {d : Nat} {rs : List Rgn} {x z : Rgn} (h : x.openAt d rs = .wr z) :
    ∃ y, x = .wr y ∧ y.openAt d rs = z := by
  cases x with
  | var i => cases h
  | bound j =>
    by_cases hj : j < d
    · simp [Rgn.openAt, hj] at h
    · cases hr : rs[j - d]? with
      | none => simp [Rgn.openAt, hj, hr] at h
      | some w =>
        have : Rgn.clean (some w) = .wr z := by simpa [Rgn.openAt, hj, hr] using h
        cases w <;> cases this
  | cell a => cases h
  | lab id => cases h
  | loan b => cases h
  | wr y => exact ⟨y, rfl, Rgn.wr.inj h⟩

/-- Opening keeps a list saying that what may be written may be read. -/
theorem closed_open {l : List Rgn} (h : closed l = true) (d : Nat) (rs : List Rgn) :
    closed (l.map (Rgn.openAt d rs)) = true := by
  refine List.all_eq_true.mpr fun x hx => ?_
  cases x with
  | wr z =>
    obtain ⟨x₀, hx₀, he⟩ := List.mem_map.mp hx
    obtain ⟨y, rfl, rfl⟩ := Rgn.openAt_eq_wr he
    simpa using List.mem_map.mpr ⟨y, closed_mem h hx₀, rfl⟩
  | _ => rfl

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

/-- The same of any type: only a tuple or a declared type has constructors. -/
theorem CtorOf.of_inst_any (hΔ : Δ.Stable) {tag : Nat} {T : Ty} {Fs' : List Ty} {θ : List Rgn}
    (h : CtorOf Δ tag (T.inst θ) Fs') :
    ∃ Fs, CtorOf Δ tag T Fs ∧ Fs' = Fs.map (Ty.inst θ) := by
  cases T with
  | int =>
    rw [Ty.inst_int] at h
    rcases h with ⟨_, hT⟩ | ⟨_, _, _, hT, _⟩ <;> cases hT
  | never =>
    rw [Ty.inst_never] at h
    rcases h with ⟨_, hT⟩ | ⟨_, _, _, hT, _⟩ <;> cases hT
  | ref ρ t =>
    rw [Ty.inst_ref] at h
    rcases h with ⟨_, hT⟩ | ⟨_, _, _, hT, _⟩ <;> cases hT
  | fn n ps r e once env acc =>
    rw [Ty.inst_fn] at h
    rcases h with ⟨_, hT⟩ | ⟨_, _, _, hT, _⟩ <;> cases hT
  | tuple fs =>
    rw [Ty.inst_tuple] at h
    rcases h with ⟨h0, hT⟩ | ⟨_, _, _, hT, _⟩
    · injection hT with hT
      exact ⟨fs, .inl ⟨h0, rfl⟩, hT.symm⟩
    · cases hT
  | data name args =>
    rw [Ty.inst_data] at h
    exact CtorOf.of_inst hΔ h

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

theorem Uniform.inst (hΔ : Δ.Stable) {T τ : Ty} (θ : List Rgn) (h : Uniform Δ T τ) :
    Uniform Δ (T.inst θ) (τ.inst θ) := by
  intro tag Fs' hc σ hσ
  obtain ⟨Fs₀, hc₀, rfl⟩ := CtorOf.of_inst_any hΔ hc
  obtain ⟨σ₀, hσ₀, rfl⟩ := List.mem_map.mp hσ
  rw [h tag Fs₀ hc₀ σ₀ hσ₀]

theorem PartOk.inst (hΔ : Δ.Stable) (θ : List Rgn) : ∀ {σ : Ty} {path : List Nat} {τ : Ty},
    PartOk Δ σ path τ → PartOk Δ (σ.inst θ) path (τ.inst θ)
  | _, _, _, .here => .here
  | _, _, _, .tuple (Fs := Fs) hi hp => by
    rw [Ty.inst_tuple]
    exact .tuple (by simp [hi]) (PartOk.inst hΔ θ hp)
  | _, _, _, .field (Fs := Fs) hall hi hp => by
    rw [Ty.inst_data]
    refine .field (Fs := Fs.map (Ty.inst θ)) (fun tag Fs' hc => ?_) (by simp [hi])
      (PartOk.inst hΔ θ hp)
    obtain ⟨Fs₀, hc₀, rfl⟩ := CtorOf.of_inst hΔ hc
    rw [hall tag Fs₀ hc₀]
  | _, _, _, .elem hu hp => .elem (hu.inst hΔ θ) (PartOk.inst hΔ θ hp)

theorem Grows.inst (hΔ : Δ.Stable) {T τ : Ty} (θ : List Rgn) (h : Grows Δ T τ) :
    Grows Δ (T.inst θ) (τ.inst θ) := by
  intro tag Fs' hc
  obtain ⟨Fs₀, hc₀, rfl⟩ := CtorOf.of_inst_any hΔ hc
  simpa using (h tag Fs₀ hc₀).inst hΔ θ

theorem Shrinks.inst (hΔ : Δ.Stable) {T : Ty} (θ : List Rgn) (h : Shrinks Δ T) :
    Shrinks Δ (T.inst θ) := by
  intro tag Fs' hc hne
  obtain ⟨Fs₀, hc₀, rfl⟩ := CtorOf.of_inst_any hΔ hc
  have hne₀ : Fs₀ ≠ [] := fun e => hne (by simp [e])
  simpa [List.map_dropLast] using (h tag Fs₀ hc₀ hne₀).inst hΔ θ

theorem HasRhs.inst (hΔ : Δ.Stable) {Γ : TEnv} {rhs : Rhs} {τ : Ty} (θ : List Rgn)
    (h : HasRhs Δ Γ rhs τ) : HasRhs Δ (Γ.map (Ty.inst θ)) rhs (τ.inst θ) := by
  cases h with
  | atom ha => exact .atom (ha.inst θ)
  | arrGet ha hi hu hd =>
    have hi' := hi.inst θ
    rw [Ty.inst_int] at hi'
    exact .arrGet (ha.inst θ) hi' (hu.inst hΔ θ) ((hΔ.dup _ θ).mpr hd)
  | arrSet ha hi hv hu hd =>
    have hi' := hi.inst θ
    rw [Ty.inst_int] at hi'
    exact .arrSet (ha.inst θ) hi' (hv.inst θ) (hu.inst hΔ θ) ((hΔ.dup _ θ).mpr hd)
  | arrLen ha hb =>
    rw [Ty.inst_int]
    exact .arrLen (ha.inst θ) (hb.inst θ)
  | arrPush ha hv hg hd => exact .arrPush (ha.inst θ) (hv.inst θ) (hg.inst hΔ θ) ((hΔ.dup _ θ).mpr hd)
  | arrPop ha hb hu hs hd =>
    rw [Ty.inst_tuple]
    refine .arrPop (ha.inst θ) (hb.inst θ) (hu.inst hΔ θ) (hs.inst hΔ θ) ?_
    have := (hΔ.dup _ θ).mpr hd
    rwa [Ty.inst_tuple] at this
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
    (θ : List Rgn) (hinj : Δ.loans → InjOn Φ θ) (h : Enters Δ fn Cs Ps ρ ε Φ) :
    Enters Δ fn (Cs.map (Ty.inst θ)) (Ps.map (Ty.inst θ)) (ρ.inst θ) (ε.inst θ)
      (Φ.map (Rgn.inst θ)) := by
  obtain ⟨sig, θ', hsig, hlen, hr, rfl, rfl, rfl, hle, hsub, hnd⟩ := h
  have hacc : (sig.acc.map (Rgn.inst θ')).map (Rgn.inst θ)
      = sig.acc.map (Rgn.inst (θ'.map (Rgn.inst θ))) := by
    rw [List.map_map]
    exact List.map_congr_left fun r _ => Rgn.inst_inst _ _ _
  refine ⟨sig, θ'.map (Rgn.inst θ), hsig, by simpa using hlen, hr, caps_inst _ _ _,
    caps_inst _ _ _, Ty.inst_inst _ _ _, ?_, ?_, ?_⟩
  · rw [← Row.inst_inst]
    exact Row.le_inst hle θ
  · rw [← hacc]
    exact hsub.map _
  · intro hL
    rw [← hacc]
    exact (hinj hL).nodup hsub (hnd hL)

theorem ArmsOk.inst (hΔ : Δ.Stable) {Cs : List Ty} {ρ : Ty} {ε : Row} {Φ : List Rgn}
    (θ : List Rgn) (hinj : Δ.loans → InjOn Φ θ) :
    ∀ {ops : List (Nat × Nat)} {H : Row}, ArmsOk Δ Cs ρ ε Φ ops H →
    ArmsOk Δ (Cs.map (Ty.inst θ)) (ρ.inst θ) (ε.inst θ) (Φ.map (Rgn.inst θ)) ops (H.inst θ)
  | _, _, .nil => by
    rw [Row.inst_nil]
    exact .nil
  | _, _, .terminal (Ps := Ps) hop hent hrest => by
    rw [Row.inst_cons]
    refine .terminal (Ps := Ps.map (Ty.inst θ)) ?_ (hent.inst θ hinj)
      (ArmsOk.inst hΔ θ hinj hrest)
    rw [hΔ.op, hop]
    rfl
  | _, _, .resumptive (Ps := Ps) (o := o) hop hent hrest => by
    rw [Row.inst_cons]
    refine .resumptive (Ps := Ps.map (Ty.inst θ)) (o := o.inst θ) ?_ ?_
      (ArmsOk.inst hΔ θ hinj hrest)
    · rw [hΔ.op, hop]
      rfl
    · have := hent.inst θ hinj
      simpa [Ty.inst_fn] using this

theorem HandlerOk.inst (hΔ : Δ.Stable) {Cs : List Ty} {ret : Nat} {ops : List (Nat × Nat)}
    {σ ρ : Ty} {H ε : Row} {Φ : List Rgn} (θ : List Rgn) (hinj : Δ.loans → InjOn Φ θ)
    (h : HandlerOk Δ Cs ret ops σ ρ H ε Φ) :
    HandlerOk Δ (Cs.map (Ty.inst θ)) ret ops (σ.inst θ) (ρ.inst θ) (H.inst θ) (ε.inst θ)
      (Φ.map (Rgn.inst θ)) := by
  refine ⟨by simpa using h.ret.inst θ hinj, h.arms.inst hΔ θ hinj, fun c hc => ?_⟩
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc
  exact (hΔ.dup c₀ θ).mpr (h.dup c₀ hc₀)

/-! ## Computations -/

theorem snoc_inst (Γ : TEnv) (σ : Ty) (θ : List Rgn) :
    (Γ ++ [σ]).map (Ty.inst θ) = Γ.map (Ty.inst θ) ++ [σ.inst θ] := by simp

/-- **Typing is closed under instantiating regions.** Under the rules for
borrows the regions the computation may touch have to stay apart: a borrow
takes away leave to use what was lent, which means nothing if what was lent
can also be reached under another name. -/
theorem HasTm.inst (hΔ : Δ.Stable) (θ : List Rgn) {ϕ : List Rgn}
    (hinj : Δ.loans → InjOn ϕ θ ∧ closed ϕ = true) {Γ : TEnv} {tm : Tm} {τ : Ty}
    {ε : Row} (h : HasTm Δ ϕ Γ tm τ ε) :
    HasTm Δ (ϕ.map (Rgn.inst θ)) (Γ.map (Ty.inst θ)) tm (τ.inst θ) (ε.inst θ) := by
  induction h with
  | ret ha => exact .ret (ha.inst θ)
  | let_ hrhs hlin _ ih =>
    rw [snoc_inst] at ih
    exact .let_ (hrhs.inst hΔ θ) (hlin.inst hΔ θ) ih
  | @call Γ f args body n rs Ps σ τ ε' ε once env acc hform hlin _ ih =>
    have hf := hform.callee
    have hn := hform.len
    have hargs := hform.argsOk
    have hrow := hform.row
    have hacc := hform.touches
    have hnd := hform.apart
    have hf' := hf.inst θ
    rw [Ty.inst_fn] at hf'
    rw [snoc_inst, Ty.open_inst] at ih
    refine .call (rs := rs.map (Rgn.inst θ)) ⟨hf', (by simpa using hn), ?_, ?_, ?_, ?_⟩
      (hlin.inst hΔ θ) ih
    · rw [← opens_inst]
      exact hargs.inst θ
    · rw [← Row.open_inst]
      exact Row.le_inst hrow θ
    · rw [← acc_open_inst]
      exact hacc.map _
    · intro hL
      rw [← acc_open_inst]
      exact (hinj hL).1.nodup hacc (hnd hL)
  | @tail Γ f args n rs Ps σ τ ε' ε once env acc hform hret hlin =>
    have hf := hform.callee
    have hn := hform.len
    have hargs := hform.argsOk
    have hrow := hform.row
    have hacc := hform.touches
    have hnd := hform.apart
    have hf' := hf.inst θ
    rw [Ty.inst_fn] at hf'
    refine .tail (rs := rs.map (Rgn.inst θ)) ⟨hf', (by simpa using hn), ?_, ?_, ?_, ?_⟩ ?_
      (hlin.inst hΔ θ)
    · rw [← opens_inst]
      exact hargs.inst θ
    · rw [← Row.open_inst]
      exact Row.le_inst hrow θ
    · rw [← acc_open_inst]
      exact hacc.map _
    · intro hL
      rw [← acc_open_inst]
      exact (hinj hL).1.nodup hacc (hnd hL)
    · rw [← Ty.open_inst, hret]
  | @callNever Γ f args body n rs Ps σ τ ε' ε once env acc hform hlin _ ih =>
    have hf := hform.callee
    have hn := hform.len
    have hargs := hform.argsOk
    have hrow := hform.row
    have hacc := hform.touches
    have hnd := hform.apart
    have hf' := hf.inst θ
    rw [Ty.inst_fn, Ty.inst_never] at hf'
    rw [snoc_inst] at ih
    refine .callNever (rs := rs.map (Rgn.inst θ)) ⟨hf', (by simpa using hn), ?_, ?_, ?_, ?_⟩
      (hlin.inst hΔ θ) ih
    · rw [← opens_inst]
      exact hargs.inst θ
    · rw [← Row.open_inst]
      exact Row.le_inst hrow θ
    · rw [← acc_open_inst]
      exact hacc.map _
    · intro hL
      rw [← acc_open_inst]
      exact (hinj hL).1.nodup hacc (hnd hL)
  | @tailNever Γ f args n rs Ps τ ε' ε once env acc hform hlin =>
    have hf := hform.callee
    have hn := hform.len
    have hargs := hform.argsOk
    have hrow := hform.row
    have hacc := hform.touches
    have hnd := hform.apart
    have hf' := hf.inst θ
    rw [Ty.inst_fn, Ty.inst_never] at hf'
    refine .tailNever (rs := rs.map (Rgn.inst θ)) ⟨hf', (by simpa using hn), ?_, ?_, ?_, ?_⟩
      (hlin.inst hΔ θ)
    · rw [← opens_inst]
      exact hargs.inst θ
    · rw [← Row.open_inst]
      exact Row.le_inst hrow θ
    · rw [← acc_open_inst]
      exact hacc.map _
    · intro hL
      rw [← acc_open_inst]
      exact (hinj hL).1.nodup hacc (hnd hL)
  | handle hform hlin _ ih =>
    have hthunk := hform.thunk
    have hcaps := hform.caps
    have hok := hform.handler
    have hrow := hform.row
    have hacc := hform.touches
    have hΦ := hform.within
    have hnd := hform.apart
    have ht' := hthunk.inst θ
    rw [Ty.inst_fn] at ht'
    rw [snoc_inst] at ih
    have hrow' := Row.le_inst hrow θ
    rw [Row.inst_append] at hrow'
    exact .handle ⟨(by simpa using ht'), (hcaps.inst θ),
      (hok.inst hΔ θ fun hL => (hinj hL).1.mono hΦ), hrow', (hacc.map _), (hΦ.map _),
      (fun hL => (hinj hL).1.nodup (hacc.trans hΦ) (hnd hL))⟩ (hlin.inst hΔ θ) ih
  | handleTail hform =>
    have hthunk := hform.thunk
    have hcaps := hform.caps
    have hok := hform.handler
    have hrow := hform.row
    have hacc := hform.touches
    have hΦ := hform.within
    have hnd := hform.apart
    have ht' := hthunk.inst θ
    rw [Ty.inst_fn] at ht'
    have hrow' := Row.le_inst hrow θ
    rw [Row.inst_append] at hrow'
    exact .handleTail ⟨(by simpa using ht'), (hcaps.inst θ),
      (hok.inst hΔ θ fun hL => (hinj hL).1.mono hΦ), hrow', (hacc.map _), (hΦ.map _),
      (fun hL => (hinj hL).1.nodup (hacc.trans hΦ) (hnd hL))⟩
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
  | label hform hlin _ ih =>
    have hthunk := hform.thunk
    have hσ := hform.lcGiven
    have hε := hform.lcRow
    have hn := hform.arity
    have hreg := hform.region
    have hacc := hform.touches
    have hnd := hform.apart
    have hrow := hform.row
    have ht' := hthunk.inst θ
    simp only [Ty.inst_fn, List.map_cons, List.map_nil, Option.map_none] at ht'
    rw [snoc_inst] at ih
    refine .label ⟨ht', (Ty.lc_inst hσ θ), (Row.lc_inst hε θ), hn, ?_, ?_, ?_, (Row.le_inst hrow θ)⟩
      (hlin.inst hΔ θ) ih
    · intro hr
      exact ⟨(hreg hr).1, List.mem_map.mpr ⟨_, (hreg hr).2, rfl⟩⟩
    · intro x hx
      obtain ⟨x₀, hx₀, rfl⟩ := List.mem_map.mp hx
      rcases hacc x₀ hx₀ with ⟨h1, rfl⟩ | ⟨hfree, hmem⟩
      · exact .inl ⟨h1, rfl⟩
      · exact .inr ⟨by rw [Rgn.inst_free]; exact hfree, List.mem_map.mpr ⟨x₀, hmem, rfl⟩⟩
    · intro hL
      refine (hinj hL).1.nodup_scope (fun x hx => ?_) (hnd hL)
      rcases hacc x hx with ⟨_, rfl⟩ | ⟨_, hmem⟩
      · exact .inl rfl
      · exact .inr hmem
  | labelTail hform =>
    have hthunk := hform.thunk
    have hσ := hform.lcGiven
    have hε := hform.lcRow
    have hn := hform.arity
    have hreg := hform.region
    have hacc := hform.touches
    have hnd := hform.apart
    have hrow := hform.row
    have ht' := hthunk.inst θ
    simp only [Ty.inst_fn, List.map_cons, List.map_nil, Option.map_none] at ht'
    refine .labelTail ⟨ht', (Ty.lc_inst hσ θ), (Row.lc_inst hε θ), hn, ?_, ?_, ?_,
      (Row.le_inst hrow θ)⟩
    · intro hr
      exact ⟨(hreg hr).1, List.mem_map.mpr ⟨_, (hreg hr).2, rfl⟩⟩
    · intro x hx
      obtain ⟨x₀, hx₀, rfl⟩ := List.mem_map.mp hx
      rcases hacc x₀ hx₀ with ⟨h1, rfl⟩ | ⟨hfree, hmem⟩
      · exact .inl ⟨h1, rfl⟩
      · exact .inr ⟨by rw [Rgn.inst_free]; exact hfree, List.mem_map.mpr ⟨x₀, hmem, rfl⟩⟩
    · intro hL
      refine (hinj hL).1.nodup_scope (fun x hx => ?_) (hnd hL)
      rcases hacc x hx with ⟨_, rfl⟩ | ⟨_, hmem⟩
      · exact .inl rfl
      · exact .inr hmem
  | guard hform hlin _ ih =>
    have hcl := hform.cleanup
    have hthunk := hform.thunk
    have hrow := hform.row
    have haccc := hform.cleanupTouches
    have hacc := hform.touches
    have hnd := hform.apart
    have hc' := hcl.inst θ
    have ht' := hthunk.inst θ
    simp only [Ty.inst_fn, List.map_nil, Row.inst_nil] at hc' ht'
    rw [snoc_inst] at ih
    exact .guard ⟨hc', ht', (Row.le_inst hrow θ), (haccc.map _), (hacc.map _),
      (fun hL => ⟨(hinj hL).1.nodup haccc (hnd hL).1, (hinj hL).1.nodup hacc (hnd hL).2⟩)⟩
      (hlin.inst hΔ θ) ih
  | guardTail hform hlin =>
    have hcl := hform.cleanup
    have hthunk := hform.thunk
    have hrow := hform.row
    have haccc := hform.cleanupTouches
    have hacc := hform.touches
    have hnd := hform.apart
    have hc' := hcl.inst θ
    have ht' := hthunk.inst θ
    simp only [Ty.inst_fn, List.map_nil, Row.inst_nil] at hc' ht'
    exact .guardTail ⟨hc', ht', (Row.le_inst hrow θ), (haccc.map _), (hacc.map _),
      (fun hL => ⟨(hinj hL).1.nodup haccc (hnd hL).1, (hinj hL).1.nodup hacc (hnd hL).2⟩)⟩
      (hlin.inst hΔ θ)
  | cancel hk hrow hacc hlin _ ih =>
    have hk' := hk.inst θ
    simp only [Ty.inst_fn, List.map_cons, List.map_nil] at hk'
    rw [snoc_inst] at ih
    have hu : Ty.unit.inst θ = Ty.unit := by simp [Ty.unit, Ty.inst_tuple]
    rw [hu] at ih
    exact .cancel hk' (Row.le_inst hrow θ) (hacc.map _) (hlin.inst hΔ θ) ih
  | @cell Γ init thunk body n r σ ρ τ εt ε once env acc hform hlin _ ih =>
    have hinit := hform.init
    have hthunk := hform.thunk
    have hσ := hform.lcHeld
    have hρ := hform.lcGiven
    have hε := hform.lcRow
    have hn := hform.arity
    have hreg := hform.region
    have hacc := hform.touches
    have hnd := hform.apart
    have hrow := hform.row
    have ht' := hthunk.inst θ
    simp only [Ty.inst_fn, List.map_cons, List.map_nil, Ty.inst_ref] at ht'
    rw [snoc_inst] at ih
    refine .cell ⟨(hinit.inst θ), ht', (Ty.lc_inst hσ θ), (Ty.lc_inst hρ θ), (Row.lc_inst hε θ), ?_,
      ?_, ?_, ?_, (Row.le_inst hrow θ)⟩ (hlin.inst hΔ θ) ih
    · rcases hn with h0 | ⟨h1, rfl⟩
      · exact .inl h0
      · exact .inr ⟨h1, rfl⟩
    · intro hr
      obtain ⟨h1, rfl⟩ := hreg hr
      exact ⟨h1, rfl⟩
    · intro x hx
      obtain ⟨x₀, hx₀, rfl⟩ := List.mem_map.mp hx
      rcases hacc x₀ hx₀ with ⟨h1, rfl | rfl⟩ | ⟨hfree, hmem⟩
      · exact .inl ⟨h1, .inl rfl⟩
      · exact .inl ⟨h1, .inr rfl⟩
      · exact .inr ⟨by rw [Rgn.inst_free]; exact hfree, List.mem_map.mpr ⟨x₀, hmem, rfl⟩⟩
    · intro hL
      refine (hinj hL).1.nodup_scope (fun x hx => ?_) (hnd hL)
      rcases hacc x hx with ⟨_, rfl | rfl⟩ | ⟨_, hmem⟩
      · exact .inl rfl
      · exact .inl rfl
      · exact .inr hmem
  | @cellTail Γ init thunk n r σ τ εt ε once env acc hform hlin =>
    have hinit := hform.init
    have hthunk := hform.thunk
    have hσ := hform.lcHeld
    have hτ := hform.lcGiven
    have hε := hform.lcRow
    have hn := hform.arity
    have hreg := hform.region
    have hacc := hform.touches
    have hnd := hform.apart
    have hrow := hform.row
    have ht' := hthunk.inst θ
    simp only [Ty.inst_fn, List.map_cons, List.map_nil, Ty.inst_ref] at ht'
    refine .cellTail ⟨(hinit.inst θ), ht', (Ty.lc_inst hσ θ), (Ty.lc_inst hτ θ), (Row.lc_inst hε θ),
      ?_, ?_, ?_, ?_, (Row.le_inst hrow θ)⟩ (hlin.inst hΔ θ)
    · rcases hn with h0 | ⟨h1, rfl⟩
      · exact .inl h0
      · exact .inr ⟨h1, rfl⟩
    · intro hr
      obtain ⟨h1, rfl⟩ := hreg hr
      exact ⟨h1, rfl⟩
    · intro x hx
      obtain ⟨x₀, hx₀, rfl⟩ := List.mem_map.mp hx
      rcases hacc x₀ hx₀ with ⟨h1, rfl | rfl⟩ | ⟨hfree, hmem⟩
      · exact .inl ⟨h1, .inl rfl⟩
      · exact .inl ⟨h1, .inr rfl⟩
      · exact .inr ⟨by rw [Rgn.inst_free]; exact hfree, List.mem_map.mpr ⟨x₀, hmem, rfl⟩⟩
    · intro hL
      refine (hinj hL).1.nodup_scope (fun x hx => ?_) (hnd hL)
      rcases hacc x hx with ⟨_, rfl | rfl⟩ | ⟨_, hmem⟩
      · exact .inl rfl
      · exact .inl rfl
      · exact .inr hmem
  | @lend Γ uniq r thunk pre post body n ρ κ σ ρt τ Pre Post εt ε once env acc hform hlin _ ih =>
    have hr := hform.ref
    have hthunk := hform.thunk
    have hσ := hform.lcHeld
    have hρ := hform.lcGiven
    have hε := hform.lcRow
    have hn := hform.arity
    have hreg := hform.region
    have hloan := hform.loan
    have hacc := hform.touches
    have hrow := hform.row
    have hr' := hr.inst θ
    have ht' := hthunk.inst θ
    simp only [Ty.inst_fn, List.map_append, List.map_cons, Ty.inst_ref] at hr' ht'
    rw [snoc_inst] at ih
    have hlc : ∀ t, t ∈ Pre.map (Ty.inst θ) ++ Post.map (Ty.inst θ) → t.lc = true := by
      intro t ht
      rw [← List.map_append] at ht
      obtain ⟨t₀, h₀, rfl⟩ := List.mem_map.mp ht
      exact Ty.lc_inst (hform.lcArgs t₀ h₀) θ
    refine .lend ⟨hr', ht', hform.before.inst θ, hform.after.inst θ, hlc, (Ty.lc_inst hσ θ),
      (Ty.lc_inst hρ θ), (Row.lc_inst hε θ), ?_, ?_, ?_, ?_, (Row.le_inst hrow θ)⟩
      (hlin.inst hΔ θ) ih
    · rcases hn with ⟨h0, rfl⟩ | ⟨h1, rfl⟩
      · exact .inl ⟨h0, rfl⟩
      · exact .inr ⟨h1, rfl⟩
    · exact fun hR => List.mem_map.mpr ⟨_, hreg hR, rfl⟩
    · intro hL
      obtain ⟨h1, hρϕ, hw, hnd, hquiet⟩ := hloan hL
      refine ⟨h1, List.mem_map.mpr ⟨_, hρϕ, rfl⟩,
        fun hu => List.mem_map.mpr ⟨_, hw hu, rfl⟩, ?_, by rw [hquiet, Row.inst_nil]⟩
      refine (hinj hL).1.nodup_scope (fun x hx => ?_) hnd
      rcases hacc x hx with ⟨_, rfl | ⟨_, rfl⟩⟩ | ⟨_, hmem, _⟩
      · exact .inl rfl
      · exact .inl rfl
      · exact .inr hmem
    · intro x hx
      obtain ⟨x₀, hx₀, rfl⟩ := List.mem_map.mp hx
      rcases hacc x₀ hx₀ with ⟨h1, rfl | ⟨hu, rfl⟩⟩ | ⟨hfree, hmem, hne⟩
      · exact .inl ⟨h1, .inl rfl⟩
      · exact .inl ⟨h1, .inr ⟨hu, rfl⟩⟩
      · refine .inr ⟨by rw [Rgn.inst_free]; exact hfree, List.mem_map.mpr ⟨x₀, hmem, rfl⟩,
          fun hL => ?_⟩
        obtain ⟨hinj', hcl⟩ := hinj hL
        obtain ⟨_, hρϕ, _, _, _⟩ := hloan hL
        refine ⟨hinj'.ne_wr hcl hmem hρϕ (hne hL).1, fun hu he => ?_⟩
        exact (hne hL).2 hu (hinj' x₀ ρ hmem hρϕ he)
  | load ha hr hd _ ih =>
    have ha' := ha.inst θ
    rw [Ty.inst_ref] at ha'
    rw [snoc_inst] at ih
    exact .load ha' (fun h => List.mem_map.mpr ⟨_, hr h, rfl⟩) ((hΔ.dup _ θ).mpr hd) ih
  | tag ha hr hp _ ih =>
    have ha' := ha.inst θ
    rw [Ty.inst_ref] at ha'
    rw [snoc_inst, Ty.inst_int] at ih
    exact .tag ha' (fun h => List.mem_map.mpr ⟨_, hr h, rfl⟩) (hp.inst θ) ih
  | focus ha hr hp _ ih =>
    have ha' := ha.inst θ
    rw [Ty.inst_ref] at ha'
    rw [snoc_inst, Ty.inst_ref] at ih
    exact .focus ha' (fun h => List.mem_map.mpr ⟨_, hr h, rfl⟩) (hp.inst hΔ θ) ih
  | focusAt ha hix hr hu _ ih =>
    have ha' := ha.inst θ
    rw [Ty.inst_ref] at ha'
    have hix' := hix.inst θ
    rw [Ty.inst_int] at hix'
    rw [snoc_inst, Ty.inst_ref] at ih
    exact .focusAt ha' hix' (fun h => List.mem_map.mpr ⟨_, hr h, rfl⟩) (hu.inst hΔ θ) ih
  | store hform hlin _ ih =>
    have ha := hform.ref
    have hr := hform.region
    have hw := hform.write
    have hb := hform.value
    have ha' := ha.inst θ
    rw [Ty.inst_ref] at ha'
    rw [snoc_inst] at ih
    have hu : Ty.unit.inst θ = Ty.unit := by simp [Ty.unit, Ty.inst_tuple]
    rw [hu] at ih
    exact .store ⟨ha', (fun h => List.mem_map.mpr ⟨_, hr h, rfl⟩),
      (fun h => List.mem_map.mpr ⟨_, hw h, rfl⟩), (hb.inst θ)⟩ (hlin.inst hΔ θ) ih
  | swap hform hlin _ ih =>
    have ha := hform.ref
    have hr := hform.region
    have hw := hform.write
    have hb := hform.value
    have ha' := ha.inst θ
    rw [Ty.inst_ref] at ha'
    rw [snoc_inst] at ih
    exact .swap ⟨ha', (fun h => List.mem_map.mpr ⟨_, hr h, rfl⟩),
      (fun h => List.mem_map.mpr ⟨_, hw h, rfl⟩), (hb.inst θ)⟩ (hlin.inst hΔ θ) ih
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
