module

public import Glorious.Typing.Static

/-!
# Typing does not depend on which regions stand for a function's region variables

A function's body is typed once, with its regions as variables. Whatever
regions it is entered with, the same derivation types it with those regions in
place of the variables. So at run time every type is one whose regions are
cells, and nothing has to carry an assignment of regions to variables around.
-/

@[expose] public section

namespace Glorious.Typing

open Core

variable {Δ : Ctx}

theorem Rgn.mem_flat {l : List Rgn} {x : Rgn} : x ∈ Rgn.flat l ↔ ∃ r, r ∈ l ∧ x ∈ r.parts := by
  simp [Rgn.flat]

theorem Rgn.flat_cons (r : Rgn) (l : List Rgn) : Rgn.flat (r :: l) = r.parts ++ Rgn.flat l := by
  simp [Rgn.flat]

theorem Rgn.flat_append (a b : List Rgn) : Rgn.flat (a ++ b) = Rgn.flat a ++ Rgn.flat b := by
  simp [Rgn.flat]

theorem Rgn.flat_nil : Rgn.flat [] = [] := rfl

theorem Rgn.flat_cons_atom {x : Rgn} (h : x.atom = true) (l : List Rgn) :
    Rgn.flat (x :: l) = x :: Rgn.flat l := by
  rw [Rgn.flat_cons, Rgn.atom_parts h]
  rfl

theorem Rgn.atom_of_mem_flat {l : List Rgn} {x : Rgn} (h : x ∈ Rgn.flat l) : x.atom = true := by
  obtain ⟨r, _, hx⟩ := Rgn.mem_flat.mp h
  exact Rgn.mem_parts_atom hx

theorem Rgn.flat_of_atoms : ∀ {l : List Rgn}, (∀ x, x ∈ l → x.atom = true) → Rgn.flat l = l
  | [], _ => rfl
  | x :: l, h => by
    rw [Rgn.flat_cons_atom (h x (List.mem_cons_self ..)),
      Rgn.flat_of_atoms (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem Rgn.flat_flat (l : List Rgn) : Rgn.flat (Rgn.flat l) = Rgn.flat l :=
  Rgn.flat_of_atoms fun _ hx => Rgn.atom_of_mem_flat hx

theorem Rgn.mem_parts_inst {θ : List Rgn} {r x : Rgn} :
    x ∈ (r.inst θ).parts ↔ ∃ y, y ∈ r.parts ∧ x ∈ (y.inst θ).parts := by
  rw [Rgn.parts_inst]
  simp

theorem Rgn.flat_map_inst (θ : List Rgn) (l : List Rgn) :
    Rgn.flat (l.map (Rgn.inst θ)) = (Rgn.flat l).flatMap fun x => (x.inst θ).parts := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    rw [List.map_cons, Rgn.flat_cons, Rgn.flat_cons, ih, List.flatMap_append, Rgn.parts_inst]

theorem Rgn.mem_flat_inst {θ l : List Rgn} {x : Rgn} :
    x ∈ Rgn.flat (l.map (Rgn.inst θ)) ↔ ∃ y, y ∈ Rgn.flat l ∧ x ∈ (y.inst θ).parts := by
  rw [Rgn.flat_map_inst]
  simp

theorem Sub.refl (a : List Rgn) : Sub a a := fun _ h => h

theorem Sub.trans {a b c : List Rgn} (h₁ : Sub a b) (h₂ : Sub b c) : Sub a c :=
  fun r h => h₂ r (h₁ r h)

theorem Sub.inst {a b : List Rgn} (h : Sub a b) (θ : List Rgn) :
    Sub (a.map (Rgn.inst θ)) (b.map (Rgn.inst θ)) := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Rgn.mem_flat_inst.mp hx
  exact Rgn.mem_flat_inst.mpr ⟨y, h y hy, hxy⟩

theorem Sub.of_mem {a b : List Rgn} (h : ∀ r, r ∈ a → r ∈ b) : Sub a b := by
  intro x hx
  obtain ⟨r, hr, hx⟩ := Rgn.mem_flat.mp hx
  exact Rgn.mem_flat.mpr ⟨r, h r hr, hx⟩

theorem Sub.of_grants {a b : List Rgn} (h : ∀ r, r ∈ a → Grants b r) : Sub a b := by
  intro x hx
  obtain ⟨r, hr, hx⟩ := Rgn.mem_flat.mp hx
  exact h r hr x hx

theorem Sub.grants {a b : List Rgn} (h : Sub a b) {r : Rgn} (hr : r ∈ a) : Grants b r :=
  fun x hx => h x (Rgn.mem_flat.mpr ⟨r, hr, hx⟩)

theorem Grants.sub {a b : List Rgn} {r : Rgn} (h : Grants a r) (hs : Sub a b) : Grants b r :=
  fun x hx => hs x (h x hx)

theorem Grants.of_mem {ϕ : List Rgn} {r : Rgn} (h : r ∈ ϕ) : Grants ϕ r :=
  fun _ hx => Rgn.mem_flat.mpr ⟨r, h, hx⟩

theorem Grants.inst {ϕ : List Rgn} {r : Rgn} (h : Grants ϕ r) (θ : List Rgn) :
    Grants (ϕ.map (Rgn.inst θ)) (r.inst θ) := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Rgn.mem_parts_inst.mp hx
  exact Rgn.mem_flat_inst.mpr ⟨y, h y hy, hxy⟩

/-- A part of what is granted is granted. -/
theorem Grants.part {ϕ : List Rgn} {x : Rgn} (h : x ∈ Rgn.flat ϕ) : Grants ϕ x := by
  intro y hy
  obtain ⟨r, hr, hx⟩ := Rgn.mem_flat.mp h
  rw [Rgn.parts_of_mem hx] at hy
  rw [List.mem_singleton.mp hy]
  exact Rgn.mem_flat.mpr ⟨r, hr, hx⟩

theorem Widen.inst {τ τ' : Ty} (h : Widen τ τ') (θ : List Rgn) : Widen (τ.inst θ) (τ'.inst θ) := by
  cases h with
  | refl => exact .refl
  | ref hp =>
    rw [Ty.inst_ref, Ty.inst_ref]
    refine .ref fun x hx => ?_
    obtain ⟨y, hy, hxy⟩ := Rgn.mem_parts_inst.mp hx
    exact Rgn.mem_parts_inst.mpr ⟨y, hp y hy, hxy⟩

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

/-- Different places among `ϕ` stay apart when `θ` is put in: what each
becomes is made of different places, none of them those of another. -/
def InjOn (ϕ θ : List Rgn) : Prop :=
  (∀ x, x ∈ Rgn.flat ϕ → ((x.inst θ).parts).Nodup)
    ∧ ∀ x y, x ∈ Rgn.flat ϕ → y ∈ Rgn.flat ϕ → ∀ z, z ∈ (x.inst θ).parts → z ∈ (y.inst θ).parts →
      x = y

theorem InjOn.mono {ϕ ϕ' θ : List Rgn} (h : InjOn ϕ θ) (hsub : Sub ϕ' ϕ) : InjOn ϕ' θ :=
  ⟨fun x hx => h.1 x (hsub x hx), fun x y hx hy => h.2 x y (hsub x hx) (hsub y hy)⟩

/-- A list without repeats whose items are sent to lists without repeats, no
two of them sharing an item, gives a list without repeats. -/
theorem nodup_flatMap_of {L : List Rgn} {f : Rgn → List Rgn} (hL : L.Nodup)
    (hf : ∀ x, x ∈ L → (f x).Nodup)
    (hd : ∀ x y, x ∈ L → y ∈ L → ∀ z, z ∈ f x → z ∈ f y → x = y) : (L.flatMap f).Nodup := by
  induction L with
  | nil => simp
  | cons a L ih =>
    obtain ⟨ha, hL⟩ := List.nodup_cons.mp hL
    rw [List.flatMap_cons]
    refine List.nodup_append.mpr ⟨hf a (List.mem_cons_self ..),
      ih hL (fun x hx => hf x (List.mem_cons_of_mem _ hx))
        (fun x y hx hy => hd x y (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ hy)), ?_⟩
    intro z hz z' hz' hzz
    subst hzz
    obtain ⟨y, hy, hzy⟩ := List.mem_flatMap.mp hz'
    have := hd a y (List.mem_cons_self ..) (List.mem_cons_of_mem _ hy) z hz hzy
    subst this
    exact ha hy

/-- A list without repeats, of regions that stay apart, has none afterwards. -/
theorem InjOn.nodup {ϕ θ : List Rgn} (h : InjOn ϕ θ) {l : List Rgn} (hsub : Sub l ϕ)
    (hnd : (Rgn.flat l).Nodup) : (Rgn.flat (l.map (Rgn.inst θ))).Nodup := by
  rw [Rgn.flat_map_inst]
  exact nodup_flatMap_of hnd (fun x hx => h.1 x (hsub x hx))
    (fun x y hx hy => h.2 x y (hsub x hx) (hsub y hy))

/-- The same when some of the list is bound, which instantiating leaves alone. -/
theorem InjOn.nodup_scope {ϕ θ : List Rgn} (h : InjOn ϕ θ) {l : List Rgn}
    (hin : ∀ x, x ∈ l → (∀ y, y ∈ x.parts → y.free = false) ∨ Grants ϕ x)
    (hnd : (Rgn.flat l).Nodup) : (Rgn.flat (l.map (Rgn.inst θ))).Nodup := by
  rw [Rgn.flat_map_inst]
  -- Each place of the list is bound, and left alone, or one of `ϕ`'s.
  have hcase : ∀ y, y ∈ Rgn.flat l →
      (y.free = false ∧ (y.inst θ).parts = [y]) ∨ (y ∈ Rgn.flat ϕ) := by
    intro y hy
    obtain ⟨x, hx, hyx⟩ := Rgn.mem_flat.mp hy
    rcases hin x hx with hb | hg
    · have hf := hb y hyx
      refine .inl ⟨hf, ?_⟩
      rw [Rgn.inst_atom_bound (Rgn.mem_parts_atom hyx) hf, Rgn.parts_of_mem hyx]
    · exact .inr (hg y hyx)
  -- What a free place becomes has only free parts.
  have hfree : ∀ y z : Rgn, y.free = true → z ∈ (y.inst θ).parts → z.free = true := fun y z hy hz =>
    Rgn.free_of_mem_parts hz (by rw [Rgn.inst_free]; exact hy)
  refine nodup_flatMap_of hnd (fun y hy => ?_) (fun x y hx hy z hzx hzy => ?_)
  · rcases hcase y hy with ⟨_, he⟩ | hm
    · rw [he]; simp
    · exact h.1 y hm
  · rcases hcase x hx with ⟨hfx, hex⟩ | hmx <;> rcases hcase y hy with ⟨hfy, hey⟩ | hmy
    · rw [hex] at hzx; rw [hey] at hzy
      rw [List.mem_singleton.mp hzx] at hzy
      exact List.mem_singleton.mp hzy
    · rw [hex] at hzx
      rw [List.mem_singleton.mp hzx] at hzy
      cases hfy' : y.free
      · have hya : y.atom = true := by
          obtain ⟨r, _, hyr⟩ := Rgn.mem_flat.mp hmy
          exact Rgn.mem_parts_atom hyr
        rw [Rgn.inst_atom_bound hya hfy', Rgn.atom_parts hya] at hzy
        exact List.mem_singleton.mp hzy
      · have := hfree y x hfy' hzy
        rw [hfx] at this
        cases this
    · rw [hey] at hzy
      rw [List.mem_singleton.mp hzy] at hzx
      cases hfx' : x.free
      · have hxa : x.atom = true := by
          obtain ⟨r, _, hxr⟩ := Rgn.mem_flat.mp hmx
          exact Rgn.mem_parts_atom hxr
        rw [Rgn.inst_atom_bound hxa hfx', Rgn.atom_parts hxa] at hzx
        exact (List.mem_singleton.mp hzx).symm
      · have := hfree x y hfx' hzx
        rw [hfy] at this
        cases this
    · exact h.2 x y hmx hmy z hzx hzy

/-- A part of what a part becomes that is leave to write comes from leave to
write. -/
theorem Rgn.inst_atom_wr {θ : List Rgn} {y w : Rgn} (hy : y.atom = true)
    (h : Rgn.wr w ∈ (y.inst θ).parts) : ∃ v, y = .wr v ∧ w ∈ (v.inst θ).parts := by
  cases y with
  | var i => exact absurd rfl (Rgn.inst_var_parts h w)
  | wr v =>
    simp only [Rgn.inst, Rgn.parts, List.mem_map] at h
    obtain ⟨u, hu, he⟩ := h
    cases he
    exact ⟨v, rfl, hu⟩
  | or a b => cases hy
  | _ => simp [Rgn.inst, Rgn.parts] at h

theorem Rgn.openAt_atom_wr {d : Nat} {rs : List Rgn} {y w : Rgn} (hy : y.atom = true)
    (h : Rgn.wr w ∈ (y.openAt d rs).parts) : ∃ v, y = .wr v ∧ w ∈ (v.openAt d rs).parts := by
  cases y with
  | bound j =>
    by_cases hj : j < d
    · simp [Rgn.openAt, hj, Rgn.parts] at h
    · cases hr : rs[j - d]? with
      | none => simp [Rgn.openAt, hj, hr, Rgn.parts] at h
      | some r =>
        have hc : (Rgn.bound j).openAt d rs = Rgn.clean (some r) := by simp [Rgn.openAt, hj, hr]
        rw [hc] at h
        exact absurd rfl (Rgn.place_parts (Rgn.clean_place _) h w)
  | wr v =>
    simp only [Rgn.openAt, Rgn.parts, List.mem_map] at h
    obtain ⟨u, hu, he⟩ := h
    cases he
    exact ⟨v, rfl, hu⟩
  | or a b => cases hy
  | _ => simp [Rgn.openAt, Rgn.parts] at h

/-- Among places that stay apart and say that what may be written may be
read, nothing becomes leave to write a part of `ρ` that was not. -/
theorem InjOn.apart_wr {ϕ θ : List Rgn} (h : InjOn ϕ θ) (hc : closed ϕ = true) {x ρ : Rgn}
    (hx : Grants ϕ x) (hρ : Grants ϕ ρ) (hne : ∀ y, y ∈ x.parts → y ∉ (Rgn.wr ρ).parts) :
    ∀ y, y ∈ (x.inst θ).parts → y ∉ (Rgn.wr (ρ.inst θ)).parts := by
  intro y hy hyw
  obtain ⟨y₀, hy₀, hyy⟩ := Rgn.mem_parts_inst.mp hy
  simp only [Rgn.parts, List.mem_map] at hyw
  obtain ⟨w, hw, rfl⟩ := hyw
  obtain ⟨v, rfl, hwv⟩ := Rgn.inst_atom_wr (Rgn.mem_parts_atom hy₀) hyy
  obtain ⟨u, hu, hwu⟩ := Rgn.mem_parts_inst.mp hw
  have hv : v ∈ Rgn.flat ϕ := closed_mem hc (hx _ hy₀)
  have huv := h.2 v u hv (hρ u hu) w hwv hwu
  subst huv
  exact hne _ hy₀ (List.mem_map.mpr ⟨v, hu, rfl⟩)

/-- Nor does anything become a part of `ρ` that was not. -/
theorem InjOn.apart {ϕ θ : List Rgn} (h : InjOn ϕ θ) {x ρ : Rgn} (hx : Grants ϕ x)
    (hρ : Grants ϕ ρ) (hne : ∀ y, y ∈ x.parts → y ∉ ρ.parts) :
    ∀ y, y ∈ (x.inst θ).parts → y ∉ (ρ.inst θ).parts := by
  intro y hy hyρ
  obtain ⟨a, ha, hya⟩ := Rgn.mem_parts_inst.mp hy
  obtain ⟨b, hb, hyb⟩ := Rgn.mem_parts_inst.mp hyρ
  have := h.2 a b (hx a ha) (hρ b hb) y hya hyb
  subst this
  exact hne a ha hb

/-- What a list without repeats says of the lists it was put together from. -/
theorem nodup_flatMap_inv {L : List Rgn} {f : Rgn → List Rgn} (h : (L.flatMap f).Nodup) :
    (∀ x, x ∈ L → (f x).Nodup) ∧ ∀ x y, x ∈ L → y ∈ L → ∀ z, z ∈ f x → z ∈ f y → x = y := by
  induction L with
  | nil => exact ⟨fun _ hx => (by cases hx), fun _ _ hx => (by cases hx)⟩
  | cons a L ih =>
    rw [List.flatMap_cons] at h
    obtain ⟨ha, hL, hd⟩ := List.nodup_append.mp h
    obtain ⟨ih1, ih2⟩ := ih hL
    refine ⟨fun x hx => ?_, fun x y hx hy z hzx hzy => ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact ha
      · exact ih1 x hx
    · rcases List.mem_cons.mp hx with hxa | hxL
      · rcases List.mem_cons.mp hy with hya | hyL
        · rw [hxa, hya]
        · subst hxa
          exact absurd rfl (hd z hzx z (List.mem_flatMap.mpr ⟨y, hyL, hzy⟩))
      · rcases List.mem_cons.mp hy with hya | hyL
        · subst hya
          exact absurd rfl (hd z hzy z (List.mem_flatMap.mpr ⟨x, hxL, hzx⟩))
        · exact ih2 x y hxL hyL z hzx hzy

/-- Places whose images do not repeat stay apart. -/
theorem InjOn.of_nodup {θ l : List Rgn} (h : (Rgn.flat (l.map (Rgn.inst θ))).Nodup) : InjOn l θ := by
  rw [Rgn.flat_map_inst] at h
  exact nodup_flatMap_inv h

theorem Rgn.flat_map_openAt (d : Nat) (rs l : List Rgn) :
    Rgn.flat (l.map (Rgn.openAt d rs)) = (Rgn.flat l).flatMap fun y => (y.openAt d rs).parts := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    rw [List.map_cons, Rgn.flat_cons, Rgn.flat_cons, ih, List.flatMap_append, Rgn.parts_openAt]

/-- Opening keeps a list saying that what may be written may be read. -/
theorem closed_open {l : List Rgn} (h : closed l = true) (d : Nat) (rs : List Rgn) :
    closed (l.map (Rgn.openAt d rs)) = true := by
  refine List.all_eq_true.mpr fun x hx => ?_
  cases x with
  | wr z =>
    rw [Rgn.flat_map_openAt] at hx
    obtain ⟨y, hy, hzy⟩ := List.mem_flatMap.mp hx
    obtain ⟨r, _, hyr⟩ := Rgn.mem_flat.mp hy
    obtain ⟨v, rfl, hzv⟩ := Rgn.openAt_atom_wr (Rgn.mem_parts_atom hyr) hzy
    have hv := closed_mem h hy
    simpa [Rgn.flat_map_openAt] using List.mem_flatMap.mpr ⟨v, hv, hzv⟩
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
  | var h hw => exact .var (by simp [h]) (hw.inst θ)
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

theorem PartOk.inst (hΔ : Δ.Stable) (θ : List Rgn) : ∀ {σ : Ty} {path : List PathStep} {τ : Ty},
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
  | _, _, _, .variant hc hi hp =>
    .variant (hc.inst hΔ θ) (by simp [hi]) (PartOk.inst hΔ θ hp)

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
    exact hsub.inst θ
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
      exact hacc.inst θ
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
      exact hacc.inst θ
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
      exact hacc.inst θ
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
      exact hacc.inst θ
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
      (hok.inst hΔ θ fun hL => (hinj hL).1.mono hΦ), hrow', (hacc.inst θ), (hΦ.inst θ),
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
      (hok.inst hΔ θ fun hL => (hinj hL).1.mono hΦ), hrow', (hacc.inst θ), (hΦ.inst θ),
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
      · exact .inr ⟨by rw [Rgn.inst_free]; exact hfree, hmem.inst θ⟩
    · intro hL
      refine (hinj hL).1.nodup_scope (fun x hx => ?_) (hnd hL)
      rcases hacc x hx with ⟨_, rfl⟩ | ⟨_, hmem⟩
      · exact .inl fun y hy => by simp [Rgn.parts] at hy; subst hy; rfl
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
      · exact .inr ⟨by rw [Rgn.inst_free]; exact hfree, hmem.inst θ⟩
    · intro hL
      refine (hinj hL).1.nodup_scope (fun x hx => ?_) (hnd hL)
      rcases hacc x hx with ⟨_, rfl⟩ | ⟨_, hmem⟩
      · exact .inl fun y hy => by simp [Rgn.parts] at hy; subst hy; rfl
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
    exact .guard ⟨hc', ht', (Row.le_inst hrow θ), (haccc.inst θ), (hacc.inst θ),
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
    exact .guardTail ⟨hc', ht', (Row.le_inst hrow θ), (haccc.inst θ), (hacc.inst θ),
      (fun hL => ⟨(hinj hL).1.nodup haccc (hnd hL).1, (hinj hL).1.nodup hacc (hnd hL).2⟩)⟩
      (hlin.inst hΔ θ)
  | cancel hk hrow hacc hlin _ ih =>
    have hk' := hk.inst θ
    simp only [Ty.inst_fn, List.map_cons, List.map_nil] at hk'
    rw [snoc_inst] at ih
    have hu : Ty.unit.inst θ = Ty.unit := by simp [Ty.unit, Ty.inst_tuple]
    rw [hu] at ih
    exact .cancel hk' (Row.le_inst hrow θ) (hacc.inst θ) (hlin.inst hΔ θ) ih
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
      · exact .inr ⟨by rw [Rgn.inst_free]; exact hfree, hmem.inst θ⟩
    · intro hL
      refine (hinj hL).1.nodup_scope (fun x hx => ?_) (hnd hL)
      rcases hacc x hx with ⟨_, rfl | rfl⟩ | ⟨_, hmem⟩
      · exact .inl fun y hy => by simp [Rgn.parts] at hy; subst hy; rfl
      · exact .inl fun y hy => by simp [Rgn.parts] at hy; subst hy; rfl
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
      · exact .inr ⟨by rw [Rgn.inst_free]; exact hfree, hmem.inst θ⟩
    · intro hL
      refine (hinj hL).1.nodup_scope (fun x hx => ?_) (hnd hL)
      rcases hacc x hx with ⟨_, rfl | rfl⟩ | ⟨_, hmem⟩
      · exact .inl fun y hy => by simp [Rgn.parts] at hy; subst hy; rfl
      · exact .inl fun y hy => by simp [Rgn.parts] at hy; subst hy; rfl
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
    · exact fun hR => (hreg hR).inst θ
    · intro hL
      obtain ⟨h1, hρϕ, hw, hnd, hquiet⟩ := hloan hL
      refine ⟨h1, hρϕ.inst θ, fun hu => (hw hu).inst θ, ?_, by rw [hquiet, Row.inst_nil]⟩
      refine (hinj hL).1.nodup_scope (fun x hx => ?_) hnd
      rcases hacc x hx with ⟨_, rfl | ⟨_, rfl⟩⟩ | ⟨_, hmem, _⟩
      · exact .inl fun y hy => by simp [Rgn.parts] at hy; subst hy; rfl
      · exact .inl fun y hy => by simp [Rgn.parts] at hy; subst hy; rfl
      · exact .inr hmem
    · intro x hx
      obtain ⟨x₀, hx₀, rfl⟩ := List.mem_map.mp hx
      rcases hacc x₀ hx₀ with ⟨h1, rfl | ⟨hu, rfl⟩⟩ | ⟨hfree, hmem, hne⟩
      · exact .inl ⟨h1, .inl rfl⟩
      · exact .inl ⟨h1, .inr ⟨hu, rfl⟩⟩
      · refine .inr ⟨by rw [Rgn.inst_free]; exact hfree, hmem.inst θ, fun hL y hy => ?_⟩
        obtain ⟨hinj', hcl⟩ := hinj hL
        obtain ⟨_, hρϕ, _, _, _⟩ := hloan hL
        exact ⟨hinj'.apart_wr hcl hmem hρϕ (fun z hz => ((hne hL) z hz).1) y hy,
          fun hu => hinj'.apart hmem hρϕ (fun z hz => ((hne hL) z hz).2 hu) y hy⟩
  | load ha hr hd _ ih =>
    have ha' := ha.inst θ
    rw [Ty.inst_ref] at ha'
    rw [snoc_inst] at ih
    exact .load ha' (fun h => (hr h).inst θ) ((hΔ.dup _ θ).mpr hd) ih
  | tag ha hr hp _ ih =>
    have ha' := ha.inst θ
    rw [Ty.inst_ref] at ha'
    rw [snoc_inst, Ty.inst_int] at ih
    exact .tag ha' (fun h => (hr h).inst θ) (hp.inst θ) ih
  | focus ha hr hp _ ih =>
    have ha' := ha.inst θ
    rw [Ty.inst_ref] at ha'
    rw [snoc_inst, Ty.inst_ref] at ih
    exact .focus ha' (fun h => (hr h).inst θ) (hp.inst hΔ θ) ih
  | focusIn ha hr hc hi _ ih =>
    have ha' := ha.inst θ
    rw [Ty.inst_ref] at ha'
    rw [snoc_inst, Ty.inst_ref] at ih
    exact .focusIn ha' (fun h => (hr h).inst θ) (hc.inst hΔ θ) (by simp [hi]) ih
  | focusAt ha hix hr hu _ ih =>
    have ha' := ha.inst θ
    rw [Ty.inst_ref] at ha'
    have hix' := hix.inst θ
    rw [Ty.inst_int] at hix'
    rw [snoc_inst, Ty.inst_ref] at ih
    exact .focusAt ha' hix' (fun h => (hr h).inst θ) (hu.inst hΔ θ) ih
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
    exact .store ⟨ha', (fun h => (hr h).inst θ),
      (fun h => (hw h).inst θ), (hb.inst θ)⟩ (hlin.inst hΔ θ) ih
  | swap hform hlin _ ih =>
    have ha := hform.ref
    have hr := hform.region
    have hw := hform.write
    have hb := hform.value
    have ha' := ha.inst θ
    rw [Ty.inst_ref] at ha'
    rw [snoc_inst] at ih
    exact .swap ⟨ha', (fun h => (hr h).inst θ),
      (fun h => (hw h).inst θ), (hb.inst θ)⟩ (hlin.inst hΔ θ) ih
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
