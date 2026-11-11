import Glorious.Typing.Stack

/-!
# Type safety for Core

A well-typed machine state steps to a well-typed state, or halts, or is one of
the four faults in `Fault`. So a well-typed program that goes wrong went wrong
by one of those, and by nothing else: `type_safety`.

If the context's notion of a duplicable type is sound, the same steps keep every
resumption held in at most one place, so a resumption is never used a second
time: `owned_safety` leaves three faults.
-/

namespace Glorious.Typing

open Core

variable {Δ : Ctx}

/-! ## Evaluating what a computation applies -/

/-- The callee of a typed call evaluates, and is typed at the callable's result
and operations. It holds what the locals naming the callable and its arguments hold. -/
theorem evalCall_ok {S : StoreTy} {env : Env} {Γ : TEnv} {f : Atom} {args : List Atom}
    {Ps : List Ty} {σ : Ty} {ε : Row} {once : Bool} {fenv : Option (List Ty)}
    (henv : HasVals Δ S env Γ) (hf : HasAtom Γ f (.fn Ps σ ε once fenv)) (hargs : HasAtoms Γ args Ps) :
    ∃ c, evalCall env f args = some c ∧ CalleeOk Δ S c σ ε
      ∧ (∀ id v, c = .cont id v → f.eval env = some (.cont id))
      ∧ (∀ id v, c = .label id v → f.eval env = some (.label id))
      ∧ (∀ id, occCallee id c = sumAt id env (atomVars (f :: args))) := by
  obtain ⟨fv, hfv, hft⟩ := atom_ok henv hf
  obtain ⟨vs, hvs, hvst⟩ := atoms_ok henv hargs
  have hocc : ∀ id, occ id fv + occs id vs = sumAt id env (atomVars (f :: args)) := fun id => by
    simpa [occs] using occs_evalAtoms id env (f :: args) (vs := fv :: vs)
      (by simp [evalAtoms, hfv, hvs])
  rcases hft.fn_inv with ⟨fn, caps, Cs, rfl, hsig, hcaps⟩ | ⟨id, o, rfl, he, hk⟩
    | ⟨id, τ, rfl, he, hlab⟩
  · exact ⟨.fn fn caps vs, by simp [evalCall, hfv, hvs],
      .fn (sig := ⟨Cs, Ps, σ, ε⟩) hsig hcaps hvst, (fun _ _ h => by cases h),
      (fun _ _ h => by cases h), fun id => by rw [← hocc id]; simp [occCallee, occ]⟩
  · subst he
    cases hvst with
    | cons hv hnil =>
      cases hnil
      exact ⟨.cont id _, by simp [evalCall, hfv, hvs], .cont hk hv,
        (fun _ _ h => by cases h; exact hfv), (fun _ _ h => by cases h),
        fun id' => by rw [← hocc id']; simp [occCallee, occ, occs]⟩
  · subst he
    cases hvst with
    | cons hv hnil =>
      cases hnil
      exact ⟨.label id _, by simp [evalCall, hfv, hvs], .label hlab hv,
        (fun _ _ h => by cases h), (fun _ _ h => by cases h; exact hfv),
        fun id' => by rw [← hocc id']; simp [occCallee, occ, occs]⟩

/-- The callable a label scope runs evaluates, applied to the label. -/
theorem evalScope_ok {S : StoreTy} {env : Env} {Γ : TEnv} {thunk : Atom} {l : Value}
    {τl σ : Ty} {ε : Row} {once : Bool} {fenv : Option (List Ty)} (henv : HasVals Δ S env Γ)
    (hf : HasAtom Γ thunk (.fn [τl] σ ε once fenv)) (hl : HasVal Δ S l τl) :
    ∃ c, evalScope env thunk l = some c ∧ CalleeOk Δ S c σ ε
      ∧ (∀ id v, c = .cont id v → thunk.eval env = some (.cont id))
      ∧ (∀ id v, c = .label id v → thunk.eval env = some (.label id))
      ∧ (∀ id, occCallee id c = sumAt id env (atomVars [thunk]) + occ id l) := by
  obtain ⟨fv, hfv, hft⟩ := atom_ok henv hf
  have hocc : ∀ id, occ id fv = sumAt id env (atomVars [thunk]) := fun id => occ_eval id env hfv
  rcases hft.fn_inv with ⟨fn, caps, Cs, rfl, hsig, hcaps⟩ | ⟨id, o, rfl, he, hk⟩
    | ⟨id, τ, rfl, he, hlab⟩
  · exact ⟨.fn fn caps [l], by simp [evalScope, hfv],
      .fn (sig := ⟨Cs, [τl], σ, ε⟩) hsig hcaps (.cons hl .nil), (fun _ _ h => by cases h),
      (fun _ _ h => by cases h), fun id => by rw [← hocc id]; simp [occCallee, occ, occs]⟩
  · cases he
    exact ⟨.cont id l, by simp [evalScope, hfv], .cont hk hl,
      (fun _ _ h => by cases h; exact hfv), (fun _ _ h => by cases h),
      fun id' => by rw [← hocc id']; simp [occCallee, occ]⟩
  · cases he
    exact ⟨.label id l, by simp [evalScope, hfv], .label hlab hl,
      (fun _ _ h => by cases h), (fun _ _ h => by cases h; exact hfv),
      fun id' => by rw [← hocc id']; simp [occCallee, occ]⟩

/-- A callable that takes no arguments is a function. -/
theorem evalThunk_ok {S : StoreTy} {env : Env} {Γ : TEnv} {f : Atom} {σ : Ty} {ε : Row}
    {once : Bool} {fenv : Option (List Ty)} (henv : HasVals Δ S env Γ)
    (hf : HasAtom Γ f (.fn [] σ ε once fenv)) :
    ∃ fn caps Cs, evalCall env f [] = some (.fn fn caps []) ∧ f.eval env = some (.clo fn caps)
      ∧ Δ.fnSig fn ⟨Cs, [], σ, ε⟩ ∧ HasVals Δ S caps Cs := by
  obtain ⟨fv, hfv, hft⟩ := atom_ok henv hf
  rcases hft.fn_inv with ⟨fn, caps, Cs, rfl, hsig, hcaps⟩ | ⟨id, o, rfl, he, hk⟩
    | ⟨id, τ, rfl, he, hlab⟩
  · exact ⟨fn, caps, Cs, by simp [evalCall, evalAtoms, hfv], hfv, hsig, hcaps⟩
  · cases he
  · cases he

/-- What two operands hold is what each holds. -/
theorem sumAt_pair (id : Nat) (env : Env) (a b : Atom) :
    sumAt id env (atomVars [a, b]) = sumAt id env (atomVars [a]) + sumAt id env (atomVars [b]) := by
  cases a <;> cases b <;> simp [atomVars, sumAt]

/-- What a function value holds is what its captures hold. -/
theorem occs_clo (id : Nat) {env : Env} {f : Atom} {fn : Nat} {caps : List Value}
    (h : f.eval env = some (.clo fn caps)) : occs id caps = sumAt id env (atomVars [f]) := by
  simpa [occ] using occ_eval id env h

/-! ## Growing the store -/

theorem StoreOk.push_handler {S : StoreTy} {conts : Conts Frame} {labels : Nat} {cells : Cells}
    (hs : StoreOk Δ S ⟨conts, labels, cells⟩) (x : Ty × Row) :
    ∃ S', S.Le S' ∧ S'.handlers labels = some x ∧ StoreOk Δ S' ⟨conts, labels + 1, cells⟩ := by
  have hfresh : S.handlers labels = none := by
    cases h : S.handlers labels with
    | none => rfl
    | some y => exact absurd (hs.handlers _ _ h) (Nat.lt_irrefl _)
  let S' : StoreTy :=
    { S with handlers := fun i => if i = labels then some x else S.handlers i }
  have hle : S.Le S' := ⟨fun _ _ h => h, fun _ _ h => h, fun i y h => by
    show (if i = labels then some x else S.handlers i) = some y
    by_cases he : i = labels
    · subst he
      rw [hfresh] at h
      cases h
    · simp [he, h], fun _ _ h => h⟩
  refine ⟨S', hle, by show (if labels = labels then some x else _) = some x; simp, ?_⟩
  refine ⟨fun id o ρ ε₀ h => ?_, fun id τ h => ?_, fun id y h => ?_, fun a τ h => ?_⟩
  · obtain ⟨hlt, hseg⟩ := hs.conts id o ρ ε₀ h
    exact ⟨hlt, fun seg hg => (hseg seg hg).mono hle⟩
  · exact Nat.lt_succ_of_lt (hs.labels id τ h)
  · have h' : (if id = labels then some x else S.handlers id) = some y := h
    by_cases he : id = labels
    · subst he
      exact Nat.lt_succ_self _
    · simp [he] at h'
      exact Nat.lt_succ_of_lt (hs.handlers id y h')
  · obtain ⟨hlt, hv⟩ := hs.cells a τ h
    exact ⟨hlt, fun v hg => (hv v hg).mono hle⟩

theorem StoreOk.push_label {S : StoreTy} {conts : Conts Frame} {labels : Nat} {cells : Cells}
    (hs : StoreOk Δ S ⟨conts, labels, cells⟩) (x : Ty) :
    ∃ S', S.Le S' ∧ S'.labels labels = some x ∧ StoreOk Δ S' ⟨conts, labels + 1, cells⟩ := by
  have hfresh : S.labels labels = none := by
    cases h : S.labels labels with
    | none => rfl
    | some y => exact absurd (hs.labels _ _ h) (Nat.lt_irrefl _)
  let S' : StoreTy := { S with labels := fun i => if i = labels then some x else S.labels i }
  have hle : S.Le S' := ⟨fun _ _ h => h, fun i y h => by
    show (if i = labels then some x else S.labels i) = some y
    by_cases he : i = labels
    · subst he
      rw [hfresh] at h
      cases h
    · simp [he, h], fun _ _ h => h, fun _ _ h => h⟩
  refine ⟨S', hle, by show (if labels = labels then some x else _) = some x; simp, ?_⟩
  refine ⟨fun id o ρ ε₀ h => ?_, fun id y h => ?_, fun id τ h => ?_, fun a τ h => ?_⟩
  · obtain ⟨hlt, hseg⟩ := hs.conts id o ρ ε₀ h
    exact ⟨hlt, fun seg hg => (hseg seg hg).mono hle⟩
  · have h' : (if id = labels then some x else S.labels id) = some y := h
    by_cases he : id = labels
    · subst he
      exact Nat.lt_succ_self _
    · simp [he] at h'
      exact Nat.lt_succ_of_lt (hs.labels id y h')
  · exact Nat.lt_succ_of_lt (hs.handlers id τ h)
  · obtain ⟨hlt, hv⟩ := hs.cells a τ h
    exact ⟨hlt, fun v hg => (hv v hg).mono hle⟩

theorem StoreOk.push_cont {S : StoreTy} {conts : Conts Frame} {labels : Nat} {cells : Cells}
    {seg : List Frame} {o ρ : Ty} {ε₀ : Row} (hs : StoreOk Δ S ⟨conts, labels, cells⟩)
    (hk : ContOk Δ S seg o ρ ε₀) :
    ∃ S', S.Le S' ∧ S'.conts conts.length = some (o, ρ, ε₀)
      ∧ StoreOk Δ S' ⟨conts ++ [some seg], labels, cells⟩ := by
  have hfresh : S.conts conts.length = none := by
    cases h : S.conts conts.length with
    | none => rfl
    | some y =>
      obtain ⟨o', ρ', ε'⟩ := y
      exact absurd (hs.conts _ _ _ _ h).1 (Nat.lt_irrefl _)
  let S' : StoreTy :=
    { S with conts := fun i => if i = conts.length then some (o, ρ, ε₀) else S.conts i }
  have hle : S.Le S' := ⟨fun i y h => by
    show (if i = conts.length then some (o, ρ, ε₀) else S.conts i) = some y
    by_cases he : i = conts.length
    · subst he
      rw [hfresh] at h
      cases h
    · simp [he, h], fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩
  refine ⟨S', hle,
    by show (if conts.length = conts.length then some (o, ρ, ε₀) else _) = _; simp, ?_⟩
  refine ⟨fun id o' ρ' ε' h => ?_, hs.labels, hs.handlers, fun a τ h => ?_⟩
  · have h' : (if id = conts.length then some (o, ρ, ε₀) else S.conts id) = some (o', ρ', ε') := h
    by_cases he : id = conts.length
    · subst he
      simp at h'
      obtain ⟨rfl, rfl, rfl⟩ := h'
      refine ⟨by simp, fun seg' hg => ?_⟩
      simp at hg
      subst hg
      exact hk.mono hle
    · simp [he] at h'
      obtain ⟨hlt, hseg⟩ := hs.conts id o' ρ' ε' h'
      have hlt : id < conts.length := hlt
      refine ⟨(by simp; omega : id < (conts ++ [some seg]).length), fun seg' hg => ?_⟩
      rw [List.getElem?_append_left hlt] at hg
      exact (hseg seg' hg).mono hle
  · obtain ⟨hlt, hv⟩ := hs.cells a τ h
    exact ⟨hlt, fun v hg => (hv v hg).mono hle⟩

theorem StoreOk.push_cell {S : StoreTy} {conts : Conts Frame} {labels : Nat} {cells : Cells}
    {v : Value} {σ : Ty} (hs : StoreOk Δ S ⟨conts, labels, cells⟩) (hv : HasVal Δ S v σ) :
    ∃ S', S.Le S' ∧ S'.cells cells.length = some σ
      ∧ StoreOk Δ S' ⟨conts, labels, cells ++ [some v]⟩ := by
  have hfresh : S.cells cells.length = none := by
    cases h : S.cells cells.length with
    | none => rfl
    | some y => exact absurd (hs.cells _ _ h).1 (Nat.lt_irrefl _)
  let S' : StoreTy :=
    { S with cells := fun i => if i = cells.length then some σ else S.cells i }
  have hle : S.Le S' := ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun i y h => by
    show (if i = cells.length then some σ else S.cells i) = some y
    by_cases he : i = cells.length
    · subst he
      rw [hfresh] at h
      cases h
    · simp [he, h]⟩
  refine ⟨S', hle, by show (if cells.length = cells.length then some σ else _) = _; simp, ?_⟩
  refine ⟨fun id o ρ ε₀ h => ?_, hs.labels, hs.handlers, fun a τ h => ?_⟩
  · obtain ⟨hlt, hseg⟩ := hs.conts id o ρ ε₀ h
    exact ⟨hlt, fun seg hg => (hseg seg hg).mono hle⟩
  · have h' : (if a = cells.length then some σ else S.cells a) = some τ := h
    by_cases he : a = cells.length
    · subst he
      simp at h'
      subst h'
      refine ⟨by simp, fun w hg => ?_⟩
      simp at hg
      subst hg
      exact hv.mono hle
    · simp [he] at h'
      obtain ⟨hlt, hval⟩ := hs.cells a τ h'
      have hlt : a < cells.length := hlt
      refine ⟨(by simp; omega : a < (cells ++ [some v]).length), fun w hg => ?_⟩
      rw [List.getElem?_append_left hlt] at hg
      exact (hval w hg).mono hle

/-- Overwriting or freeing a cell keeps the store typed. -/
theorem StoreOk.set_cell {S : StoreTy} {conts : Conts Frame} {labels : Nat} {cells : Cells}
    {a : Nat} {τ : Ty} {x : Option Value} (hs : StoreOk Δ S ⟨conts, labels, cells⟩)
    (ha : S.cells a = some τ) (hx : ∀ v, x = some v → HasVal Δ S v τ) :
    StoreOk Δ S ⟨conts, labels, cells.set a x⟩ := by
  refine ⟨hs.conts, hs.labels, hs.handlers, fun a' τ' h => ?_⟩
  obtain ⟨hlt, hv⟩ := hs.cells a' τ' h
  refine ⟨by simpa using hlt, fun v hg => ?_⟩
  rw [List.getElem?_set] at hg
  by_cases he : a = a'
  · subst he
    rw [ha] at h
    cases h
    simp at hg
    exact hx v hg.2
  · simp [he] at hg
    exact hv v hg

/-! ## One step -/

/-- The outcome of a step from `s` is acceptable: a well-typed state, a result,
or no step at all because `s` is one of the faults. If duplicable types hold no
resumptions and no resumption was held twice before the step, none is after. -/
def StepOk (Δ : Ctx) (s : State) : Step State Value → Prop
  | .next s' => Typed Δ s' ∧ (DupSound Δ → Unique s → Unique s')
  | .halt _ => True
  | .stuck => Fault s

theorem StepOk.next {S : StoreTy} {s s' : State} (h : TypedAt Δ S s')
    (hu : DupSound Δ → Unique s → Unique s') : StepOk Δ s (.next s') :=
  ⟨⟨S, h⟩, hu⟩

/-- A step that enters code on a stack and leaves the resumptions alone. -/
theorem StepOk.of_safe {S : StoreTy} {s : State} {r : Step State Value} {b : Nat → Nat}
    {store : Store Frame} (h : Safe Δ S b store r) (hc : store.conts = s.store.conts)
    (hb : DupSound Δ → ∀ id, b id + occCells id store.cells
      ≤ occEnv id s.env (fv s.tm) + occStack id s.stack + occCells id s.store.cells) :
    StepOk Δ s r := by
  cases r with
  | next s' =>
    obtain ⟨ht, hk, hle⟩ := h
    refine ⟨⟨S, ht⟩, fun hD hu => hu.mono (by rw [hk.conts]; exact hc) fun id => ?_⟩
    have h1 := hle id
    have h2 := hb hD id
    have h3 := hk.cells id
    simp only [occState, hk.conts, hc]
    omega
  | halt v => exact True.intro
  | stuck => exact h.elim

/-- A step that makes a resumption out of `seg`. -/
theorem StepOk.of_safe_fresh {S : StoreTy} {s : State} {r : Step State Value} {b : Nat → Nat}
    {store : Store Frame} {seg : List Frame} (h : Safe Δ S b store r)
    (hc : store.conts = s.store.conts ++ [some seg])
    (hb : DupSound Δ → ∀ id, b id + occCells id store.cells + occStack id seg
      ≤ occEnv id s.env (fv s.tm) + occStack id s.stack + occCells id s.store.cells
        + (if s.store.conts.length = id then 1 else 0)) :
    StepOk Δ s r := by
  cases r with
  | next s' =>
    obtain ⟨ht, hk, hle⟩ := h
    refine ⟨⟨S, ht⟩, fun hD hu => hu.fresh (by rw [hk.conts]; exact hc) fun id => ?_⟩
    have h1 := hle id
    have h2 := hb hD id
    have h4 := hk.cells id
    simp only [occState, hk.conts, hc, occConts_push]
    omega
  | halt v => exact True.intro
  | stuck => exact h.elim

/-- A step that uses up resumption `k`, whose frames were `seg`. -/
theorem StepOk.of_safe_take {S : StoreTy} {s : State} {r : Step State Value} {b : Nat → Nat}
    {store : Store Frame} {k : Nat} {seg : List Frame} (h : Safe Δ S b store r)
    (hc : store.conts = s.store.conts.set k none) (hk : s.store.conts[k]? = some (some seg))
    (hb : DupSound Δ → ∀ id, b id + occCells id store.cells + (if k = id then 1 else 0)
      ≤ occEnv id s.env (fv s.tm) + occStack id s.stack + occCells id s.store.cells
        + occStack id seg) :
    StepOk Δ s r := by
  cases r with
  | next s' =>
    obtain ⟨ht, hkept, hle⟩ := h
    refine ⟨⟨S, ht⟩, fun hD hu => hu.take (by rw [hkept.conts]; exact hc) fun id => ?_⟩
    have h1 := hle id
    have h2 := hb hD id
    have h3 := occConts_take id hk
    have h4 := hkept.cells id
    simp only [occState, hkept.conts, hc]
    omega
  | halt v => exact True.intro
  | stuck => exact h.elim

/-- A step that applies a callee. -/
theorem StepOk.of_apply {p : Program} {S : StoreTy} {s : State} {c : Callee} {st : List Frame}
    {store : Store Frame}
    (h : ((∀ k v, c ≠ .cont k v)
          ∧ Safe Δ S (fun id => occCallee id c + occStack id st) store (apply p c st store))
        ∨ (∃ k v seg, c = .cont k v ∧ store.conts[k]? = some (some seg)
            ∧ Safe Δ S (fun id => occ id v + occStack id seg + occStack id st)
                ⟨store.conts.set k none, store.labels, store.cells⟩ (apply p c st store))
        ∨ (apply p c st store = .stuck ∧ Faulty st store c))
    (hc : store.conts = s.store.conts)
    (hb : DupSound Δ → ∀ id, occCallee id c + occStack id st + occCells id store.cells
      ≤ occEnv id s.env (fv s.tm) + occStack id s.stack + occCells id s.store.cells)
    (hf : Faulty st store c → Fault s) : StepOk Δ s (apply p c st store) := by
  rcases h with ⟨_, h⟩ | ⟨k, v, seg, rfl, hk, h⟩ | ⟨he, hfa⟩
  · exact .of_safe h hc hb
  · refine .of_safe_take h (by rw [← hc]) (by rw [← hc]; exact hk) (fun hD id => ?_)
    have := hb hD id
    simp only [occCallee] at this
    show occ id v + occStack id seg + occStack id st + occCells id store.cells
        + (if k = id then 1 else 0) ≤ _
    omega
  · rw [he]
    exact hf hfa

theorem Faulty.fault {s : State} {f : Atom} {c : Callee} {st : List Frame} {store : Store Frame}
    (hfa : Faulty st store c) (hcallee : calleeAtom s.tm = some f)
    (hk : ∀ id v, c = .cont id v → f.eval s.env = some (.cont id))
    (hl : ∀ id v, c = .label id v → f.eval s.env = some (.label id))
    (hstore : store.conts = s.store.conts)
    (hsub : ∀ id, findLabel Frame.asLabel id st = none →
      findLabel Frame.asLabel id s.stack = none) : Fault s := by
  cases hfa with
  | resumed h => exact .resumed hcallee (hk _ _ rfl) (hstore ▸ h)
  | dead h => exact .dead hcallee (hl _ _ rfl) (hsub _ h)

theorem mem_skip {a b c : List Nat} {i : Nat} (h : i ∈ a ++ c) : i ∈ a ++ (b ++ c) := by
  rcases List.mem_append.mp h with h | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (List.mem_append_right _ h)

/-- A well-typed state that is not at a host operation steps to a well-typed
state, halts, or is a fault. -/
theorem step_ok {p : Program} {S : StoreTy} {s : State} (hp : ProgramOk Δ p)
    (ht : TypedAt Δ S s) (hnh : ∀ id args body, s.tm ≠ .host id args body) :
    StepOk Δ s (step p s) := by
  obtain @⟨tm, env, stack, store, Γ, τ, ε, ε', henv, htm, hle, hst, hs⟩ := ht
  obtain ⟨conts, labels, cells⟩ := store
  cases htm with
  | @ret _ a _ _ ha =>
    obtain ⟨v, hv, hvt⟩ := atom_ok henv ha
    have h1 : step p ⟨.ret a, env, stack, ⟨conts, labels, cells⟩⟩
        = deliver p v stack ⟨conts, labels, cells⟩ := by simp [step, hv]
    rw [h1]
    refine .of_safe (deliver_safe hp hs hst hvt) rfl (fun hD id => ?_)
    have := occ_atom_le id (live := fv (.ret a)) hv (fun i hi => hi)
    dsimp only
    omega
  | @let_ _ rhs body σ _ _ hrhs hlin hbody =>
    rcases rhs_ok (S := S) henv hrhs with ⟨v, hv, hvt⟩ | ⟨q, args, m, n, rfl, hargs, hq, hnone⟩
    · have h1 : step p ⟨.let_ rhs body, env, stack, ⟨conts, labels, cells⟩⟩
          = .next ⟨body, env ++ [v], stack, ⟨conts, labels, cells⟩⟩ := by simp [step, hv]
      rw [h1]
      refine .next (.mk (henv.snoc hvt) hbody hle hst hs) (fun hD hu => hu.mono rfl fun id => ?_)
      have h2 := moved_live hD henv hlin (live := fv (.let_ rhs body))
        (fun i hi => by
          rcases List.mem_append.mp hi with h | h
          · exact List.mem_append_left _ (rhsMoves_sub h)
          · exact List.mem_append_right _ h) id
      have h3 := occEnv_push id env v (fv body)
      have h4 := rhs_occ hD henv hrhs hv id
      simp only [occState]
      omega
    · have h1 : step p ⟨.let_ (.prim q args) body, env, stack, ⟨conts, labels, cells⟩⟩
          = .stuck := by simp [step, hnone]
      rw [h1]
      exact Fault.overflow hargs hq
  | @call _ f args body Ps σ _ ε₁ _ once _ hf hargs hrow hlin hbody =>
    obtain ⟨c, hc, hcok, hck, hcl, hocc⟩ := evalCall_ok (S := S) henv hf hargs
    have h1 : step p ⟨.call f args body, env, stack, ⟨conts, labels, cells⟩⟩
        = apply p c (.call env body :: stack) ⟨conts, labels, cells⟩ := by simp [step, hc]
    rw [h1]
    refine .of_apply
      (apply_ok hp hs hcok (.call henv hbody hle hst) (Row.le_trans hrow hle)) rfl
      (fun hD id => ?_) (fun hfa => ?_)
    · have h2 := moved_live hD henv hlin (live := fv (.call f args body)) (fun i hi => hi) id
      simp only [hocc id, occStack, occFrame]
      omega
    · exact hfa.fault (s := ⟨.call f args body, env, stack, ⟨conts, labels, cells⟩⟩) rfl hck hcl
        rfl (fun _ h => findLabel_cons_none h)
  | @tail _ f args Ps _ ε₁ _ once _ hf hargs hrow hlin =>
    obtain ⟨c, hc, hcok, hck, hcl, hocc⟩ := evalCall_ok (S := S) henv hf hargs
    have h1 : step p ⟨.tail f args, env, stack, ⟨conts, labels, cells⟩⟩
        = apply p c stack ⟨conts, labels, cells⟩ := by simp [step, hc]
    rw [h1]
    refine .of_apply (apply_ok hp hs hcok hst (Row.le_trans hrow hle)) rfl
      (fun hD id => ?_) (fun hfa => ?_)
    · have h2 := moved_live hD henv hlin (live := fv (.tail f args))
        (fun i hi => by simpa [fv] using hi) id
      simp only [hocc id]
      omega
    · exact hfa.fault (s := ⟨.tail f args, env, stack, ⟨conts, labels, cells⟩⟩) rfl hck hcl
        rfl (fun _ h => h)
  | @callNever _ f args body Ps σ _ ε₁ _ once _ hf hargs hrow hlin hbody =>
    obtain ⟨c, hc, hcok, hck, hcl, hocc⟩ := evalCall_ok (S := S) henv hf hargs
    have h1 : step p ⟨.call f args body, env, stack, ⟨conts, labels, cells⟩⟩
        = apply p c (.call env body :: stack) ⟨conts, labels, cells⟩ := by simp [step, hc]
    rw [h1]
    refine .of_apply
      (apply_ok hp hs hcok (.never (.call henv hbody hle hst)) (Row.le_trans hrow hle)) rfl
      (fun hD id => ?_) (fun hfa => ?_)
    · have h2 := moved_live hD henv hlin (live := fv (.call f args body)) (fun i hi => hi) id
      simp only [hocc id, occStack, occFrame]
      omega
    · exact hfa.fault (s := ⟨.call f args body, env, stack, ⟨conts, labels, cells⟩⟩) rfl hck hcl
        rfl (fun _ h => findLabel_cons_none h)
  | @tailNever _ f args Ps _ ε₁ _ once _ hf hargs hrow hlin =>
    obtain ⟨c, hc, hcok, hck, hcl, hocc⟩ := evalCall_ok (S := S) henv hf hargs
    have h1 : step p ⟨.tail f args, env, stack, ⟨conts, labels, cells⟩⟩
        = apply p c stack ⟨conts, labels, cells⟩ := by simp [step, hc]
    rw [h1]
    refine .of_apply (apply_ok hp hs hcok (.never hst) (Row.le_trans hrow hle)) rfl
      (fun hD id => ?_) (fun hfa => ?_)
    · have h2 := moved_live hD henv hlin (live := fv (.tail f args))
        (fun i hi => by simpa [fv] using hi) id
      simp only [hocc id]
      omega
    · exact hfa.fault (s := ⟨.tail f args, env, stack, ⟨conts, labels, cells⟩⟩) rfl hck hcl
        rfl (fun _ h => h)
  | @handle _ ret ops captures thunk body Cs σ ρ _ εt H _ once _ hthunk hcaps hok hrow hlin hbody =>
    obtain ⟨caps, hcv, hcvt⟩ := atoms_ok (S := S) henv hcaps
    obtain ⟨fn, tcaps, TCs, hcall, hteval, hsig, htc⟩ := evalThunk_ok (S := S) henv hthunk
    have h1 : step p ⟨.handle ret ops captures thunk body, env, stack, ⟨conts, labels, cells⟩⟩
        = callFn p fn tcaps [] (.handler labels ⟨ret, ops, caps⟩ :: .call env body :: stack)
            ⟨conts, labels + 1, cells⟩ := by
      simp [step, hcv, hcall, apply]
    rw [h1]
    obtain ⟨S', hS, hid, hs'⟩ := hs.push_handler (ρ, ε)
    refine .of_safe (callFn_safe hp hsig (htc.mono hS) .nil hrow
      (.handler hid ⟨Cs, hcvt.mono hS, hok⟩ hle (.call (henv.mono hS) hbody hle (hst.mono hS)))
      hs') rfl (fun hD id => ?_)
    have h2 := moved_live hD henv hlin
      (live := fv (.handle ret ops captures thunk body)) (fun i hi => mem_skip hi) id
    have h3 : occs id caps = 0 := occs_dup hD id hcvt hok.dup
    have h4 := occs_clo id hteval
    simp only [occStack, occFrame, occs]
    omega
  | @handleTail _ ret ops captures thunk Cs σ _ εt H _ once _ hthunk hcaps hok hrow =>
    obtain ⟨caps, hcv, hcvt⟩ := atoms_ok (S := S) henv hcaps
    obtain ⟨fn, tcaps, TCs, hcall, hteval, hsig, htc⟩ := evalThunk_ok (S := S) henv hthunk
    have h1 : step p ⟨.handleTail ret ops captures thunk, env, stack, ⟨conts, labels, cells⟩⟩
        = callFn p fn tcaps [] (.handler labels ⟨ret, ops, caps⟩ :: stack)
            ⟨conts, labels + 1, cells⟩ := by
      simp [step, hcv, hcall, apply]
    rw [h1]
    obtain ⟨S', hS, hid, hs'⟩ := hs.push_handler (τ, ε)
    refine .of_safe (callFn_safe hp hsig (htc.mono hS) .nil hrow
      (.handler hid ⟨Cs, hcvt.mono hS, hok⟩ hle (hst.mono hS)) hs') rfl (fun hD id => ?_)
    have h2 := occ_atom_le id (live := fv (.handleTail ret ops captures thunk)) hteval
      (fun i hi => atomVars_head_sub hi)
    have h3 : occs id caps = 0 := occs_dup hD id hcvt hok.dup
    simp only [occ] at h2
    simp only [occStack, occFrame, occs]
    omega
  | @raise _ op args targs Ps _ _ hl hop hargs hlin =>
    obtain ⟨vs, hvs, hvst⟩ := atoms_ok (S := S) henv hargs
    obtain ⟨d, ρ, ε₀, εa, εb, Cs, Ps', r, hfind, hid, hcaps, hdup, hop', hale, hsig, hbelow, hble,
      hin, _⟩ := find_ok hst (hle _ _ hl)
    rw [hop] at hop'
    cases hop'
    have h1 : step p ⟨.raise op args, env, stack, ⟨conts, labels, cells⟩⟩
        = leave p (.handler d.id) (.invoke d.arm d.handler.caps vs) stack
            ⟨conts, labels, cells⟩ := by
      simp [step, hvs, hfind]
    rw [h1]
    refine .of_safe (leave_safe hp hs hst
      (.handler (sig := ⟨Cs, Ps, ρ, εa⟩) hid hsig hale hcaps hvst) hin) rfl (fun hD id => ?_)
    have h2 := moved_live hD henv hlin (live := fv (.raise op args))
      (fun i hi => by simpa [fv] using hi) id
    have h3 : occs id d.handler.caps = 0 := occs_dup hD id hcaps hdup
    have h4 := occs_evalAtoms id env args hvs
    simp only [occAfter]
    omega
  | @perform _ op args body targs Ps σ _ _ hl hop hargs hlin hbody =>
    obtain ⟨vs, hvs, hvst⟩ := atoms_ok (S := S) henv hargs
    obtain ⟨d, ρ, ε₀, εa, εb, Cs, Ps', r, hfind, hid, hcaps, hdup, hop', hale, hsig, hbelow, hble,
      _, hre⟩ := find_ok hst (hle _ _ hl)
    rw [hop] at hop'
    cases hop'
    have h1 : step p ⟨.perform op args body, env, stack, ⟨conts, labels, cells⟩⟩
        = callFn p d.arm d.handler.caps (vs ++ [.cont conts.length]) d.below
            ⟨conts ++ [some (.call env body :: d.above ++ [.handler d.id d.handler])],
              labels, cells⟩ := by
      simp [step, hvs, hfind]
    rw [h1]
    have hk : ContOk Δ S (.call env body :: d.above ++ [.handler d.id d.handler]) σ ρ ε₀ := by
      intro S' hS st' ε'' hst' hr
      refine ⟨ε', ?_⟩
      simpa using StackOk.call (henv.mono hS) hbody hle (hre S' hS st' ε'' hst' hr)
    obtain ⟨S', hS, hcont, hs'⟩ := hs.push_cont hk
    have hsig' : Δ.fnSig d.arm ⟨Cs, Ps ++ [.fn [σ] ρ ε₀ true none], ρ, εa⟩ := hsig
    refine .of_safe_fresh (callFn_safe hp hsig'
      (hcaps.mono hS) ((hvst.mono hS).snoc (.cont hcont)) (Row.le_trans hale hble)
      (hbelow.mono hS) hs') rfl (fun hD id => ?_)
    have h2 := moved_live hD henv hlin (live := fv (.perform op args body)) (fun i hi => hi) id
    have h3 : occs id d.handler.caps = 0 := occs_dup hD id hcaps hdup
    have h4 := occs_evalAtoms id env args hvs
    have h5 : occStack id stack
        = occStack id d.above + (occs id d.handler.caps + occStack id d.below) := by
      have := congrArg (occStack id) (findHandler_split hfind)
      simpa [occStack_append, occStack, occFrame] using this
    simp only [occs_append, occs, occ, occStack, occFrame, occStack_append]
    omega
  | @label _ thunk body σ ρ _ εl εt _ once once' _ hthunk hrow hlin hbody =>
    obtain ⟨S', hS, hlab, hs'⟩ := hs.push_label σ
    obtain ⟨c, hc, hcok, hck, hcl, hocc⟩ :=
      evalScope_ok (S := S') (l := .label labels) (henv.mono hS) hthunk (.label hlab)
    have h1 : step p ⟨.label thunk body, env, stack, ⟨conts, labels, cells⟩⟩
        = apply p c (.label labels :: .call env body :: stack) ⟨conts, labels + 1, cells⟩ := by
      simp [step, hc]
    rw [h1]
    refine .of_apply
      (apply_ok hp hs' hcok (.label hlab (.call (henv.mono hS) hbody hle (hst.mono hS)))
        (Row.le_trans hrow hle)) rfl (fun hD id => ?_) (fun hfa => ?_)
    · have h2 := moved_live hD henv hlin (live := fv (.label thunk body)) (fun i hi => hi) id
      simp only [hocc id, occ, occStack, occFrame]
      omega
    · exact hfa.fault (s := ⟨.label thunk body, env, stack, ⟨conts, labels, cells⟩⟩) rfl hck hcl
        rfl (fun _ h => findLabel_cons_none (findLabel_cons_none h))
  | @labelTail _ thunk ρ _ εl εt _ once once' _ hthunk hrow =>
    obtain ⟨S', hS, hlab, hs'⟩ := hs.push_label τ
    obtain ⟨c, hc, hcok, hck, hcl, hocc⟩ :=
      evalScope_ok (S := S') (l := .label labels) (henv.mono hS) hthunk (.label hlab)
    have h1 : step p ⟨.labelTail thunk, env, stack, ⟨conts, labels, cells⟩⟩
        = apply p c (.label labels :: stack) ⟨conts, labels + 1, cells⟩ := by
      simp [step, hc]
    rw [h1]
    refine .of_apply
      (apply_ok hp hs' hcok (.label hlab (hst.mono hS)) (Row.le_trans hrow hle)) rfl
      (fun hD id => ?_) (fun hfa => ?_)
    · have h2 := moved_live hD henv (Linear.single thunk) (live := fv (.labelTail thunk))
        (fun i hi => by simpa [fv] using hi) id
      simp only [hocc id, occ, occStack, occFrame]
      omega
    · exact hfa.fault (s := ⟨.labelTail thunk, env, stack, ⟨conts, labels, cells⟩⟩) rfl hck hcl
        rfl (fun _ h => findLabel_cons_none h)
  | @guard _ cleanup thunk body σc σ _ εt _ once once' _ _ hcl hthunk hrow hlin hbody =>
    obtain ⟨gfn, gcaps, GCs, _, hgev, hgsig, hgc⟩ := evalThunk_ok (S := S) henv hcl
    obtain ⟨fn, tcaps, TCs, hcall, hteval, hsig, htc⟩ := evalThunk_ok (S := S) henv hthunk
    have h1 : step p ⟨.guard cleanup thunk body, env, stack, ⟨conts, labels, cells⟩⟩
        = callFn p fn tcaps [] (.guard gfn gcaps :: .call env body :: stack)
            ⟨conts, labels, cells⟩ := by
      simp [step, evalClosure, hgev, hcall, apply]
    rw [h1]
    refine .of_safe (callFn_safe hp hsig htc .nil (Row.le_trans hrow hle)
      (.guard hgsig hgc (.call henv hbody hle hst)) hs) rfl (fun hD id => ?_)
    have h2 := moved_live hD henv hlin (live := fv (.guard cleanup thunk body))
      (fun i hi => hi) id
    have h3 := occs_evalAtoms id env [cleanup, thunk] (vs := [.clo gfn gcaps, .clo fn tcaps])
      (by simp [evalAtoms, hgev, hteval])
    simp only [occs, occ] at h3
    simp only [occStack, occFrame, occs]
    omega
  | @guardTail _ cleanup thunk σc _ εt _ once once' _ _ hcl hthunk hrow hlin =>
    obtain ⟨gfn, gcaps, GCs, _, hgev, hgsig, hgc⟩ := evalThunk_ok (S := S) henv hcl
    obtain ⟨fn, tcaps, TCs, hcall, hteval, hsig, htc⟩ := evalThunk_ok (S := S) henv hthunk
    have h1 : step p ⟨.guardTail cleanup thunk, env, stack, ⟨conts, labels, cells⟩⟩
        = callFn p fn tcaps [] (.guard gfn gcaps :: stack) ⟨conts, labels, cells⟩ := by
      simp [step, evalClosure, hgev, hcall, apply]
    rw [h1]
    refine .of_safe (callFn_safe hp hsig htc .nil (Row.le_trans hrow hle)
      (.guard hgsig hgc hst) hs) rfl (fun hD id => ?_)
    have h2 := moved_live hD henv hlin (live := fv (.guardTail cleanup thunk))
      (fun i hi => by simpa [fv] using hi) id
    have h3 := occs_evalAtoms id env [cleanup, thunk] (vs := [.clo gfn gcaps, .clo fn tcaps])
      (by simp [evalAtoms, hgev, hteval])
    simp only [occs, occ] at h3
    simp only [occStack, occFrame, occs]
    omega
  | @cancel _ k body σ ρ _ ε₁ _ once _ hk hrow hlin hbody =>
    obtain ⟨kv, hkv, hkt⟩ := atom_ok henv hk
    have hquiet : ∀ id, occState id ⟨body, env ++ [Value.unit], stack, ⟨conts, labels, cells⟩⟩
        ≤ occState id ⟨.cancel k body, env, stack, ⟨conts, labels, cells⟩⟩ := fun id => by
      have h2 := occEnv_push id env Value.unit (fv body)
      have h3 := occEnv_mono (id := id) (env := env) (a := fv body) (b := fv (.cancel k body))
        (fun i hi => List.mem_append_right _ hi)
      have h4 := occ_unit id
      simp only [occState]
      omega
    rcases hkt.fn_inv with ⟨fn, caps, Cs, rfl, _, _⟩ | ⟨id, o, rfl, he, hcont⟩
      | ⟨id, τl, rfl, _, _⟩
    · have h1 : step p ⟨.cancel k body, env, stack, ⟨conts, labels, cells⟩⟩
          = .next ⟨body, env ++ [Value.unit], stack, ⟨conts, labels, cells⟩⟩ := by
        simp [step, evalCont, hkv]
      rw [h1]
      exact .next (.mk (henv.snoc .unit) hbody hle hst hs) (fun _ hu => hu.mono rfl hquiet)
    · cases he
      obtain ⟨hlt, hseg⟩ := hs.conts id σ ρ ε₁ hcont
      cases hget : conts[id]? with
      | none => exact absurd hlt (by simpa using List.getElem?_eq_none_iff.mp hget)
      | some x =>
        cases x with
        | none =>
          have h1 : step p ⟨.cancel k body, env, stack, ⟨conts, labels, cells⟩⟩ = .stuck := by
            simp [step, evalCont, hkv, takeCont_none hget]
          rw [h1]
          exact Fault.resumed (s := ⟨.cancel k body, env, stack, ⟨conts, labels, cells⟩⟩)
            rfl hkv hget
        | some seg =>
          have h1 : step p ⟨.cancel k body, env, stack, ⟨conts, labels, cells⟩⟩
              = leave p (.label labels) (.yield Value.unit)
                  (seg ++ .yield Value.unit :: .label labels :: .call env body :: stack)
                  ⟨conts.set id none, labels + 1, cells⟩ := by
            simp [step, evalCont, hkv, takeCont_some hget]
          rw [h1]
          obtain ⟨S', hS, hlab, hs'⟩ := (hs.take id).push_label Ty.unit
          have hbase : StackOk Δ S'
              (.yield Value.unit :: .label labels :: .call env body :: stack) ρ ε' :=
            .yield .unit (.label hlab (.call (henv.mono hS) hbody hle (hst.mono hS)))
          obtain ⟨ε'', hst'⟩ := hseg seg hget S' hS _ ε' hbase (Row.le_trans hrow hle)
          refine .of_safe_take (leave_safe hp hs' hst' (.label hlab .unit)
            ⟨.label labels, by simp, by simp [Frame.isTarget]⟩) rfl hget (fun hD id' => ?_)
          have h2 := moved_live hD henv hlin (live := fv (.cancel k body)) (fun i hi => hi) id'
          have h3 := occ_eval id' env hkv
          have h4 := occ_unit id'
          simp only [occ] at h3
          simp only [occAfter, occStack_append, occStack, occFrame]
          omega
    · have h1 : step p ⟨.cancel k body, env, stack, ⟨conts, labels, cells⟩⟩
          = .next ⟨body, env ++ [Value.unit], stack, ⟨conts, labels, cells⟩⟩ := by
        simp [step, evalCont, hkv]
      rw [h1]
      exact .next (.mk (henv.snoc .unit) hbody hle hst hs) (fun _ hu => hu.mono rfl hquiet)
  | @cell _ init thunk body σ ρ _ εt _ once _ hinit hthunk hrow hlin hbody =>
    obtain ⟨v, hv, hvt⟩ := atom_ok henv hinit
    obtain ⟨S', hS, hcell, hs'⟩ := hs.push_cell hvt
    obtain ⟨c, hc, hcok, hck, hcl, hocc⟩ :=
      evalScope_ok (S := S') (l := .ref cells.length) (henv.mono hS) hthunk (.ref hcell)
    have h1 : step p ⟨.cell init thunk body, env, stack, ⟨conts, labels, cells⟩⟩
        = apply p c (.cell cells.length :: .call env body :: stack)
            ⟨conts, labels, cells ++ [some v]⟩ := by
      simp [step, hv, hc, Store.alloc]
    rw [h1]
    refine .of_apply
      (apply_ok hp hs' hcok (.cell (.call (henv.mono hS) hbody hle (hst.mono hS)))
        (Row.le_trans hrow hle)) rfl (fun hD id => ?_) (fun hfa => ?_)
    · have h2 := moved_live hD henv hlin (live := fv (.cell init thunk body)) (fun i hi => hi) id
      have h3 := sumAt_pair id env init thunk
      have h4 := occ_eval id env hv
      simp only [hocc id, occ, occStack, occFrame, occCells_push]
      omega
    · exact hfa.fault (s := ⟨.cell init thunk body, env, stack, ⟨conts, labels, cells⟩⟩) rfl hck
        hcl rfl (fun _ h => findLabel_cons_none (findLabel_cons_none h))
  | @cellTail _ init thunk σ _ εt _ once _ hinit hthunk hrow hlin =>
    obtain ⟨v, hv, hvt⟩ := atom_ok henv hinit
    obtain ⟨S', hS, hcell, hs'⟩ := hs.push_cell hvt
    obtain ⟨c, hc, hcok, hck, hcl, hocc⟩ :=
      evalScope_ok (S := S') (l := .ref cells.length) (henv.mono hS) hthunk (.ref hcell)
    have h1 : step p ⟨.cellTail init thunk, env, stack, ⟨conts, labels, cells⟩⟩
        = apply p c (.cell cells.length :: stack) ⟨conts, labels, cells ++ [some v]⟩ := by
      simp [step, hv, hc, Store.alloc]
    rw [h1]
    refine .of_apply
      (apply_ok hp hs' hcok (.cell (hst.mono hS)) (Row.le_trans hrow hle)) rfl
      (fun hD id => ?_) (fun hfa => ?_)
    · have h2 := moved_live hD henv hlin (live := fv (.cellTail init thunk))
        (fun i hi => by simpa [fv] using hi) id
      have h3 := sumAt_pair id env init thunk
      have h4 := occ_eval id env hv
      simp only [hocc id, occ, occStack, occFrame, occCells_push]
      omega
    · exact hfa.fault (s := ⟨.cellTail init thunk, env, stack, ⟨conts, labels, cells⟩⟩) rfl hck
        hcl rfl (fun _ h => findLabel_cons_none h)
  | @load _ a body σ _ _ ha hdup hbody =>
    obtain ⟨v, hv, hvt⟩ := atom_ok henv ha
    obtain ⟨addr, rfl, hcell⟩ := hvt.ref_inv
    obtain ⟨hlt, hval⟩ := hs.cells addr σ hcell
    cases hget : cells[addr]? with
    | none => exact absurd hlt (by simpa using List.getElem?_eq_none_iff.mp hget)
    | some x =>
      cases x with
      | none =>
        have h1 : step p ⟨.mem .load [a] body, env, stack, ⟨conts, labels, cells⟩⟩ = .stuck := by
          simp [step, evalAtoms, hv, MemOp.eval, hget]
        rw [h1]
        exact Fault.freed (a := addr) (vs := []) (by simp [evalAtoms, hv]) hget
      | some w =>
        have h1 : step p ⟨.mem .load [a] body, env, stack, ⟨conts, labels, cells⟩⟩
            = .next ⟨body, env ++ [w], stack, ⟨conts, labels, cells⟩⟩ := by
          simp [step, evalAtoms, hv, MemOp.eval, hget]
        rw [h1]
        refine .next (.mk (henv.snoc (hval w hget)) hbody hle hst hs)
          (fun hD hu => hu.mono rfl fun id => ?_)
        have h2 := occEnv_push id env w (fv body)
        have h3 := occEnv_mono (id := id) (env := env) (a := fv body)
          (b := fv (.mem .load [a] body)) (fun i hi => List.mem_append_right _ hi)
        have h4 := hD _ _ _ (hval w hget) hdup id
        simp only [occState]
        omega
  | @store _ a b body σ _ _ ha hb hlin hbody =>
    obtain ⟨v, hv, hvt⟩ := atom_ok henv ha
    obtain ⟨w, hw, hwt⟩ := atom_ok henv hb
    obtain ⟨addr, rfl, hcell⟩ := hvt.ref_inv
    obtain ⟨hlt, hval⟩ := hs.cells addr σ hcell
    cases hget : cells[addr]? with
    | none => exact absurd hlt (by simpa using List.getElem?_eq_none_iff.mp hget)
    | some x =>
      cases x with
      | none =>
        have h1 : step p ⟨.mem .store [a, b] body, env, stack, ⟨conts, labels, cells⟩⟩
            = .stuck := by
          simp [step, evalAtoms, hv, hw, MemOp.eval, hget]
        rw [h1]
        exact Fault.freed (a := addr) (vs := [w]) (by simp [evalAtoms, hv, hw]) hget
      | some old =>
        have h1 : step p ⟨.mem .store [a, b] body, env, stack, ⟨conts, labels, cells⟩⟩
            = .next ⟨body, env ++ [Value.unit], stack,
                ⟨conts, labels, cells.set addr (some w)⟩⟩ := by
          simp [step, evalAtoms, hv, hw, MemOp.eval, hget]
        rw [h1]
        refine .next (.mk (henv.snoc .unit) hbody hle hst
          (hs.set_cell hcell (fun u hu => by cases hu; exact hwt)))
          (fun hD hu => hu.mono rfl fun id => ?_)
        have h2 := moved_live hD henv hlin (live := fv (.mem .store [a, b] body))
          (fun i hi => by
            rcases List.mem_append.mp hi with h | h
            · exact List.mem_append_left _ (atomVars_tail_sub h)
            · exact List.mem_append_right _ h) id
        have h3 := occEnv_push id env Value.unit (fv body)
        have h4 := occ_eval id env hw
        have h5 := occCells_set id hget (some w)
        have h6 := occ_unit id
        simp only [oweight] at h5
        simp only [occState]
        omega
  | @swap _ a b body σ _ _ ha hb hlin hbody =>
    obtain ⟨v, hv, hvt⟩ := atom_ok henv ha
    obtain ⟨w, hw, hwt⟩ := atom_ok henv hb
    obtain ⟨addr, rfl, hcell⟩ := hvt.ref_inv
    obtain ⟨hlt, hval⟩ := hs.cells addr σ hcell
    cases hget : cells[addr]? with
    | none => exact absurd hlt (by simpa using List.getElem?_eq_none_iff.mp hget)
    | some x =>
      cases x with
      | none =>
        have h1 : step p ⟨.mem .swap [a, b] body, env, stack, ⟨conts, labels, cells⟩⟩
            = .stuck := by
          simp [step, evalAtoms, hv, hw, MemOp.eval, hget]
        rw [h1]
        exact Fault.freed (a := addr) (vs := [w]) (by simp [evalAtoms, hv, hw]) hget
      | some old =>
        have h1 : step p ⟨.mem .swap [a, b] body, env, stack, ⟨conts, labels, cells⟩⟩
            = .next ⟨body, env ++ [old], stack,
                ⟨conts, labels, cells.set addr (some w)⟩⟩ := by
          simp [step, evalAtoms, hv, hw, MemOp.eval, hget]
        rw [h1]
        refine .next (.mk (henv.snoc (hval old hget)) hbody hle hst
          (hs.set_cell hcell (fun u hu => by cases hu; exact hwt)))
          (fun hD hu => hu.mono rfl fun id => ?_)
        have h2 := moved_live hD henv hlin (live := fv (.mem .swap [a, b] body))
          (fun i hi => by
            rcases List.mem_append.mp hi with h | h
            · exact List.mem_append_left _ (atomVars_tail_sub h)
            · exact List.mem_append_right _ h) id
        have h3 := occEnv_push id env old (fv body)
        have h4 := occ_eval id env hw
        have h5 := occCells_set id hget (some w)
        simp only [oweight] at h5
        simp only [occState]
        omega
  | write _ _ => exact absurd rfl (hnh _ _ _)
  | read _ => exact absurd rfl (hnh _ _ _)

/-! ## Programs in their world -/

/-- The outcome of a step of a program in its world is acceptable. -/
def ConfigOk (Δ : Ctx) (c : Config) : Step Config Result → Prop
  | .next c' => Typed Δ c'.state ∧ (DupSound Δ → Unique c.state → Unique c'.state)
  | .halt _ => True
  | .stuck => Fault c.state

theorem stepIO_eq_lift {p : Program} {s : State} {w : World}
    (h : ∀ id args body, s.tm ≠ .host id args body) : stepIO p ⟨s, w⟩ = lift w (step p s) := by
  obtain ⟨tm, env, stack, store⟩ := s
  cases tm <;> first | rfl | exact absurd rfl (h _ _ _)

/-- A host step binds a value that holds no resumption. -/
theorem host_quiet {id : Nat} {args : List Atom} {body : Tm} {env : Env} {stack : List Frame}
    {store : Store Frame} {r : Value} (hr : ∀ k, occ k r = 0)
    (hu : Unique ⟨.host id args body, env, stack, store⟩) :
    Unique ⟨body, env ++ [r], stack, store⟩ :=
  hu.mono rfl fun k => by
    have h2 := occEnv_push k env r (fv body)
    have h3 := occEnv_mono (id := k) (env := env) (a := fv body)
      (b := fv (.host id args body)) (fun i hi => List.mem_append_right _ hi)
    have h4 := hr k
    simp only [occState]
    omega

/-- A well-typed program state in any world steps to a well-typed state, halts,
or is a fault. Reading and writing never fail. -/
theorem stepIO_ok {p : Program} {c : Config} (hp : ProgramOk Δ p) (ht : Typed Δ c.state) :
    ConfigOk Δ c (stepIO p c) := by
  obtain ⟨⟨tm, env, stack, store⟩, w⟩ := c
  obtain ⟨S, ht⟩ := ht
  by_cases hh : ∃ id args body, tm = .host id args body
  · obtain ⟨id, args, body, rfl⟩ := hh
    obtain @⟨_, _, _, _, Γ, τ, ε, ε', henv, htm, hle, hst, hs⟩ := ht
    cases htm with
    | @write _ a _ σ _ _ ha hbody =>
      obtain ⟨v, hv, hvt⟩ := atom_ok henv ha
      have h1 : stepIO p ⟨⟨.host 0 [a] body, env, stack, store⟩, w⟩
          = .next ⟨⟨body, env ++ [.data 0 []], stack, store⟩, ⟨w.input, w.output ++ [v]⟩⟩ := by
        simp [stepIO, evalAtoms, hv, Host.call]
      rw [h1]
      exact ⟨⟨S, .mk (henv.snoc .unit) hbody hle hst hs⟩,
        fun _ hu => host_quiet (fun k => by simp [occ, occs]) hu⟩
    | read hbody =>
      obtain ⟨input, output⟩ := w
      cases input with
      | nil =>
        exact ⟨⟨S, .mk (henv.snoc (.data (.inl ⟨rfl, rfl⟩) (.cons .int (.cons .int .nil))))
          hbody hle hst hs⟩, fun _ hu => host_quiet (fun k => by simp [occ, occs]) hu⟩
      | cons n rest =>
        exact ⟨⟨S, .mk (henv.snoc (.data (.inl ⟨rfl, rfl⟩) (.cons .int (.cons .int .nil))))
          hbody hle hst hs⟩, fun _ hu => host_quiet (fun k => by simp [occ, occs]) hu⟩
  · have hnh : ∀ id args body, tm ≠ .host id args body :=
      fun id args body h => hh ⟨id, args, body, h⟩
    have hstep := step_ok (s := ⟨tm, env, stack, store⟩) hp ht hnh
    rw [stepIO_eq_lift hnh]
    cases hr : step p ⟨tm, env, stack, store⟩ with
    | next s' =>
      rw [hr] at hstep
      exact hstep
    | halt v => exact True.intro
    | stuck =>
      rw [hr] at hstep
      exact hstep

/-! ## Whole runs -/

/-- The program about to start is well typed. -/
theorem typed_init {p : Program} (hp : ProgramOk Δ p) : Typed Δ (init p) := by
  obtain ⟨τ, hmain⟩ := hp.main
  refine ⟨⟨fun _ => none, fun _ => none, fun _ => none, fun _ => none⟩, ?_⟩
  refine .mk .nil hmain (Row.le_refl _) .nil ⟨?_, ?_, ?_, ?_⟩
  · intro _ _ _ _ h
    simp at h
  · intro _ _ h
    simp at h
  · intro _ _ h
    simp at h
  · intro _ _ h
    simp at h

/-- The program about to start holds no resumption. -/
theorem unique_init (p : Program) : Unique (init p) := fun id => by
  simp [occState, init, occEnv, total, occStack, occCells, occConts, osum]

/-- From a well-typed state, a run of any length is still going in a well-typed
state, or has halted, or stopped at a fault. Where no resumption is held twice
at the start, none is held twice at the state the run is in or stopped at. -/
theorem run_ok {p : Program} (hp : ProgramOk Δ p) : ∀ (n : Nat) {c : Config},
    Typed Δ c.state →
    (∃ c', Machine.run (stepIO p) n c = .next c' ∧ Typed Δ c'.state
        ∧ (DupSound Δ → Unique c.state → Unique c'.state))
      ∨ (∃ r, Machine.run (stepIO p) n c = .halt r)
      ∨ (∃ m c', m < n ∧ Machine.run (stepIO p) m c = .next c' ∧ stepIO p c' = .stuck
          ∧ Fault c'.state ∧ (DupSound Δ → Unique c.state → Unique c'.state)) := by
  intro n
  induction n with
  | zero => intro c ht; exact .inl ⟨c, rfl, ht, fun _ hu => hu⟩
  | succ n ih =>
    intro c ht
    have hstep := stepIO_ok hp ht
    cases hr : stepIO p c with
    | next c₁ =>
      rw [hr] at hstep
      obtain ⟨ht₁, hu₁⟩ := hstep
      have hrun : ∀ k, Machine.run (stepIO p) (k + 1) c = Machine.run (stepIO p) k c₁ := by
        intro k
        rw [Machine.run_succ, hr, Step.bind_next]
      rcases ih (c := c₁) ht₁ with ⟨c', hc', ht', hu'⟩ | ⟨r, hr'⟩ | ⟨m, c', hm, hc', hs', hf, hu'⟩
      · exact .inl ⟨c', by rw [hrun]; exact hc', ht', fun hD hu => hu' hD (hu₁ hD hu)⟩
      · exact .inr (.inl ⟨r, by rw [hrun]; exact hr'⟩)
      · exact .inr (.inr ⟨m + 1, c', by omega, by rw [hrun]; exact hc', hs', hf,
          fun hD hu => hu' hD (hu₁ hD hu)⟩)
    | halt r =>
      exact .inr (.inl ⟨r, by rw [Machine.run_succ, hr, Step.bind_halt]⟩)
    | stuck =>
      rw [hr] at hstep
      exact .inr (.inr ⟨0, c, by omega, rfl, hr, hstep, fun _ hu => hu⟩)

/--
**Type safety.** If a well-typed program goes wrong, the state it could not
step from is one of the four faults: arithmetic overflow, use of a freed cell,
a second use of a resumption, or a label applied after its scope ended.
Everything else the machine gives no meaning to cannot happen: an unbound
local, a value of the wrong shape, a missing function or clause, an operation
with no handler, an exit with no target.
-/
theorem type_safety {p : Program} (hp : ProgramOk Δ p) (input : List Int)
    (h : GoesWrong p input) :
    ∃ c, Machine.Reaches (stepIO p) (initIO p input) c ∧ stepIO p c = .stuck
      ∧ Fault c.state := by
  obtain ⟨n, hn⟩ := h
  rcases run_ok hp n (c := initIO p input) (typed_init hp) with ⟨c', hc', _⟩ | ⟨r, hr⟩
    | ⟨m, c', _, hc', hs', hf, _⟩
  · rw [hn] at hc'
    cases hc'
  · rw [hn] at hr
    cases hr
  · exact ⟨c', ⟨m, hc'⟩, hs', hf⟩

/--
**Ownership.** If, besides, the types the context calls duplicable hold no
resumptions, then the fault is not a second use of a resumption: every
resumption is held in at most one place for as long as the program runs, and
whatever is about to use one finds it unused.
-/
theorem owned_safety {p : Program} (hp : ProgramOk Δ p) (hD : DupSound Δ) (input : List Int)
    (h : GoesWrong p input) :
    ∃ c, Machine.Reaches (stepIO p) (initIO p input) c ∧ stepIO p c = .stuck
      ∧ Fault c.state ∧ ¬ Resumed c.state := by
  obtain ⟨n, hn⟩ := h
  rcases run_ok hp n (c := initIO p input) (typed_init hp) with ⟨c', hc', _⟩ | ⟨r, hr⟩
    | ⟨m, c', _, hc', hs', hf, hu⟩
  · rw [hn] at hc'
    cases hc'
  · rw [hn] at hr
    cases hr
  · exact ⟨c', ⟨m, hc'⟩, hs', hf, (hu hD (unique_init p)).not_resumed⟩

end Glorious.Typing
