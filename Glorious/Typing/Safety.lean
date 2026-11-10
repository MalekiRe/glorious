import Glorious.Typing.Stack

/-!
# Type safety for Core

A well-typed machine state steps to a well-typed state, or halts, or is one of
the four faults in `Fault`. So a well-typed program that goes wrong went wrong
by one of those, and by nothing else. The final statement is `type_safety`.
-/

namespace Glorious.Typing

open Core

variable {Δ : Ctx}

/-! ## Evaluating what a computation applies -/

/-- The callee of a typed call evaluates, and is typed at the callable's result
and operations. -/
theorem evalCall_ok {S : StoreTy} {env : Env} {Γ : TEnv} {f : Atom} {args : List Atom}
    {Ps : List Ty} {σ : Ty} {ε : Row} (henv : HasVals Δ S env Γ)
    (hf : HasAtom Γ f (.fn Ps σ ε)) (hargs : HasAtoms Γ args Ps) :
    ∃ c, evalCall env f args = some c ∧ CalleeOk Δ S c σ ε
      ∧ (∀ id v, c = .cont id v → f.eval env = some (.cont id))
      ∧ (∀ id v, c = .label id v → f.eval env = some (.label id)) := by
  obtain ⟨fv, hfv, hft⟩ := atom_ok henv hf
  obtain ⟨vs, hvs, hvst⟩ := atoms_ok henv hargs
  rcases hft.fn_inv with ⟨fn, caps, Cs, rfl, hsig, hcaps⟩ | ⟨id, o, rfl, he, hk⟩
    | ⟨id, τ, rfl, he, hlab⟩
  · exact ⟨.fn fn caps vs, by simp [evalCall, hfv, hvs],
      .fn (sig := ⟨Cs, Ps, σ, ε⟩) hsig hcaps hvst, (fun _ _ h => by cases h),
      (fun _ _ h => by cases h)⟩
  · subst he
    cases hvst with
    | cons hv hnil =>
      cases hnil
      exact ⟨.cont id _, by simp [evalCall, hfv, hvs], .cont hk hv,
        (fun _ _ h => by cases h; exact hfv), (fun _ _ h => by cases h)⟩
  · subst he
    cases hvst with
    | cons hv hnil =>
      cases hnil
      exact ⟨.label id _, by simp [evalCall, hfv, hvs], .label hlab hv,
        (fun _ _ h => by cases h), (fun _ _ h => by cases h; exact hfv)⟩

/-- The callable a label scope runs evaluates, applied to the label. -/
theorem evalScope_ok {S : StoreTy} {env : Env} {Γ : TEnv} {thunk : Atom} {l : Value}
    {τl σ : Ty} {ε : Row} (henv : HasVals Δ S env Γ) (hf : HasAtom Γ thunk (.fn [τl] σ ε))
    (hl : HasVal Δ S l τl) :
    ∃ c, evalScope env thunk l = some c ∧ CalleeOk Δ S c σ ε
      ∧ (∀ id v, c = .cont id v → thunk.eval env = some (.cont id))
      ∧ (∀ id v, c = .label id v → thunk.eval env = some (.label id)) := by
  obtain ⟨fv, hfv, hft⟩ := atom_ok henv hf
  rcases hft.fn_inv with ⟨fn, caps, Cs, rfl, hsig, hcaps⟩ | ⟨id, o, rfl, he, hk⟩
    | ⟨id, τ, rfl, he, hlab⟩
  · exact ⟨.fn fn caps [l], by simp [evalScope, hfv],
      .fn (sig := ⟨Cs, [τl], σ, ε⟩) hsig hcaps (.cons hl .nil), (fun _ _ h => by cases h),
      (fun _ _ h => by cases h)⟩
  · cases he
    exact ⟨.cont id l, by simp [evalScope, hfv], .cont hk hl,
      (fun _ _ h => by cases h; exact hfv), (fun _ _ h => by cases h)⟩
  · cases he
    exact ⟨.label id l, by simp [evalScope, hfv], .label hlab hl,
      (fun _ _ h => by cases h), (fun _ _ h => by cases h; exact hfv)⟩

/-- A callable that takes no arguments is a function. -/
theorem evalThunk_ok {S : StoreTy} {env : Env} {Γ : TEnv} {f : Atom} {σ : Ty} {ε : Row}
    (henv : HasVals Δ S env Γ) (hf : HasAtom Γ f (.fn [] σ ε)) :
    ∃ fn caps Cs, evalCall env f [] = some (.fn fn caps []) ∧ f.eval env = some (.clo fn caps)
      ∧ Δ.fnSig fn ⟨Cs, [], σ, ε⟩ ∧ HasVals Δ S caps Cs := by
  obtain ⟨fv, hfv, hft⟩ := atom_ok henv hf
  rcases hft.fn_inv with ⟨fn, caps, Cs, rfl, hsig, hcaps⟩ | ⟨id, o, rfl, he, hk⟩
    | ⟨id, τ, rfl, he, hlab⟩
  · exact ⟨fn, caps, Cs, by simp [evalCall, evalAtoms, hfv], hfv, hsig, hcaps⟩
  · cases he
  · cases he

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
or no step at all because `s` is one of the faults. -/
def StepOk (Δ : Ctx) (s : State) : Step State Value → Prop
  | .next s' => Typed Δ s'
  | .halt _ => True
  | .stuck => Fault s

theorem StepOk.next {S : StoreTy} {s s' : State} (h : TypedAt Δ S s') : StepOk Δ s (.next s') :=
  Exists.intro S h

theorem StepOk.of_safe {S : StoreTy} {s : State} {r : Step State Value} (h : Safe Δ S r) :
    StepOk Δ s r := by
  cases r with
  | next s' => exact .next h
  | halt v => exact True.intro
  | stuck => exact h.elim

theorem StepOk.of_apply {p : Program} {S : StoreTy} {s : State} {c : Callee} {st : List Frame}
    {store : Store Frame}
    (h : Safe Δ S (apply p c st store) ∨ (apply p c st store = .stuck ∧ Faulty st store c))
    (hf : Faulty st store c → Fault s) : StepOk Δ s (apply p c st store) := by
  rcases h with h | ⟨he, hfa⟩
  · exact .of_safe h
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
    exact .of_safe (deliver_safe hp hs hst hvt)
  | @let_ _ rhs body σ _ _ hrhs hbody =>
    rcases rhs_ok (S := S) henv hrhs with ⟨v, hv, hvt⟩ | ⟨q, args, m, n, rfl, hargs, hq, hnone⟩
    · have h1 : step p ⟨.let_ rhs body, env, stack, ⟨conts, labels, cells⟩⟩
          = .next ⟨body, env ++ [v], stack, ⟨conts, labels, cells⟩⟩ := by simp [step, hv]
      rw [h1]
      exact .next (.mk (henv.snoc hvt) hbody hle hst hs)
    · have h1 : step p ⟨.let_ (.prim q args) body, env, stack, ⟨conts, labels, cells⟩⟩
          = .stuck := by simp [step, hnone]
      rw [h1]
      exact Fault.overflow hargs hq
  | @call _ f args body Ps σ _ ε₁ _ hf hargs hrow hbody =>
    obtain ⟨c, hc, hcok, hck, hcl⟩ := evalCall_ok (S := S) henv hf hargs
    have h1 : step p ⟨.call f args body, env, stack, ⟨conts, labels, cells⟩⟩
        = apply p c (.call env body :: stack) ⟨conts, labels, cells⟩ := by simp [step, hc]
    rw [h1]
    refine .of_apply
      (apply_ok hp hs hcok (.call henv hbody hle hst) (Row.le_trans hrow hle)) (fun hfa => ?_)
    exact hfa.fault (s := ⟨.call f args body, env, stack, ⟨conts, labels, cells⟩⟩) rfl hck hcl
      rfl (fun _ h => findLabel_cons_none h)
  | @tail _ f args Ps _ ε₁ _ hf hargs hrow =>
    obtain ⟨c, hc, hcok, hck, hcl⟩ := evalCall_ok (S := S) henv hf hargs
    have h1 : step p ⟨.tail f args, env, stack, ⟨conts, labels, cells⟩⟩
        = apply p c stack ⟨conts, labels, cells⟩ := by simp [step, hc]
    rw [h1]
    refine .of_apply (apply_ok hp hs hcok hst (Row.le_trans hrow hle)) (fun hfa => ?_)
    exact hfa.fault (s := ⟨.tail f args, env, stack, ⟨conts, labels, cells⟩⟩) rfl hck hcl
      rfl (fun _ h => h)
  | @handle _ ret ops captures thunk body Cs σ ρ _ εt H _ hthunk hcaps hok hrow hbody =>
    obtain ⟨caps, hcv, hcvt⟩ := atoms_ok (S := S) henv hcaps
    obtain ⟨fn, tcaps, TCs, hcall, _, hsig, htc⟩ := evalThunk_ok (S := S) henv hthunk
    have h1 : step p ⟨.handle ret ops captures thunk body, env, stack, ⟨conts, labels, cells⟩⟩
        = callFn p fn tcaps [] (.handler labels ⟨ret, ops, caps⟩ :: .call env body :: stack)
            ⟨conts, labels + 1, cells⟩ := by
      simp [step, hcv, hcall, apply]
    rw [h1]
    obtain ⟨S', hS, hid, hs'⟩ := hs.push_handler (ρ, ε)
    exact .of_safe (callFn_safe hp hsig (htc.mono hS) .nil hrow
      (.handler hid ⟨Cs, hcvt.mono hS, hok⟩ hle (.call (henv.mono hS) hbody hle (hst.mono hS)))
      hs')
  | @handleTail _ ret ops captures thunk Cs σ _ εt H _ hthunk hcaps hok hrow =>
    obtain ⟨caps, hcv, hcvt⟩ := atoms_ok (S := S) henv hcaps
    obtain ⟨fn, tcaps, TCs, hcall, _, hsig, htc⟩ := evalThunk_ok (S := S) henv hthunk
    have h1 : step p ⟨.handleTail ret ops captures thunk, env, stack, ⟨conts, labels, cells⟩⟩
        = callFn p fn tcaps [] (.handler labels ⟨ret, ops, caps⟩ :: stack)
            ⟨conts, labels + 1, cells⟩ := by
      simp [step, hcv, hcall, apply]
    rw [h1]
    obtain ⟨S', hS, hid, hs'⟩ := hs.push_handler (τ, ε)
    exact .of_safe (callFn_safe hp hsig (htc.mono hS) .nil hrow
      (.handler hid ⟨Cs, hcvt.mono hS, hok⟩ hle (hst.mono hS)) hs')
  | @raise _ op args targs Ps _ _ hl hop hargs =>
    obtain ⟨vs, hvs, hvst⟩ := atoms_ok (S := S) henv hargs
    obtain ⟨d, ρ, ε₀, εa, εb, Cs, Ps', r, hfind, hid, hcaps, hop', hale, hsig, hbelow, hble, hin,
      _⟩ := find_ok hst (hle _ _ hl)
    rw [hop] at hop'
    cases hop'
    have h1 : step p ⟨.raise op args, env, stack, ⟨conts, labels, cells⟩⟩
        = leave p (.handler d.id) (.invoke d.arm d.handler.caps vs) stack
            ⟨conts, labels, cells⟩ := by
      simp [step, hvs, hfind]
    rw [h1]
    exact .of_safe (leave_safe hp hs hst
      (.handler (sig := ⟨Cs, Ps, ρ, εa⟩) hid hsig hale hcaps hvst) hin)
  | @perform _ op args body targs Ps σ _ _ hl hop hargs hbody =>
    obtain ⟨vs, hvs, hvst⟩ := atoms_ok (S := S) henv hargs
    obtain ⟨d, ρ, ε₀, εa, εb, Cs, Ps', r, hfind, hid, hcaps, hop', hale, hsig, hbelow, hble, _,
      hre⟩ := find_ok hst (hle _ _ hl)
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
    have hsig' : Δ.fnSig d.arm ⟨Cs, Ps ++ [.fn [σ] ρ ε₀], ρ, εa⟩ := hsig
    exact .of_safe (callFn_safe hp hsig'
      (hcaps.mono hS) ((hvst.mono hS).snoc (.cont hcont)) (Row.le_trans hale hble)
      (hbelow.mono hS) hs')
  | @label _ thunk body σ ρ _ εl εt _ hthunk hrow hbody =>
    obtain ⟨S', hS, hlab, hs'⟩ := hs.push_label σ
    obtain ⟨c, hc, hcok, hck, hcl⟩ :=
      evalScope_ok (S := S') (l := .label labels) (henv.mono hS) hthunk (.label hlab)
    have h1 : step p ⟨.label thunk body, env, stack, ⟨conts, labels, cells⟩⟩
        = apply p c (.label labels :: .call env body :: stack) ⟨conts, labels + 1, cells⟩ := by
      simp [step, hc]
    rw [h1]
    refine .of_apply
      (apply_ok hp hs' hcok (.label hlab (.call (henv.mono hS) hbody hle (hst.mono hS)))
        (Row.le_trans hrow hle)) (fun hfa => ?_)
    exact hfa.fault (s := ⟨.label thunk body, env, stack, ⟨conts, labels, cells⟩⟩) rfl hck hcl
      rfl (fun _ h => findLabel_cons_none (findLabel_cons_none h))
  | @labelTail _ thunk ρ _ εl εt _ hthunk hrow =>
    obtain ⟨S', hS, hlab, hs'⟩ := hs.push_label τ
    obtain ⟨c, hc, hcok, hck, hcl⟩ :=
      evalScope_ok (S := S') (l := .label labels) (henv.mono hS) hthunk (.label hlab)
    have h1 : step p ⟨.labelTail thunk, env, stack, ⟨conts, labels, cells⟩⟩
        = apply p c (.label labels :: stack) ⟨conts, labels + 1, cells⟩ := by
      simp [step, hc]
    rw [h1]
    refine .of_apply
      (apply_ok hp hs' hcok (.label hlab (hst.mono hS)) (Row.le_trans hrow hle))
      (fun hfa => ?_)
    exact hfa.fault (s := ⟨.labelTail thunk, env, stack, ⟨conts, labels, cells⟩⟩) rfl hck hcl
      rfl (fun _ h => findLabel_cons_none h)
  | @guard _ cleanup thunk body σc σ _ εt _ hcl hthunk hrow hbody =>
    obtain ⟨gfn, gcaps, GCs, _, hgev, hgsig, hgc⟩ := evalThunk_ok (S := S) henv hcl
    obtain ⟨fn, tcaps, TCs, hcall, _, hsig, htc⟩ := evalThunk_ok (S := S) henv hthunk
    have h1 : step p ⟨.guard cleanup thunk body, env, stack, ⟨conts, labels, cells⟩⟩
        = callFn p fn tcaps [] (.guard gfn gcaps :: .call env body :: stack)
            ⟨conts, labels, cells⟩ := by
      simp [step, evalClosure, hgev, hcall, apply]
    rw [h1]
    exact .of_safe (callFn_safe hp hsig htc .nil (Row.le_trans hrow hle)
      (.guard hgsig hgc (.call henv hbody hle hst)) hs)
  | @guardTail _ cleanup thunk σc _ εt _ hcl hthunk hrow =>
    obtain ⟨gfn, gcaps, GCs, _, hgev, hgsig, hgc⟩ := evalThunk_ok (S := S) henv hcl
    obtain ⟨fn, tcaps, TCs, hcall, _, hsig, htc⟩ := evalThunk_ok (S := S) henv hthunk
    have h1 : step p ⟨.guardTail cleanup thunk, env, stack, ⟨conts, labels, cells⟩⟩
        = callFn p fn tcaps [] (.guard gfn gcaps :: stack) ⟨conts, labels, cells⟩ := by
      simp [step, evalClosure, hgev, hcall, apply]
    rw [h1]
    exact .of_safe (callFn_safe hp hsig htc .nil (Row.le_trans hrow hle)
      (.guard hgsig hgc hst) hs)
  | @cancel _ k body σ ρ _ ε₁ _ hk hrow hbody =>
    obtain ⟨kv, hkv, hkt⟩ := atom_ok henv hk
    rcases hkt.fn_inv with ⟨fn, caps, Cs, rfl, _, _⟩ | ⟨id, o, rfl, he, hcont⟩
      | ⟨id, τl, rfl, _, _⟩
    · have h1 : step p ⟨.cancel k body, env, stack, ⟨conts, labels, cells⟩⟩
          = .next ⟨body, env ++ [Value.unit], stack, ⟨conts, labels, cells⟩⟩ := by
        simp [step, evalCont, hkv]
      rw [h1]
      exact .next (.mk (henv.snoc .unit) hbody hle hst hs)
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
          exact .of_safe (leave_safe hp hs' hst' (.label hlab .unit)
            ⟨.label labels, by simp, by simp [Frame.isTarget]⟩)
    · have h1 : step p ⟨.cancel k body, env, stack, ⟨conts, labels, cells⟩⟩
          = .next ⟨body, env ++ [Value.unit], stack, ⟨conts, labels, cells⟩⟩ := by
        simp [step, evalCont, hkv]
      rw [h1]
      exact .next (.mk (henv.snoc .unit) hbody hle hst hs)
  | @alloc _ a body σ _ _ ha hbody =>
    obtain ⟨v, hv, hvt⟩ := atom_ok henv ha
    have h1 : step p ⟨.mem .alloc [a] body, env, stack, ⟨conts, labels, cells⟩⟩
        = .next ⟨body, env ++ [.ref cells.length], stack,
            ⟨conts, labels, cells ++ [some v]⟩⟩ := by
      simp [step, evalAtoms, hv, MemOp.eval]
    rw [h1]
    obtain ⟨S', hS, hcell, hs'⟩ := hs.push_cell hvt
    exact .next (.mk ((henv.mono hS).snoc (.ref hcell)) hbody hle (hst.mono hS) hs')
  | @load _ a body σ _ _ ha hbody =>
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
        exact .next (.mk (henv.snoc (hval w hget)) hbody hle hst hs)
  | @store _ a b body σ _ _ ha hb hbody =>
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
        exact .next (.mk (henv.snoc .unit) hbody hle hst
          (hs.set_cell hcell (fun u hu => by cases hu; exact hwt)))
  | @free _ a body σ _ _ ha hbody =>
    obtain ⟨v, hv, hvt⟩ := atom_ok henv ha
    obtain ⟨addr, rfl, hcell⟩ := hvt.ref_inv
    obtain ⟨hlt, hval⟩ := hs.cells addr σ hcell
    cases hget : cells[addr]? with
    | none => exact absurd hlt (by simpa using List.getElem?_eq_none_iff.mp hget)
    | some x =>
      cases x with
      | none =>
        have h1 : step p ⟨.mem .free [a] body, env, stack, ⟨conts, labels, cells⟩⟩ = .stuck := by
          simp [step, evalAtoms, hv, MemOp.eval, hget]
        rw [h1]
        exact Fault.freed (a := addr) (vs := []) (by simp [evalAtoms, hv]) hget
      | some old =>
        have h1 : step p ⟨.mem .free [a] body, env, stack, ⟨conts, labels, cells⟩⟩
            = .next ⟨body, env ++ [Value.unit], stack,
                ⟨conts, labels, cells.set addr none⟩⟩ := by
          simp [step, evalAtoms, hv, MemOp.eval, hget]
        rw [h1]
        exact .next (.mk (henv.snoc .unit) hbody hle hst
          (hs.set_cell hcell (fun u hu => by cases hu)))
  | write _ _ => exact absurd rfl (hnh _ _ _)
  | read _ => exact absurd rfl (hnh _ _ _)

/-! ## Programs in their world -/

/-- The outcome of a step of a program in its world is acceptable. -/
def ConfigOk (Δ : Ctx) (c : Config) : Step Config Result → Prop
  | .next c' => Typed Δ c'.state
  | .halt _ => True
  | .stuck => Fault c.state

theorem stepIO_eq_lift {p : Program} {s : State} {w : World}
    (h : ∀ id args body, s.tm ≠ .host id args body) : stepIO p ⟨s, w⟩ = lift w (step p s) := by
  obtain ⟨tm, env, stack, store⟩ := s
  cases tm <;> first | rfl | exact absurd rfl (h _ _ _)

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
      exact ⟨S, .mk (henv.snoc .unit) hbody hle hst hs⟩
    | read hbody =>
      obtain ⟨input, output⟩ := w
      cases input with
      | nil =>
        exact ⟨S, .mk (henv.snoc (.data (.inl ⟨rfl, rfl⟩) (.cons .int (.cons .int .nil))))
          hbody hle hst hs⟩
      | cons n rest =>
        exact ⟨S, .mk (henv.snoc (.data (.inl ⟨rfl, rfl⟩) (.cons .int (.cons .int .nil))))
          hbody hle hst hs⟩
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

/-- From a well-typed state, a run of any length is still going in a well-typed
state, or has halted, or stopped at a fault. -/
theorem run_ok {p : Program} (hp : ProgramOk Δ p) : ∀ (n : Nat) {c : Config},
    Typed Δ c.state →
    (∃ c', Machine.run (stepIO p) n c = .next c' ∧ Typed Δ c'.state)
      ∨ (∃ r, Machine.run (stepIO p) n c = .halt r)
      ∨ (∃ m c', m < n ∧ Machine.run (stepIO p) m c = .next c' ∧ stepIO p c' = .stuck
          ∧ Fault c'.state) := by
  intro n
  induction n with
  | zero => intro c ht; exact .inl ⟨c, rfl, ht⟩
  | succ n ih =>
    intro c ht
    have hstep := stepIO_ok hp ht
    cases hr : stepIO p c with
    | next c₁ =>
      rw [hr] at hstep
      have hrun : ∀ k, Machine.run (stepIO p) (k + 1) c = Machine.run (stepIO p) k c₁ := by
        intro k
        rw [Machine.run_succ, hr, Step.bind_next]
      rcases ih (c := c₁) hstep with ⟨c', hc', ht'⟩ | ⟨r, hr'⟩ | ⟨m, c', hm, hc', hs', hf⟩
      · exact .inl ⟨c', by rw [hrun]; exact hc', ht'⟩
      · exact .inr (.inl ⟨r, by rw [hrun]; exact hr'⟩)
      · exact .inr (.inr ⟨m + 1, c', by omega, by rw [hrun]; exact hc', hs', hf⟩)
    | halt r =>
      exact .inr (.inl ⟨r, by rw [Machine.run_succ, hr, Step.bind_halt]⟩)
    | stuck =>
      rw [hr] at hstep
      exact .inr (.inr ⟨0, c, by omega, rfl, hr, hstep⟩)

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
    | ⟨m, c', _, hc', hs', hf⟩
  · rw [hn] at hc'
    cases hc'
  · rw [hn] at hr
    cases hr
  · exact ⟨c', ⟨m, hc'⟩, hs', hf⟩

end Glorious.Typing
