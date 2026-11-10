import Glorious.Typing.Values

/-!
# Typed stacks deliver, leave and dispatch

A value delivered to a typed stack, an exit through a typed stack and an
operation performed on a typed stack all end in a typed state. These are the
facts about whole stacks that the safety theorem needs.
-/

namespace Glorious.Typing

open Core

variable {Δ : Ctx}

/-! ## Growing the store typing -/

theorem HandlerRt.mono {S S' : StoreTy} (hle : S.Le S') {h : Handler} {σ ρ : Ty} {H ε : Row}
    (hh : HandlerRt Δ S h σ ρ H ε) : HandlerRt Δ S' h σ ρ H ε :=
  let ⟨Cs, hc, hok⟩ := hh
  ⟨Cs, hc.mono hle, hok⟩

theorem ExitOk.mono {S S' : StoreTy} (hle : S.Le S') {target : Target} {after : After}
    (h : ExitOk Δ S target after) : ExitOk Δ S' target after := by
  cases h with
  | label hl hv => exact .label (hle.labels _ _ hl) (hv.mono hle)
  | handler hh hsig hr hc ha =>
    exact .handler (hle.handlers _ _ hh) hsig hr (hc.mono hle) (ha.mono hle)

theorem StackOk.mono {S S' : StoreTy} (hle : S.Le S') {st : List Frame} {τ : Ty} {ε : Row}
    (h : StackOk Δ S st τ ε) : StackOk Δ S' st τ ε := by
  induction h with
  | nil => exact .nil
  | call henv hbody hrow _ ih => exact .call (henv.mono hle) hbody hrow ih
  | handler hid hh hrow _ ih => exact .handler (hle.handlers _ _ hid) (hh.mono hle) hrow ih
  | label hid _ ih => exact .label (hle.labels _ _ hid) ih
  | guard hsig hc _ ih => exact .guard hsig (hc.mono hle) ih
  | yield hw _ ih => exact .yield (hw.mono hle) ih
  | exit hx hin _ ih => exact .exit (hx.mono hle) hin ih

theorem ContOk.mono {S S' : StoreTy} (hle : S.Le S') {seg : List Frame} {o ρ : Ty} {ε₀ : Row}
    (h : ContOk Δ S seg o ρ ε₀) : ContOk Δ S' seg o ρ ε₀ :=
  fun S'' hle' st ε' hst hr => h S'' (hle.trans hle') st ε' hst hr

theorem StackOk.tail {S : StoreTy} {fr : Frame} {st : List Frame} {τ : Ty} {ε : Row}
    (h : StackOk Δ S (fr :: st) τ ε) : ∃ τ' ε', StackOk Δ S st τ' ε' := by
  cases h with
  | call _ _ _ h => exact ⟨_, _, h⟩
  | handler _ _ _ h => exact ⟨_, _, h⟩
  | label _ h => exact ⟨_, _, h⟩
  | guard _ _ h => exact ⟨_, _, h⟩
  | yield _ h => exact ⟨_, _, h⟩
  | exit _ _ h => exact ⟨_, _, h⟩

/-! ## Finding the handler of an operation -/

theorem lookup_cons_eq {β : Type} (k : Nat) (b : β) (as : List (Nat × β)) :
    List.lookup k ((k, b) :: as) = some b := by
  simp

theorem lookup_cons_ne {β : Type} {a k : Nat} (h : a ≠ k) (b : β) (as : List (Nat × β)) :
    List.lookup a ((k, b) :: as) = List.lookup a as := by
  have hb : (a == k) = false := by simpa using h
  simp [List.lookup_cons, hb]

/-- The signature of the function serving an operation, by whether the
operation can be resumed. -/
def ArmSig (Δ : Ctx) (Cs : List Ty) (ρ : Ty) (ε : Row) (arm : Nat) (Ps : List Ty) (εa : Row) :
    Option Ty → Prop
  | none => Δ.fnSig arm ⟨Cs, Ps, ρ, εa⟩
  | some o => Δ.fnSig arm ⟨Cs, Ps ++ [.fn [o] ρ ε], ρ, εa⟩

theorem ArmsOk.lookup_none {Cs : List Ty} {ρ : Ty} {ε : Row} {ops : List (Nat × Nat)} {H : Row}
    (h : ArmsOk Δ Cs ρ ε ops H) {op : Nat} : H.lookup op = none → ops.lookup op = none := by
  induction h with
  | nil => intro _; rfl
  | @terminal op' arm Ps εa ops H _ _ _ ih =>
    intro hl
    by_cases he : op = op'
    · subst he
      rw [lookup_cons_eq] at hl
      cases hl
    · rw [lookup_cons_ne he] at hl ⊢
      exact ih hl
  | @resumptive op' arm Ps o εa ops H _ _ _ ih =>
    intro hl
    by_cases he : op = op'
    · subst he
      rw [lookup_cons_eq] at hl
      cases hl
    · rw [lookup_cons_ne he] at hl ⊢
      exact ih hl

theorem ArmsOk.lookup_some {Cs : List Ty} {ρ : Ty} {ε : Row} {ops : List (Nat × Nat)} {H : Row}
    (h : ArmsOk Δ Cs ρ ε ops H) {op : Nat} {Ps : List Ty} {r : Option Ty} :
    H.lookup op = some (Ps, r) →
    ∃ arm εa, ops.lookup op = some arm ∧ Row.le εa ε ∧ ArmSig Δ Cs ρ ε arm Ps εa r := by
  induction h with
  | nil => intro hl; simp [List.lookup] at hl
  | @terminal op' arm Ps' εa ops H hsig hle _ ih =>
    intro hl
    by_cases he : op = op'
    · subst he
      rw [lookup_cons_eq] at hl
      cases hl
      exact ⟨arm, εa, lookup_cons_eq .., hle, hsig⟩
    · rw [lookup_cons_ne he] at hl
      obtain ⟨arm', εa', hl', hle', hsig'⟩ := ih hl
      exact ⟨arm', εa', by rw [lookup_cons_ne he]; exact hl', hle', hsig'⟩
  | @resumptive op' arm Ps' o εa ops H hsig hle _ ih =>
    intro hl
    by_cases he : op = op'
    · subst he
      rw [lookup_cons_eq] at hl
      cases hl
      exact ⟨arm, εa, lookup_cons_eq .., hle, hsig⟩
    · rw [lookup_cons_ne he] at hl
      obtain ⟨arm', εa', hl', hle', hsig'⟩ := ih hl
      exact ⟨arm', εa', by rw [lookup_cons_ne he]; exact hl', hle', hsig'⟩

theorem findHandler_skip {op : Nat} {fr : Frame} {st : List Frame} {d : Dispatch Frame}
    (hfr : handles Frame.asHandler op fr = none)
    (hd : findHandler Frame.asHandler op st = some d) :
    findHandler Frame.asHandler op (fr :: st)
      = some ⟨fr :: d.above, d.id, d.handler, d.arm, d.below⟩ := by
  simp [findHandler, hfr, hd]

/--
An operation the stack's type offers has a handler on the stack, and the
machine's search finds it. The function serving the operation is typed at the
type the row gives the operation; the stack below the handler takes what the
handler yields; and the frames above the handler, with the handler, can be put
on any later stack that suits the handler and are typed there as they are here.
-/
theorem find_ok {S : StoreTy} {st : List Frame} {τ : Ty} {ε : Row} (hst : StackOk Δ S st τ ε) :
    ∀ {op : Nat} {Ps : List Ty} {r : Option Ty}, ε.lookup op = some (Ps, r) →
    ∃ d ρ ε₀ εa εb Cs, findHandler Frame.asHandler op st = some d
      ∧ S.handlers d.id = some (ρ, ε₀)
      ∧ HasVals Δ S d.handler.caps Cs
      ∧ Row.le εa ε₀ ∧ ArmSig Δ Cs ρ ε₀ d.arm Ps εa r
      ∧ StackOk Δ S d.below ρ εb ∧ Row.le ε₀ εb
      ∧ (∃ fr, fr ∈ st ∧ fr.isTarget (.handler d.id) = true)
      ∧ (∀ S', S.Le S' → ∀ st' ε', StackOk Δ S' st' ρ ε' → Row.le ε₀ ε' →
          StackOk Δ S' (d.above ++ .handler d.id d.handler :: st') τ ε) := by
  induction hst with
  | nil => intro op Ps r hl; simp [List.lookup] at hl
  | @call env body st Γ σ τ εb ε henv hbody hrow _ ih =>
    intro op Ps r hl
    obtain ⟨d, ρ, ε₀, εa, εb', Cs, hf, hid, hcaps, hale, hsig, hbelow, hble, ⟨fr, hfr, hft⟩, hre⟩ :=
      ih hl
    exact ⟨_, ρ, ε₀, εa, εb', Cs, findHandler_skip (by simp [handles, Frame.asHandler]) hf, hid,
      hcaps, hale, hsig, hbelow, hble, ⟨fr, List.mem_cons_of_mem _ hfr, hft⟩,
      fun S' hle st' ε' hst' hr => .call (henv.mono hle) hbody hrow (hre S' hle st' ε' hst' hr)⟩
  | @handler id h st σ ρ H ε₀ ε hid hh hrow hrest ih =>
    intro op Ps r hl
    obtain ⟨Cs, hcaps, hok⟩ := hh
    rw [List.lookup_append] at hl
    cases hH : H.lookup op with
    | none =>
      rw [hH] at hl
      have hl' : ε.lookup op = some (Ps, r) := hrow _ _ (by simpa using hl)
      obtain ⟨d, ρ', ε₀', εa, εb', Cs', hf, hid', hcaps', hale, hsig, hbelow, hble,
        ⟨fr, hfr, hft⟩, hre⟩ := ih hl'
      have hskip : handles Frame.asHandler op (.handler id h) = none := by
        simp [handles, Frame.asHandler, hok.arms.lookup_none hH]
      exact ⟨_, ρ', ε₀', εa, εb', Cs', findHandler_skip hskip hf, hid', hcaps', hale, hsig,
        hbelow, hble, ⟨fr, List.mem_cons_of_mem _ hfr, hft⟩,
        fun S' hle st' ε' hst' hr =>
          .handler (hle.handlers _ _ hid) (HandlerRt.mono hle ⟨Cs, hcaps, hok⟩) hrow
            (hre S' hle st' ε' hst' hr)⟩
    | some sig =>
      rw [hH] at hl
      have e : sig = (Ps, r) := by simpa using hl
      subst e
      obtain ⟨arm, εa, harm, hale, hsig⟩ := hok.arms.lookup_some hH
      have hfind : findHandler Frame.asHandler op (.handler id h :: st)
          = some ⟨[], id, h, arm, st⟩ := by
        simp [findHandler, handles, Frame.asHandler, harm]
      exact ⟨_, ρ, ε₀, εa, ε, Cs, hfind, hid, hcaps, hale, hsig, hrest, hrow,
        ⟨.handler id h, List.mem_cons_self .., by simp [Frame.isTarget]⟩,
        fun S' hle st' ε' hst' hr =>
          .handler (hle.handlers _ _ hid) (HandlerRt.mono hle ⟨Cs, hcaps, hok⟩) hr hst'⟩
  | @label id st τ ε hid _ ih =>
    intro op Ps r hl
    obtain ⟨d, ρ, ε₀, εa, εb', Cs, hf, hid', hcaps, hale, hsig, hbelow, hble, ⟨fr, hfr, hft⟩, hre⟩ :=
      ih hl
    exact ⟨_, ρ, ε₀, εa, εb', Cs, findHandler_skip (by simp [handles, Frame.asHandler]) hf, hid',
      hcaps, hale, hsig, hbelow, hble, ⟨fr, List.mem_cons_of_mem _ hfr, hft⟩,
      fun S' hle st' ε' hst' hr => .label (hle.labels _ _ hid) (hre S' hle st' ε' hst' hr)⟩
  | @guard fn captures st Cs' σc τ ε hgs hgc _ ih =>
    intro op Ps r hl
    obtain ⟨d, ρ, ε₀, εa, εb', Cs, hf, hid', hcaps, hale, hsig, hbelow, hble, ⟨fr, hfr, hft⟩, hre⟩ :=
      ih hl
    exact ⟨_, ρ, ε₀, εa, εb', Cs, findHandler_skip (by simp [handles, Frame.asHandler]) hf, hid',
      hcaps, hale, hsig, hbelow, hble, ⟨fr, List.mem_cons_of_mem _ hfr, hft⟩,
      fun S' hle st' ε' hst' hr => .guard hgs (hgc.mono hle) (hre S' hle st' ε' hst' hr)⟩
  | @yield w st σ τ ε hw _ ih =>
    intro op Ps r hl
    obtain ⟨d, ρ, ε₀, εa, εb', Cs, hf, hid', hcaps, hale, hsig, hbelow, hble, ⟨fr, hfr, hft⟩, hre⟩ :=
      ih hl
    exact ⟨_, ρ, ε₀, εa, εb', Cs, findHandler_skip (by simp [handles, Frame.asHandler]) hf, hid',
      hcaps, hale, hsig, hbelow, hble, ⟨fr, List.mem_cons_of_mem _ hfr, hft⟩,
      fun S' hle st' ε' hst' hr => .yield (hw.mono hle) (hre S' hle st' ε' hst' hr)⟩
  | exit _ _ _ _ => intro op Ps r hl; simp [List.lookup] at hl

/-! ## Delivering and leaving -/

theorem leave_target_yield {p : Program} {fr : Frame} {target : Target} {v : Value}
    {st : List Frame} {store : Store Frame} (h : fr.isTarget target = true) :
    leave p target (.yield v) (fr :: st) store = deliver p v st store := by
  simp [leave, h]

theorem leave_target_invoke {p : Program} {fr : Frame} {target : Target} {fn : Nat}
    {captures args : List Value} {st : List Frame} {store : Store Frame}
    (h : fr.isTarget target = true) :
    leave p target (.invoke fn captures args) (fr :: st) store
      = callFn p fn captures args st store := by
  simp [leave, h]

theorem leave_guard {p : Program} {target : Target} {after : After} {fn : Nat}
    {captures : List Value} {st : List Frame} {store : Store Frame}
    (h : ¬ (Frame.guard fn captures).isTarget target = true) :
    leave p target after (.guard fn captures :: st) store
      = callFn p fn captures [] (.exit target after :: st) store := by
  simp [leave, h]

theorem StackOk.label_target {S : StoreTy} {fr : Frame} {st : List Frame} {τ σ : Ty} {ε : Row}
    {id : Nat} (h : StackOk Δ S (fr :: st) τ ε) (ht : fr.isTarget (.label id) = true)
    (hl : S.labels id = some σ) : ∃ ε', StackOk Δ S st σ ε' := by
  cases h with
  | label hid hrest =>
    simp [Frame.isTarget] at ht
    subst ht
    rw [hl] at hid
    cases hid
    exact ⟨_, hrest⟩
  | _ => simp [Frame.isTarget] at ht

theorem StackOk.handler_target {S : StoreTy} {fr : Frame} {st : List Frame} {τ ρ : Ty}
    {ε ε₀ : Row} {id : Nat} (h : StackOk Δ S (fr :: st) τ ε)
    (ht : fr.isTarget (.handler id) = true) (hl : S.handlers id = some (ρ, ε₀)) :
    ∃ ε', StackOk Δ S st ρ ε' ∧ Row.le ε₀ ε' := by
  cases h with
  | handler hid _ hrow hrest =>
    simp [Frame.isTarget] at ht
    subst ht
    rw [hl] at hid
    cases hid
    exact ⟨_, hrest, hrow⟩
  | _ => simp [Frame.isTarget] at ht

/--
Delivering a value to a typed stack that takes it, and leaving a typed stack
for a target that is on it, both end well: in a typed state or with the
program's result. Proved together, as the two are defined together.
-/
theorem deliver_leave_safe {p : Program} {S : StoreTy} {store : Store Frame}
    (hp : ProgramOk Δ p) (hs : StoreOk Δ S store) : ∀ (st : List Frame),
    (∀ {v : Value} {τ : Ty} {ε : Row}, StackOk Δ S st τ ε → HasVal Δ S v τ →
        Safe Δ S (deliver p v st store))
    ∧ (∀ {target : Target} {after : After} {τ : Ty} {ε : Row}, StackOk Δ S st τ ε →
        ExitOk Δ S target after → (∃ fr, fr ∈ st ∧ fr.isTarget target = true) →
        Safe Δ S (leave p target after st store)) := by
  intro st
  induction st with
  | nil =>
    refine ⟨fun _ _ => ?_, fun _ _ hin => ?_⟩
    · exact True.intro
    · obtain ⟨fr, hfr, _⟩ := hin
      cases hfr
  | cons fr st ih =>
    obtain ⟨ihd, ihl⟩ := ih
    refine ⟨fun hst hv => ?_, @fun target after τ ε hst hx hin => ?_⟩
    · cases hst with
      | call henv hbody hrow hrest => exact .mk (henv.snoc hv) hbody hrow hrest hs
      | handler hid hh hrow hrest =>
        obtain ⟨Cs, hcaps, hok⟩ := hh
        obtain ⟨εr, hret, hrle⟩ := hok.ret
        exact callFn_safe hp hret hcaps (.cons hv .nil) (Row.le_trans hrle hrow) hrest hs
      | label hid hrest => exact ihd hrest hv
      | guard hsig hc hrest =>
        exact callFn_safe hp hsig hc .nil (Row.nil_le _) (.yield hv hrest) hs
      | yield hw hrest => exact ihd hrest hw
      | exit hx hin hrest => exact ihl hrest hx hin
    · by_cases ht : fr.isTarget target = true
      · cases hx with
        | label hl hv =>
          obtain ⟨ε', hrest⟩ := hst.label_target ht hl
          rw [leave_target_yield ht]
          exact ihd hrest hv
        | handler hh hsig hr hc ha =>
          obtain ⟨ε', hrest, hrow⟩ := hst.handler_target ht hh
          rw [leave_target_invoke ht]
          exact callFn_safe hp hsig hc ha (Row.le_trans hr hrow) hrest hs
      · have hin' : ∃ fr', fr' ∈ st ∧ fr'.isTarget target = true := by
          obtain ⟨f, hf, hft⟩ := hin
          rcases List.mem_cons.mp hf with rfl | hf
          · exact absurd hft ht
          · exact ⟨f, hf, hft⟩
        obtain ⟨τ', ε', hrest⟩ := hst.tail
        cases fr with
        | guard fn captures =>
          cases hst with
          | guard hsig hc hrest' =>
            rw [leave_guard ht]
            exact callFn_safe hp hsig hc .nil (Row.nil_le _) (.exit hx hin' hrest') hs
        | call env body =>
          have h1 : leave p target after (.call env body :: st) store
              = leave p target after st store := by simp [leave, ht]
          rw [h1]
          exact ihl hrest hx hin'
        | handler id h =>
          have h1 : leave p target after (.handler id h :: st) store
              = leave p target after st store := by simp [leave, ht]
          rw [h1]
          exact ihl hrest hx hin'
        | label id =>
          have h1 : leave p target after (.label id :: st) store
              = leave p target after st store := by simp [leave, ht]
          rw [h1]
          exact ihl hrest hx hin'
        | yield w =>
          have h1 : leave p target after (.yield w :: st) store
              = leave p target after st store := by simp [leave, ht]
          rw [h1]
          exact ihl hrest hx hin'
        | exit t a =>
          have h1 : leave p target after (.exit t a :: st) store
              = leave p target after st store := by simp [leave, ht]
          rw [h1]
          exact ihl hrest hx hin'

theorem deliver_safe {p : Program} {S : StoreTy} {store : Store Frame} {st : List Frame}
    {v : Value} {τ : Ty} {ε : Row} (hp : ProgramOk Δ p) (hs : StoreOk Δ S store)
    (hst : StackOk Δ S st τ ε) (hv : HasVal Δ S v τ) : Safe Δ S (deliver p v st store) :=
  (deliver_leave_safe hp hs st).1 hst hv

theorem leave_safe {p : Program} {S : StoreTy} {store : Store Frame} {st : List Frame}
    {target : Target} {after : After} {τ : Ty} {ε : Row} (hp : ProgramOk Δ p)
    (hs : StoreOk Δ S store) (hst : StackOk Δ S st τ ε) (hx : ExitOk Δ S target after)
    (hin : ∃ fr, fr ∈ st ∧ fr.isTarget target = true) :
    Safe Δ S (leave p target after st store) :=
  (deliver_leave_safe hp hs st).2 hst hx hin

/-! ## Applying a callee -/

theorem takeCont_some {α : Type} : ∀ {cs : List (Option α)} {id : Nat} {x : α},
    cs[id]? = some (some x) → takeCont cs id = some (x, cs.set id none)
  | [], _, _, h => by simp at h
  | c :: cs, 0, x, h => by
    simp at h
    subst h
    simp [takeCont]
  | c :: cs, id + 1, x, h => by
    simp at h
    simp [takeCont, takeCont_some h]

theorem takeCont_none {α : Type} : ∀ {cs : List (Option α)} {id : Nat},
    cs[id]? = some none → takeCont cs id = none
  | [], _, h => by simp at h
  | c :: cs, 0, h => by
    simp at h
    subst h
    simp [takeCont]
  | c :: cs, id + 1, h => by
    simp at h
    simp [takeCont, takeCont_none h]

theorem findLabel_target {id : Nat} : ∀ {st : List Frame} {r : List Frame × List Frame},
    findLabel Frame.asLabel id st = some r → ∃ fr, fr ∈ st ∧ fr.isTarget (.label id) = true
  | [], _, h => by simp [findLabel] at h
  | fr :: st, r, h => by
    by_cases he : Frame.asLabel fr = some id
    · refine ⟨fr, List.mem_cons_self .., ?_⟩
      cases fr <;> simp [Frame.asLabel] at he
      simp [Frame.isTarget, he]
    · cases hr : findLabel Frame.asLabel id st with
      | none => simp [findLabel, he, hr] at h
      | some r' =>
        obtain ⟨f, hf, hft⟩ := findLabel_target hr
        exact ⟨f, List.mem_cons_of_mem _ hf, hft⟩

theorem findLabel_cons_none {id : Nat} {fr : Frame} {st : List Frame}
    (h : findLabel Frame.asLabel id (fr :: st) = none) :
    findLabel Frame.asLabel id st = none := by
  by_cases he : Frame.asLabel fr = some id
  · simp [findLabel, he] at h
  · cases hr : findLabel Frame.asLabel id st with
    | none => rfl
    | some r => simp [findLabel, he, hr] at h

/-- A callee applied to typed arguments: what it gives back, and the operations it needs. -/
inductive CalleeOk (Δ : Ctx) (S : StoreTy) : Callee → Ty → Row → Prop where
  | fn {fn : Nat} {captures vs : List Value} {sig : FnSig} :
      Δ.fnSig fn sig → HasVals Δ S captures sig.caps → HasVals Δ S vs sig.params →
      CalleeOk Δ S (.fn fn captures vs) sig.ret sig.eff
  | cont {id : Nat} {v : Value} {o ρ : Ty} {ε : Row} :
      S.conts id = some (o, ρ, ε) → HasVal Δ S v o → CalleeOk Δ S (.cont id v) ρ ε
  | label {id : Nat} {v : Value} {σ ρ : Ty} {ε : Row} :
      S.labels id = some σ → HasVal Δ S v σ → CalleeOk Δ S (.label id v) ρ ε

/-- The two ways applying a typed callee can fail. -/
inductive Faulty (st : List Frame) (store : Store Frame) : Callee → Prop where
  | resumed {id : Nat} {v : Value} : store.conts[id]? = some none → Faulty st store (.cont id v)
  | dead {id : Nat} {v : Value} :
      findLabel Frame.asLabel id st = none → Faulty st store (.label id v)

/-- Taking a resumption's frames out of a typed store leaves a typed store. -/
theorem StoreOk.take {S : StoreTy} {conts : Conts Frame} {labels : Nat} {cells : Cells}
    (hs : StoreOk Δ S ⟨conts, labels, cells⟩) (id : Nat) :
    StoreOk Δ S ⟨conts.set id none, labels, cells⟩ := by
  refine ⟨fun id' o ρ ε₀ h => ?_, hs.labels, hs.handlers, hs.cells⟩
  obtain ⟨hlt, hseg⟩ := hs.conts id' o ρ ε₀ h
  refine ⟨by simpa using hlt, fun seg hget => ?_⟩
  rw [List.getElem?_set] at hget
  by_cases he : id = id'
  · subst he
    simp at hget
  · simp [he] at hget
    exact hseg seg hget

/-- Applying a typed callee on a stack that takes its result and serves its
operations ends well, unless it is a used resumption or a label whose scope has
ended. -/
theorem apply_ok {p : Program} {S : StoreTy} {store : Store Frame} {st : List Frame}
    {c : Callee} {σ : Ty} {ε' ε : Row} (hp : ProgramOk Δ p) (hs : StoreOk Δ S store)
    (hc : CalleeOk Δ S c σ ε') (hst : StackOk Δ S st σ ε) (hle : Row.le ε' ε) :
    Safe Δ S (apply p c st store) ∨ (apply p c st store = .stuck ∧ Faulty st store c) := by
  cases hc with
  | fn hsig hcaps hvs => exact .inl (callFn_safe hp hsig hcaps hvs hle hst hs)
  | @cont id v o ρ ε' hk hv =>
    obtain ⟨conts, labels, cells⟩ := store
    obtain ⟨hlt, hseg⟩ := hs.conts id o σ ε' hk
    cases hget : conts[id]? with
    | none =>
      have := List.getElem?_eq_none_iff.mp hget
      exact absurd hlt (by simpa using this)
    | some x =>
      cases x with
      | none =>
        exact .inr ⟨by simp [apply, takeCont_none hget], .resumed hget⟩
      | some seg =>
        obtain ⟨ε'', hst'⟩ := hseg seg hget S (StoreTy.Le.refl S) st ε hst hle
        have h1 : apply p (.cont id v) st ⟨conts, labels, cells⟩
            = deliver p v (seg ++ st) ⟨conts.set id none, labels, cells⟩ := by
          simp [apply, takeCont_some hget]
        rw [h1]
        exact .inl (deliver_safe hp (hs.take id) hst' hv)
  | @label id v σ' ρ ε' hl hv =>
    cases hf : findLabel Frame.asLabel id st with
    | none => exact .inr ⟨by simp [apply, hf], .dead hf⟩
    | some r =>
      have h1 : apply p (.label id v) st store = leave p (.label id) (.yield v) st store := by
        simp [apply, hf]
      rw [h1]
      exact .inl (leave_safe hp hs hst (.label hl hv) (findLabel_target hf))

end Glorious.Typing
