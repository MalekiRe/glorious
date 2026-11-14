module

public import Glorious.Typing.Values

/-!
# Typed stacks deliver, leave and dispatch

A value delivered to a typed stack, an exit through a typed stack and an
operation performed on a typed stack all end in a typed state. These are the
facts about whole stacks that the safety theorem needs.
-/

@[expose] public section

namespace Glorious.Typing

open Core

variable {Δ : Ctx}

/-! ## Growing the store typing -/

theorem HandlerRt.mono {S S' : StoreTy} (hle : S.Le S') {h : Handler} {σ ρ : Ty} {H ε : Row}
    {Φ : List Rgn} (hh : HandlerRt Δ S h σ ρ H ε Φ) : HandlerRt Δ S' h σ ρ H ε Φ :=
  let ⟨Cs, hc, hok⟩ := hh
  ⟨Cs, hc.mono hle, hok⟩

theorem ExitOk.mono {S S' : StoreTy} (hle : S.Le S') {target : Target} {after : After}
    (h : ExitOk Δ S target after) : ExitOk Δ S' target after := by
  cases h with
  | label hl hv => exact .label (hle.labels _ _ hl) (hv.mono hle)
  | handler hh hent hc ha =>
    exact .handler (hle.handlers _ _ hh) hent (hc.mono hle) (ha.mono hle)

theorem StackOk.mono {S S' : StoreTy} (hle : S.Le S') {st : List Frame} {τ : Ty} {ε : Row}
    {ϕ : List Rgn} (h : StackOk Δ S st τ ε ϕ) : StackOk Δ S' st τ ε ϕ := by
  induction h with
  | nil => exact .nil
  | call henv hbody hrow hsub _ ih => exact .call (henv.mono hle) hbody hrow hsub ih
  | handler hid hh hrow hsub _ ih =>
    exact .handler (hle.handlers _ _ hid) (hh.mono hle) hrow hsub ih
  | label hid _ ih => exact .label (hle.labels _ _ hid) ih
  | guard hent hc _ ih => exact .guard hent (hc.mono hle) ih
  | cell hc _ ih => exact .cell (hle.cells _ _ hc) ih
  | lend hl hb hon hρ hw _ ih => exact .lend (hle.loans _ _ hl) hb (hon.mono hle) hρ hw ih
  | lendLoose hn hl hon _ ih =>
    exact .lendLoose hn (hle.loans _ _ hl)
      (fun hR => by
        obtain ⟨ρ, h1, h2⟩ := hon hR
        exact ⟨ρ, h1.mono hle, h2⟩) ih
  | yield hw _ ih => exact .yield (hw.mono hle) ih
  | exit hx hin _ ih => exact .exit (hx.mono hle) hin ih
  | never _ ih => exact .never ih

theorem ContOk.mono {S S' : StoreTy} (hle : S.Le S') {seg : List Frame} {o ρ : Ty} {ε₀ : Row}
    {Φ : List Rgn} (h : ContOk Δ S seg o ρ ε₀ Φ) : ContOk Δ S' seg o ρ ε₀ Φ :=
  fun S'' hle' st ε' ϕ' hst hr hΦ => h S'' (hle.trans hle') st ε' ϕ' hst hr hΦ

theorem StackOk.tail {S : StoreTy} {st : List Frame} {τ : Ty} {ε : Row} {ϕ : List Rgn}
    (h : StackOk Δ S st τ ε ϕ) :
    ∀ {fr : Frame} {st' : List Frame}, st = fr :: st' →
      ∃ τ' ε' ϕ', StackOk Δ S st' τ' ε' ϕ' := by
  induction h with
  | nil => intro fr st' e; cases e
  | call _ _ _ _ h _ => intro fr st' e; cases e; exact ⟨_, _, _, h⟩
  | handler _ _ _ _ h _ => intro fr st' e; cases e; exact ⟨_, _, _, h⟩
  | label _ h _ => intro fr st' e; cases e; exact ⟨_, _, _, h⟩
  | guard _ _ h _ => intro fr st' e; cases e; exact ⟨_, _, _, h⟩
  | cell _ h _ => intro fr st' e; cases e; exact ⟨_, _, _, h⟩
  | lend _ _ _ _ _ h _ => intro fr st' e; cases e; exact ⟨_, _, _, h⟩
  | lendLoose _ _ _ h _ => intro fr st' e; cases e; exact ⟨_, _, _, h⟩
  | yield _ h _ => intro fr st' e; cases e; exact ⟨_, _, _, h⟩
  | exit _ _ h _ => intro fr st' e; cases e; exact ⟨_, _, _, h⟩
  | never _ ih => intro fr st' e; exact ih e

/-! ## Finding the handler of an operation -/

theorem lookup_cons_eq {β : Type} (k : Nat) (b : β) (as : List (Nat × β)) :
    List.lookup k ((k, b) :: as) = some b := by
  simp

theorem lookup_cons_ne {β : Type} {a k : Nat} (h : a ≠ k) (b : β) (as : List (Nat × β)) :
    List.lookup a ((k, b) :: as) = List.lookup a as := by
  have hb : (a == k) = false := by simpa using h
  simp [List.lookup_cons, hb]

/-- How the function serving an operation is entered, by whether the operation
can be resumed. -/
def ArmEnters (Δ : Ctx) (Cs : List Ty) (ρ : Ty) (ε : Row) (Φ : List Rgn) (arm : Nat)
    (Ps : List Ty) : Option Ty → Prop
  | none => Enters Δ arm Cs Ps ρ ε Φ
  | some o => Enters Δ arm Cs (Ps ++ [.fn 0 [o] ρ ε true none Φ]) ρ ε Φ

theorem ArmsOk.lookup_none {Cs : List Ty} {ρ : Ty} {ε : Row} {Φ : List Rgn}
    {ops : List (Nat × Nat)} {H : Row} (h : ArmsOk Δ Cs ρ ε Φ ops H) {op : Nat} :
    H.lookup op = none → ops.lookup op = none := by
  induction h with
  | nil => intro _; rfl
  | @terminal op' arm targs Ps ops H _ _ _ ih =>
    intro hl
    by_cases he : op = op'
    · subst he
      rw [lookup_cons_eq] at hl
      cases hl
    · rw [lookup_cons_ne he] at hl ⊢
      exact ih hl
  | @resumptive op' arm targs Ps o ops H _ _ _ ih =>
    intro hl
    by_cases he : op = op'
    · subst he
      rw [lookup_cons_eq] at hl
      cases hl
    · rw [lookup_cons_ne he] at hl ⊢
      exact ih hl

theorem ArmsOk.lookup_some {Cs : List Ty} {ρ : Ty} {ε : Row} {Φ : List Rgn}
    {ops : List (Nat × Nat)} {H : Row} (h : ArmsOk Δ Cs ρ ε Φ ops H) {op : Nat}
    {targs : List Ty} :
    H.lookup op = some targs →
    ∃ arm Ps r, ops.lookup op = some arm ∧ Δ.opSig op targs = some (Ps, r)
      ∧ ArmEnters Δ Cs ρ ε Φ arm Ps r := by
  induction h with
  | nil => intro hl; simp [List.lookup] at hl
  | @terminal op' arm targs' Ps' ops H hop hent _ ih =>
    intro hl
    by_cases he : op = op'
    · subst he
      rw [lookup_cons_eq] at hl
      cases hl
      exact ⟨arm, Ps', none, lookup_cons_eq .., hop, hent⟩
    · rw [lookup_cons_ne he] at hl
      obtain ⟨arm', Ps, r, hl', hop', hent'⟩ := ih hl
      exact ⟨arm', Ps, r, by rw [lookup_cons_ne he]; exact hl', hop', hent'⟩
  | @resumptive op' arm targs' Ps' o ops H hop hent _ ih =>
    intro hl
    by_cases he : op = op'
    · subst he
      rw [lookup_cons_eq] at hl
      cases hl
      exact ⟨arm, Ps', some o, lookup_cons_eq .., hop, hent⟩
    · rw [lookup_cons_ne he] at hl
      obtain ⟨arm', Ps, r, hl', hop', hent'⟩ := ih hl
      exact ⟨arm', Ps, r, by rw [lookup_cons_ne he]; exact hl', hop', hent'⟩

theorem findHandler_skip {op : Nat} {fr : Frame} {st : List Frame} {d : Dispatch Frame}
    (hfr : handles Frame.asHandler op fr = none)
    (hd : findHandler Frame.asHandler op st = some d) :
    findHandler Frame.asHandler op (fr :: st)
      = some ⟨fr :: d.above, d.id, d.handler, d.arm, d.below⟩ := by
  simp [findHandler, hfr, hd]

/--
An operation the stack's type offers has a handler on the stack, and the
machine's search finds it. The function serving the operation is entered at the
operation's declared type; the stack below the handler takes what the handler
yields and grants what it touches; and the frames above the handler, with the
handler, can be put on any later stack that suits the handler and are typed
there as they are here.
-/
theorem find_ok {S : StoreTy} {st : List Frame} {τ : Ty} {ε : Row} {ϕ : List Rgn}
    (hst : StackOk Δ S st τ ε ϕ) :
    ∀ {op : Nat} {targs : List Ty}, ε.lookup op = some targs →
    ∃ d ρ ε₀ Φ εb ϕb Cs Ps r, findHandler Frame.asHandler op st = some d
      ∧ S.handlers d.id = some (ρ, ε₀, Φ)
      ∧ HasVals Δ S d.handler.caps Cs ∧ (∀ c, c ∈ Cs → Δ.dup c)
      ∧ Δ.opSig op targs = some (Ps, r)
      ∧ ArmEnters Δ Cs ρ ε₀ Φ d.arm Ps r
      ∧ StackOk Δ S d.below ρ εb ϕb ∧ Row.le ε₀ εb ∧ Sub Φ ϕb
      ∧ (∃ fr, fr ∈ st ∧ fr.isTarget (.handler d.id) = true)
      ∧ (∀ S', S.Le S' → ∀ st' ε' ϕ', StackOk Δ S' st' ρ ε' ϕ' → Row.le ε₀ ε' → Sub Φ ϕ' →
          StackOk Δ S' (d.above ++ .handler d.id d.handler :: st') τ ε ϕ)
      ∧ (Δ.regions ∧ Δ.loans → ∀ uniq a b, Frame.lend uniq a b ∉ d.above) := by
  induction hst with
  | nil => intro op targs hl; simp [List.lookup] at hl
  | @call env body st Γ σ τ εb ε ϕb ϕ henv hbody hrow hsub _ ih =>
    intro op targs hl
    obtain ⟨d, ρ, ε₀, Φ, εb', ϕb', Cs, Ps, r, hf, hid, hcaps, hdup, hop, hent, hbelow, hble, hΦ,
      ⟨fr, hfr, hft⟩, hre, hq⟩ := ih hl
    exact ⟨_, ρ, ε₀, Φ, εb', ϕb', Cs, Ps, r,
      findHandler_skip (by simp [handles, Frame.asHandler]) hf, hid,
      hcaps, hdup, hop, hent, hbelow, hble, hΦ, ⟨fr, List.mem_cons_of_mem _ hfr, hft⟩,
      fun S' hle st' ε' ϕ' hst' hr hs =>
        .call (henv.mono hle) hbody hrow hsub (hre S' hle st' ε' ϕ' hst' hr hs),
      fun hB u a' b' hm => by
        rcases List.mem_cons.mp hm with h | h
        · cases h
        · exact hq hB u a' b' h⟩
  | @handler id h st σ ρ H ε₀ ε Φ ϕ hid hh hrow hsub hrest ih =>
    intro op targs hl
    obtain ⟨Cs, hcaps, hok⟩ := hh
    rw [List.lookup_append] at hl
    cases hH : H.lookup op with
    | none =>
      rw [hH] at hl
      have hl' : ε.lookup op = some targs := hrow _ _ (by simpa using hl)
      obtain ⟨d, ρ', ε₀', Φ', εb', ϕb', Cs', Ps, r, hf, hid', hcaps', hdup, hop, hent, hbelow,
        hble, hΦ, ⟨fr, hfr, hft⟩, hre, hq⟩ := ih hl'
      have hskip : handles Frame.asHandler op (.handler id h) = none := by
        simp [handles, Frame.asHandler, hok.arms.lookup_none hH]
      exact ⟨_, ρ', ε₀', Φ', εb', ϕb', Cs', Ps, r, findHandler_skip hskip hf, hid', hcaps', hdup,
        hop, hent, hbelow, hble, hΦ, ⟨fr, List.mem_cons_of_mem _ hfr, hft⟩,
        fun S' hle st' ε' ϕ' hst' hr hs =>
          .handler (hle.handlers _ _ hid) (HandlerRt.mono hle ⟨Cs, hcaps, hok⟩) hrow hsub
            (hre S' hle st' ε' ϕ' hst' hr hs),
      fun hB u a' b' hm => by
        rcases List.mem_cons.mp hm with h | h
        · cases h
        · exact hq hB u a' b' h⟩
    | some found =>
      rw [hH] at hl
      have e : found = targs := by simpa using hl
      subst e
      obtain ⟨arm, Ps, r, harm, hop, hent⟩ := hok.arms.lookup_some hH
      have hfind : findHandler Frame.asHandler op (.handler id h :: st)
          = some ⟨[], id, h, arm, st⟩ := by
        simp [findHandler, handles, Frame.asHandler, harm]
      exact ⟨_, ρ, ε₀, Φ, ε, ϕ, Cs, Ps, r, hfind, hid, hcaps, hok.dup, hop, hent, hrest, hrow,
        hsub, ⟨.handler id h, List.mem_cons_self .., by simp [Frame.isTarget]⟩,
        fun S' hle st' ε' ϕ' hst' hr hs =>
          .handler (hle.handlers _ _ hid) (HandlerRt.mono hle ⟨Cs, hcaps, hok⟩) hr hs hst',
        fun _ _ _ _ hm => by cases hm⟩
  | @label id st τ ε ϕ hid _ ih =>
    intro op targs hl
    obtain ⟨d, ρ, ε₀, Φ, εb', ϕb', Cs, Ps, r, hf, hid', hcaps, hdup, hop, hent, hbelow, hble, hΦ,
      ⟨fr, hfr, hft⟩, hre, hq⟩ := ih hl
    exact ⟨_, ρ, ε₀, Φ, εb', ϕb', Cs, Ps, r,
      findHandler_skip (by simp [handles, Frame.asHandler]) hf, hid',
      hcaps, hdup, hop, hent, hbelow, hble, hΦ, ⟨fr, List.mem_cons_of_mem _ hfr, hft⟩,
      fun S' hle st' ε' ϕ' hst' hr hs =>
        .label (hle.labels _ _ hid) (hre S' hle st' ε' ϕ' hst' hr hs),
      fun hB u a' b' hm => by
        rcases List.mem_cons.mp hm with h | h
        · cases h
        · exact hq hB u a' b' h⟩
  | @guard fn captures st Cs' σc τ ε ϕ hgs hgc _ ih =>
    intro op targs hl
    obtain ⟨d, ρ, ε₀, Φ, εb', ϕb', Cs, Ps, r, hf, hid', hcaps, hdup, hop, hent, hbelow, hble, hΦ,
      ⟨fr, hfr, hft⟩, hre, hq⟩ := ih hl
    exact ⟨_, ρ, ε₀, Φ, εb', ϕb', Cs, Ps, r,
      findHandler_skip (by simp [handles, Frame.asHandler]) hf, hid',
      hcaps, hdup, hop, hent, hbelow, hble, hΦ, ⟨fr, List.mem_cons_of_mem _ hfr, hft⟩,
      fun S' hle st' ε' ϕ' hst' hr hs =>
        .guard hgs (hgc.mono hle) (hre S' hle st' ε' ϕ' hst' hr hs),
      fun hB u a' b' hm => by
        rcases List.mem_cons.mp hm with h | h
        · cases h
        · exact hq hB u a' b' h⟩
  | @cell a st σ τ ε ϕ hc _ ih =>
    intro op targs hl
    obtain ⟨d, ρ, ε₀, Φ, εb', ϕb', Cs, Ps, r, hf, hid', hcaps, hdup, hop, hent, hbelow, hble, hΦ,
      ⟨fr, hfr, hft⟩, hre, hq⟩ := ih hl
    exact ⟨_, ρ, ε₀, Φ, εb', ϕb', Cs, Ps, r,
      findHandler_skip (by simp [handles, Frame.asHandler]) hf, hid',
      hcaps, hdup, hop, hent, hbelow, hble, hΦ, ⟨fr, List.mem_cons_of_mem _ hfr, hft⟩,
      fun S' hle st' ε' ϕ' hst' hr hs =>
        .cell (hle.cells _ _ hc) (hre S' hle st' ε' ϕ' hst' hr hs),
      fun hB u a' b' hm => by
        rcases List.mem_cons.mp hm with h | h
        · cases h
        · exact hq hB u a' b' h⟩
  | lend _ _ _ _ _ _ _ => intro op targs hl; simp [List.lookup] at hl
  | @lendLoose uniq a b st τ ε ϕ hn hlo hon _ ih =>
    intro op targs hl
    obtain ⟨d, ρ, ε₀, Φ, εb', ϕb', Cs, Ps, r, hf, hid', hcaps, hdup, hop, hent, hbelow, hble, hΦ,
      ⟨fr, hfr, hft⟩, hre, hq⟩ := ih hl
    exact ⟨_, ρ, ε₀, Φ, εb', ϕb', Cs, Ps, r,
      findHandler_skip (by simp [handles, Frame.asHandler]) hf, hid',
      hcaps, hdup, hop, hent, hbelow, hble, hΦ, ⟨fr, List.mem_cons_of_mem _ hfr, hft⟩,
      fun S' hle st' ε' ϕ' hst' hr hs =>
        .lendLoose hn (hle.loans _ _ hlo)
          (fun hR => by
            obtain ⟨ρ', h1, h2⟩ := hon hR
            exact ⟨ρ', h1.mono hle, h2⟩) (hre S' hle st' ε' ϕ' hst' hr hs),
      fun hB => absurd hB hn⟩
  | @yield w st σ τ ε ϕ hw _ ih =>
    intro op targs hl
    obtain ⟨d, ρ, ε₀, Φ, εb', ϕb', Cs, Ps, r, hf, hid', hcaps, hdup, hop, hent, hbelow, hble, hΦ,
      ⟨fr, hfr, hft⟩, hre, hq⟩ := ih hl
    exact ⟨_, ρ, ε₀, Φ, εb', ϕb', Cs, Ps, r,
      findHandler_skip (by simp [handles, Frame.asHandler]) hf, hid',
      hcaps, hdup, hop, hent, hbelow, hble, hΦ, ⟨fr, List.mem_cons_of_mem _ hfr, hft⟩,
      fun S' hle st' ε' ϕ' hst' hr hs =>
        .yield (hw.mono hle) (hre S' hle st' ε' ϕ' hst' hr hs),
      fun hB u a' b' hm => by
        rcases List.mem_cons.mp hm with h | h
        · cases h
        · exact hq hB u a' b' h⟩
  | exit _ _ _ _ => intro op targs hl; simp [List.lookup] at hl
  | never _ ih =>
    intro op targs hl
    obtain ⟨d, ρ, ε₀, Φ, εb', ϕb', Cs, Ps, r, hf, hid', hcaps, hdup, hop, hent, hbelow, hble, hΦ,
      hin, hre, hq⟩ := ih hl
    exact ⟨d, ρ, ε₀, Φ, εb', ϕb', Cs, Ps, r, hf, hid', hcaps, hdup, hop, hent, hbelow, hble, hΦ,
      hin, fun S' hle st' ε' ϕ' hst' hr hs => .never (hre S' hle st' ε' ϕ' hst' hr hs), hq⟩

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

theorem StackOk.label_target {S : StoreTy} {st : List Frame} {τ : Ty} {ε : Row}
    {ϕ : List Rgn} (h : StackOk Δ S st τ ε ϕ) :
    ∀ {fr : Frame} {st' : List Frame} {id : Nat} {σ : Ty}, st = fr :: st' →
      fr.isTarget (.label id) = true → S.labels id = some σ →
      ∃ ε' ϕ', StackOk Δ S st' σ ε' ϕ' := by
  induction h with
  | label hid hrest _ =>
    intro fr st' id σ e ht hl
    cases e
    simp [Frame.isTarget] at ht
    subst ht
    rw [hl] at hid
    cases hid
    exact ⟨_, _, hrest⟩
  | never _ ih => intro fr st' id σ e ht hl; exact ih e ht hl
  | _ => intro fr st' id σ e ht _; cases e <;> simp [Frame.isTarget] at ht

theorem StackOk.handler_target {S : StoreTy} {st : List Frame} {τ : Ty} {ε : Row}
    {ϕ : List Rgn} (h : StackOk Δ S st τ ε ϕ) :
    ∀ {fr : Frame} {st' : List Frame} {id : Nat} {ρ : Ty} {ε₀ : Row} {Φ : List Rgn},
      st = fr :: st' → fr.isTarget (.handler id) = true → S.handlers id = some (ρ, ε₀, Φ) →
      ∃ ε' ϕ', StackOk Δ S st' ρ ε' ϕ' ∧ Row.le ε₀ ε' ∧ Sub Φ ϕ' := by
  induction h with
  | handler hid _ hrow hsub hrest _ =>
    intro fr st' id ρ ε₀ Φ e ht hl
    cases e
    simp [Frame.isTarget] at ht
    subst ht
    rw [hl] at hid
    cases hid
    exact ⟨_, _, hrest, hrow, hsub⟩
  | never _ ih => intro fr st' id ρ ε₀ Φ e ht hl; exact ih e ht hl
  | _ => intro fr st' id ρ ε₀ Φ e ht _; cases e <;> simp [Frame.isTarget] at ht

/-- A guard on a typed stack has a typed cleanup, and what is below it is typed. -/
theorem StackOk.guard_inv {S : StoreTy} {st : List Frame} {τ : Ty} {ε : Row} {ϕ : List Rgn}
    (h : StackOk Δ S st τ ε ϕ) :
    ∀ {fn : Nat} {captures : List Value} {st' : List Frame}, st = .guard fn captures :: st' →
      ∃ Cs σc τ' ε' ϕ', Enters Δ fn Cs [] σc [] ϕ' ∧ HasVals Δ S captures Cs
        ∧ StackOk Δ S st' τ' ε' ϕ' := by
  induction h with
  | guard hent hc hrest _ =>
    intro fn captures st' e
    cases e
    exact ⟨_, _, _, _, _, hent, hc, hrest⟩
  | never _ ih => intro fn captures st' e; exact ih e
  | _ => intro fn captures st' e; cases e

/-- A stack grants only regions of things the store typing knows: so a new
cell, label or borrow is none of them. -/
theorem StackOk.known {S : StoreTy} {st : List Frame} {τ : Ty} {ε : Row} {ϕ : List Rgn}
    (h : StackOk Δ S st τ ε ϕ) : ∀ x, x ∈ Rgn.flat ϕ → Known S x := by
  induction h with
  | nil => intro x hx; cases hx
  | call _ _ _ _ _ ih => exact ih
  | handler _ _ _ hΦ _ ih => exact fun x hx => ih x (hΦ x hx)
  | label hl _ ih =>
    intro x hx
    rw [Rgn.flat_cons_atom rfl] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, hl⟩
    · exact ih x hx
  | guard _ _ _ ih => exact ih
  | cell hc _ ih =>
    intro x hx
    rw [Rgn.flat_cons_atom rfl, Rgn.flat_cons_atom rfl] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, hc⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨_, hc⟩
      · exact ih x hx
  | @lend uniq a b st τ ε ϕ ρ hl _ _ _ _ _ ih =>
    intro x hx
    rw [flat_lent] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, hl⟩
    · rcases List.mem_append.mp hx with hx | hx
      · cases uniq with
        | false => cases hx
        | true =>
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨_, hl⟩
          · cases hx
      · exact ih x (List.mem_filter.mp hx).1
  | lendLoose _ hl _ _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, hl⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨_, hl⟩
      · exact ih x hx
  | yield _ _ ih => exact ih
  | exit _ _ _ ih => exact ih
  | never _ ih => exact ih

/-- Releasing a cell keeps the store typed: a released cell keeps its type. -/
theorem StoreOk.release {S : StoreTy} {store : Store Frame} (hs : StoreOk Δ S store) (a : Nat) :
    StoreOk Δ S (store.release a) := by
  refine ⟨hs.conts, hs.labels, hs.handlers, fun a' τ' h => ?_, hs.loans, hs.quiet⟩
  obtain ⟨hlt, hv⟩ := hs.cells a' τ' h
  refine ⟨by simpa [Store.release] using hlt, fun v hg => ?_⟩
  simp only [Store.release] at hg
  rw [List.getElem?_set] at hg
  by_cases he : a = a'
  · subst he
    simp at hg
  · simp [he] at hg
    exact hv v hg

/--
Delivering a value to a typed stack that takes it, and leaving a typed stack
for a target that is on it, both end well: in a typed state or with the
program's result. The state holds no more than the value, or what the exit
carries, and the stack did. Proved together, as the two are defined together.
-/
theorem deliver_leave_safe {p : Program} {S : StoreTy} (hp : ProgramOk Δ p) :
    ∀ (st : List Frame) {store : Store Frame}, StoreOk Δ S store →
    (∀ {v : Value} {τ : Ty} {ε : Row} {ϕ : List Rgn}, StackOk Δ S st τ ε ϕ → HasVal Δ S v τ →
        Safe Δ S (fun id => occ id v + occStack id st) store (deliver p v st store))
    ∧ (∀ {target : Target} {after : After} {τ : Ty} {ε : Row} {ϕ : List Rgn},
        StackOk Δ S st τ ε ϕ → ExitOk Δ S target after →
        (∃ fr, fr ∈ st ∧ fr.isTarget target = true) →
        Safe Δ S (fun id => occAfter id after + occStack id st) store
          (leave p target after st store)) := by
  intro st
  induction st with
  | nil =>
    intro store hs
    refine ⟨fun _ _ => ?_, fun _ _ hin => ?_⟩
    · exact True.intro
    · obtain ⟨fr, hfr, _⟩ := hin
      cases hfr
  | cons fr st ih =>
    intro store hs
    obtain ⟨ihd, ihl⟩ := ih hs
    refine ⟨@fun v τ ε ϕ hst hv => ?_, @fun target after τ ε ϕ hst hx hin => ?_⟩
    · cases hst with
      | @call env body _ Γ σ τ' εb ε' ϕb ϕ' henv hbody hrow hsub hrest =>
        show Safe Δ S _ store (.next ⟨body, env ++ [v], st, store⟩)
        refine ⟨.mk (henv.snoc hv) hbody hrow hsub hrest hs, Kept.refl _, fun id => ?_⟩
        have := occEnv_push id env v (fv body)
        show occEnv id (env ++ [v]) (fv body) + occStack id st
          ≤ occ id v + occStack id (.call env body :: st)
        simp only [occStack, occFrame]
        omega
      | handler hid hh hrow hsub hrest =>
        obtain ⟨Cs, hcaps, hok⟩ := hh
        exact (enter_safe hp hok.ret hcaps (.cons hv .nil) hrow hsub hrest hs).weaken
          fun id => by simp only [occStack, occFrame, occs]; omega
      | label hid hrest =>
        exact (ihd hrest hv).weaken fun id => by simp only [occStack, occFrame]; omega
      | guard hent hc hrest =>
        exact (enter_safe hp hent hc .nil (Row.nil_le _) (Sub.refl _) (.yield hv hrest) hs).weaken
          fun id => by simp only [occStack, occFrame, occs]; omega
      | @cell a _ _ _ _ _ _ hrest =>
        exact (((ih (hs.release a)).1 hrest hv).release).weaken
          fun id => by simp only [occStack, occFrame]; omega
      | lend _ _ _ _ _ hrest =>
        exact (ihd hrest hv).weaken fun id => by simp only [occStack, occFrame]; omega
      | lendLoose _ _ _ hrest =>
        exact (ihd hrest hv).weaken fun id => by simp only [occStack, occFrame]; omega
      | yield hw hrest =>
        exact (ihd hrest hw).weaken fun id => by simp only [occStack, occFrame]; omega
      | exit hx hin hrest =>
        exact (ihl hrest hx hin).weaken fun id => by simp only [occStack, occFrame]; omega
      | never _ => exact hv.not_never.elim
    · by_cases ht : fr.isTarget target = true
      · cases hx with
        | label hl hv =>
          obtain ⟨ε', ϕ', hrest⟩ := hst.label_target rfl ht hl
          rw [leave_target_yield ht]
          exact (ihd hrest hv).weaken fun id => by simp only [occStack, occAfter]; omega
        | handler hh hent hc ha =>
          obtain ⟨ε', ϕ', hrest, hrow, hsub⟩ := hst.handler_target rfl ht hh
          rw [leave_target_invoke ht]
          exact (enter_safe hp hent hc ha hrow hsub hrest hs).weaken
            fun id => by simp only [occStack, occAfter]; omega
      · have hin' : ∃ fr', fr' ∈ st ∧ fr'.isTarget target = true := by
          obtain ⟨f, hf, hft⟩ := hin
          rcases List.mem_cons.mp hf with rfl | hf
          · exact absurd hft ht
          · exact ⟨f, hf, hft⟩
        obtain ⟨τ', ε', ϕ', hrest⟩ := hst.tail rfl
        cases fr with
        | guard fn captures =>
          obtain ⟨Cs, σc, τ'', ε'', ϕ'', hent, hc, hrest'⟩ := hst.guard_inv rfl
          rw [leave_guard ht]
          exact (enter_safe hp hent hc .nil (Row.nil_le _) (Sub.refl _)
            (.exit hx hin' hrest') hs).weaken
            fun id => by simp only [occStack, occFrame, occs]; omega
        | call env body =>
          have h1 : leave p target after (.call env body :: st) store
              = leave p target after st store := by simp [leave, ht]
          rw [h1]
          exact (ihl hrest hx hin').weaken fun id => by simp only [occStack]; omega
        | handler id h =>
          have h1 : leave p target after (.handler id h :: st) store
              = leave p target after st store := by simp [leave, ht]
          rw [h1]
          exact (ihl hrest hx hin').weaken fun id => by simp only [occStack]; omega
        | label id =>
          have h1 : leave p target after (.label id :: st) store
              = leave p target after st store := by simp [leave, ht]
          rw [h1]
          exact (ihl hrest hx hin').weaken fun id => by simp only [occStack]; omega
        | lend uniq a b =>
          have h1 : leave p target after (.lend uniq a b :: st) store
              = leave p target after st store := by simp [leave, ht]
          rw [h1]
          exact (ihl hrest hx hin').weaken fun id => by simp only [occStack]; omega
        | cell a =>
          have h1 : leave p target after (.cell a :: st) store
              = leave p target after st (store.release a) := by simp [leave, ht]
          rw [h1]
          exact (((ih (hs.release a)).2 hrest hx hin').release).weaken
            fun id => by simp only [occStack]; omega
        | yield w =>
          have h1 : leave p target after (.yield w :: st) store
              = leave p target after st store := by simp [leave, ht]
          rw [h1]
          exact (ihl hrest hx hin').weaken fun id => by simp only [occStack]; omega
        | exit t a =>
          have h1 : leave p target after (.exit t a :: st) store
              = leave p target after st store := by simp [leave, ht]
          rw [h1]
          exact (ihl hrest hx hin').weaken fun id => by simp only [occStack]; omega

theorem deliver_safe {p : Program} {S : StoreTy} {store : Store Frame} {st : List Frame}
    {v : Value} {τ : Ty} {ε : Row} {ϕ : List Rgn} (hp : ProgramOk Δ p) (hs : StoreOk Δ S store)
    (hst : StackOk Δ S st τ ε ϕ) (hv : HasVal Δ S v τ) :
    Safe Δ S (fun id => occ id v + occStack id st) store (deliver p v st store) :=
  (deliver_leave_safe hp st hs).1 hst hv

theorem leave_safe {p : Program} {S : StoreTy} {store : Store Frame} {st : List Frame}
    {target : Target} {after : After} {τ : Ty} {ε : Row} {ϕ : List Rgn} (hp : ProgramOk Δ p)
    (hs : StoreOk Δ S store) (hst : StackOk Δ S st τ ε ϕ) (hx : ExitOk Δ S target after)
    (hin : ∃ fr, fr ∈ st ∧ fr.isTarget target = true) :
    Safe Δ S (fun id => occAfter id after + occStack id st) store
      (leave p target after st store) :=
  (deliver_leave_safe hp st hs).2 hst hx hin

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

/-- A callee applied to typed arguments: what it gives back, the operations it
needs and the regions it touches. -/
inductive CalleeOk (Δ : Ctx) (S : StoreTy) : Callee → Ty → Row → List Rgn → Prop where
  | fn {fn : Nat} {captures vs : List Value} {sig : FnSig} {θ rs : List Rgn} :
      Δ.fnSig fn sig → θ.length = sig.crgns → rs.length = sig.rgns →
      HasVals Δ S captures (sig.caps.map (Ty.inst θ)) →
      HasVals Δ S vs ((sig.params.map (Ty.inst θ)).map (Ty.open rs)) →
      CalleeOk Δ S (.fn fn captures vs) ((sig.ret.inst θ).open rs) ((sig.eff.inst θ).open rs)
        ((sig.acc.map (Rgn.inst θ)).map (Rgn.openAt 0 rs))
  | cont {id : Nat} {v : Value} {o ρ : Ty} {ε : Row} {Φ : List Rgn} :
      S.conts id = some (o, ρ, ε, Φ) → HasVal Δ S v o → CalleeOk Δ S (.cont id v) ρ ε Φ
  | label {id : Nat} {v : Value} {σ ρ : Ty} {ε : Row} {ϕ : List Rgn} :
      S.labels id = some σ → HasVal Δ S v σ → CalleeOk Δ S (.label id v) ρ ε ϕ

/-- The two ways applying a typed callee can fail. -/
inductive Faulty (st : List Frame) (store : Store Frame) : Callee → Prop where
  | resumed {id : Nat} {v : Value} : store.conts[id]? = some none → Faulty st store (.cont id v)
  | dead {id : Nat} {v : Value} :
      findLabel Frame.asLabel id st = none → Faulty st store (.label id v)

/-- Taking a resumption's frames out of a typed store leaves a typed store. -/
theorem StoreOk.take {S : StoreTy} {conts : Conts Frame} {labels : Nat} {cells : Cells}
    (hs : StoreOk Δ S ⟨conts, labels, cells⟩) (id : Nat) :
    StoreOk Δ S ⟨conts.set id none, labels, cells⟩ := by
  refine ⟨fun id' o ρ ε₀ Φ h => ?_, hs.labels, hs.handlers, hs.cells, hs.loans,
    fun hB k seg hk => hs.quiet hB k seg (by
      have hk' : (conts.set id none)[k]? = some (some seg) := hk
      rw [List.getElem?_set] at hk'
      by_cases he : id = k
      · subst he
        by_cases hlt : id < conts.length
        · simp [hlt] at hk'
        · simp [hlt] at hk'
      · simpa [he] using hk')⟩
  obtain ⟨hlt, hseg⟩ := hs.conts id' o ρ ε₀ Φ h
  refine ⟨by simpa using hlt, fun seg hget => ?_⟩
  rw [List.getElem?_set] at hget
  by_cases he : id = id'
  · subst he
    simp at hget
  · simp [he] at hget
    exact hseg seg hget

/-- How many times a callee holds resumption `id`: in the callable applied,
which may itself be that resumption, and in its arguments. -/
def occCallee (id : Nat) : Callee → Nat
  | .fn _ captures vs => occs id captures + occs id vs
  | .cont k v => (if k = id then 1 else 0) + occ id v
  | .label _ v => occ id v

/-- Applying a typed callee on a stack that takes its result, serves its
operations and grants its regions ends well, unless it is a used resumption or
a label whose scope has ended. Resuming a resumption takes its frames out of
the store. -/
theorem apply_ok {p : Program} {S : StoreTy} {store : Store Frame} {st : List Frame}
    {c : Callee} {σ : Ty} {ε' ε : Row} {ϕ' ϕ : List Rgn} (hp : ProgramOk Δ p)
    (hs : StoreOk Δ S store) (hc : CalleeOk Δ S c σ ε' ϕ') (hst : StackOk Δ S st σ ε ϕ)
    (hle : Row.le ε' ε) (hsub : Sub ϕ' ϕ) (hnd : Δ.loans → (Rgn.flat ϕ').Nodup) :
    ((∀ k v, c ≠ .cont k v)
        ∧ Safe Δ S (fun id => occCallee id c + occStack id st) store (apply p c st store))
      ∨ (∃ k v seg, c = .cont k v ∧ store.conts[k]? = some (some seg)
          ∧ Safe Δ S (fun id => occ id v + occStack id seg + occStack id st)
              ⟨store.conts.set k none, store.labels, store.cells⟩ (apply p c st store))
      ∨ (apply p c st store = .stuck ∧ Faulty st store c) := by
  cases hc with
  | fn hsig hθ hrs hcaps hvs =>
    exact .inl ⟨(fun _ _ h => by cases h),
      (callFn_safe hp hsig hθ hrs hcaps hvs hle hsub hnd hst hs).weaken
        fun id => by simp only [occCallee]; omega⟩
  | @cont id v o ρ ε' _ hk hv =>
    obtain ⟨conts, labels, cells⟩ := store
    obtain ⟨hlt, hseg⟩ := hs.conts id o σ ε' _ hk
    cases hget : conts[id]? with
    | none =>
      have := List.getElem?_eq_none_iff.mp hget
      exact absurd hlt (by simpa using this)
    | some x =>
      cases x with
      | none =>
        exact .inr (.inr ⟨by simp [apply, takeCont_none hget], .resumed hget⟩)
      | some seg =>
        obtain ⟨ε'', ϕ'', hst'⟩ := hseg seg hget S (StoreTy.Le.refl S) st ε ϕ hst hle hsub
        have h1 : apply p (.cont id v) st ⟨conts, labels, cells⟩
            = deliver p v (seg ++ st) ⟨conts.set id none, labels, cells⟩ := by
          simp [apply, takeCont_some hget]
        rw [h1]
        exact .inr (.inl ⟨id, v, seg, rfl, hget,
          (deliver_safe hp (hs.take id) hst' hv).weaken
            fun k => by simp only [occStack_append]; omega⟩)
  | @label id v σ' ρ ε' ϕ' hl hv =>
    cases hf : findLabel Frame.asLabel id st with
    | none => exact .inr (.inr ⟨by simp [apply, hf], .dead hf⟩)
    | some r =>
      have h1 : apply p (.label id v) st store = leave p (.label id) (.yield v) st store := by
        simp [apply, hf]
      rw [h1]
      exact .inl ⟨(fun _ _ h => by cases h),
        (leave_safe hp hs hst (.label hl hv) (findLabel_target hf)).weaken
          fun k => by simp only [occCallee, occAfter]; omega⟩

end Glorious.Typing
