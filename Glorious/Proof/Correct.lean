import Glorious.Proof.Simulation
import Glorious.Proof.Patterns

/-!
# Compiler correctness

The bytecode produced by `compile` has exactly the behaviour of the Core program
it was compiled from. The final statements are `compile_correct`,
`compile_emits` and `compile_emits_reflect`.
-/

namespace Glorious

open Machine
open Bytecode (Instr Code)

/-! ## The simulation relation -/

/-- A suspended Core caller is a return frame that resumes its compiled code
with the same locals. Every other kind of frame the bytecode has is identical
in both machines. -/
inductive MatchFrame : Core.Frame → Bytecode.Frame → Prop where
  | call {body : Core.Tm} {ρ : Env} {code : Code} {pc : Nat} :
      CodeAt code pc (compileTm body) → MatchFrame (.call ρ body) (.ret code pc ρ)
  | handler {id : Nat} {h : Handler} : MatchFrame (.handler id h) (.handler id h)
  | label {id : Nat} : MatchFrame (.label id) (.label id)
  | guard {fn : Nat} {captures : List Value} :
      MatchFrame (.guard fn captures) (.guard fn captures)
  | cell {a : Nat} : MatchFrame (.cell a) (.cell a)
  | yield {v : Value} : MatchFrame (.yield v) (.yield v)
  | exit {target : Target} {after : After} :
      MatchFrame (.exit target after) (.exit target after)

theorem MatchFrame.asHandler_eq {f : Core.Frame} {f' : Bytecode.Frame} (h : MatchFrame f f') :
    f.asHandler = f'.asHandler := by
  cases h <;> rfl

theorem MatchFrame.asLabel_eq {f : Core.Frame} {f' : Bytecode.Frame} (h : MatchFrame f f') :
    f.asLabel = f'.asLabel := by
  cases h <;> rfl

theorem MatchFrame.isTarget_eq {f : Core.Frame} {f' : Bytecode.Frame} (h : MatchFrame f f')
    (target : Target) : f.isTarget target = f'.isTarget target := by
  cases h <;> cases target <;> rfl

/-- Stacks correspond frame by frame, but for the scopes of borrows: Core marks
where a borrow ends with a frame, which nothing reads, and the bytecode has no
such frame. -/
inductive MatchFrames : List Core.Frame → List Bytecode.Frame → Prop where
  | nil : MatchFrames [] []
  | cons {f : Core.Frame} {f' : Bytecode.Frame} {stack : List Core.Frame}
      {frames : List Bytecode.Frame} :
      MatchFrame f f' → MatchFrames stack frames → MatchFrames (f :: stack) (f' :: frames)
  | lend {uniq : Bool} {a b : Nat} {stack : List Core.Frame} {frames : List Bytecode.Frame} :
      MatchFrames stack frames → MatchFrames (.lend uniq a b :: stack) frames

theorem MatchFrames.length_le {a : List Core.Frame} {a' : List Bytecode.Frame}
    (h : MatchFrames a a') : a'.length ≤ a.length := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons _ _ ih => simpa using ih
  | lend _ ih => exact Nat.le_succ_of_le ih

theorem MatchFrames.append {a b : List Core.Frame} {a' b' : List Bytecode.Frame}
    (ha : MatchFrames a a') (hb : MatchFrames b b') : MatchFrames (a ++ b) (a' ++ b') := by
  induction ha with
  | nil => exact hb
  | cons hf _ ih => exact .cons hf ih
  | lend _ ih => exact .lend ih

/-- A store entry is used up in both machines, or holds corresponding stacks. -/
inductive MatchCont :
    Option (List Core.Frame) → Option (List Bytecode.Frame) → Prop where
  | empty : MatchCont Option.none Option.none
  | full {s : List Core.Frame} {s' : List Bytecode.Frame} :
      MatchFrames s s' → MatchCont (Option.some s) (Option.some s')

/-- The continuation stores correspond entry by entry, so resumption identities agree. -/
inductive MatchConts : Conts Core.Frame → Conts Bytecode.Frame → Prop where
  | nil : MatchConts [] []
  | cons {a : Option (List Core.Frame)} {b : Option (List Bytecode.Frame)}
      {as : Conts Core.Frame} {bs : Conts Bytecode.Frame} :
      MatchCont a b → MatchConts as bs → MatchConts (a :: as) (b :: bs)

namespace MatchConts

variable {a : Conts Core.Frame} {b : Conts Bytecode.Frame}

theorem length_eq (h : MatchConts a b) : a.length = b.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem snoc {x : Option (List Core.Frame)} {y : Option (List Bytecode.Frame)}
    (h : MatchConts a b) (hx : MatchCont x y) : MatchConts (a ++ [x]) (b ++ [y]) := by
  induction h with
  | nil => exact .cons hx .nil
  | cons hc _ ih => exact .cons hc ih

/-- Taking a continuation out of corresponding stores gives corresponding
stacks and leaves corresponding stores. -/
theorem take (h : MatchConts a b) :
    ∀ {id : Nat} {seg : List Core.Frame} {a₁ : Conts Core.Frame},
    takeCont a id = some (seg, a₁) →
    ∃ seg' b₁, takeCont b id = some (seg', b₁) ∧ MatchFrames seg seg'
      ∧ MatchConts a₁ b₁ := by
  induction h with
  | nil => intro id seg a₁ ht; simp [takeCont] at ht
  | @cons x y as bs hx hrest ih =>
    intro id seg a₁ ht
    cases id with
    | zero =>
      cases hx with
      | empty => simp [takeCont] at ht
      | full hs =>
        simp [takeCont] at ht
        obtain ⟨rfl, rfl⟩ := ht
        exact ⟨_, _, rfl, hs, .cons .empty hrest⟩
    | succ id =>
      cases hr : takeCont as id with
      | none => simp [takeCont, hr] at ht
      | some r =>
        obtain ⟨seg₀, as₁⟩ := r
        simp [takeCont, hr] at ht
        obtain ⟨rfl, rfl⟩ := ht
        obtain ⟨seg', bs₁, hb, hs, hcs⟩ := ih hr
        exact ⟨seg', y :: bs₁, by simp [takeCont, hb], hs, .cons hx hcs⟩

end MatchConts

/-- Searching corresponding stacks for a handler finds the same handler, with
corresponding frames above and below it. -/
theorem find_sim {op : Nat} {stack : List Core.Frame} {frames : List Bytecode.Frame}
    (h : MatchFrames stack frames) : ∀ {d : Dispatch Core.Frame},
    findHandler Core.Frame.asHandler op stack = some d →
    ∃ above' below', findHandler Bytecode.Frame.asHandler op frames
        = some ⟨above', d.id, d.handler, d.arm, below'⟩
      ∧ MatchFrames d.above above' ∧ MatchFrames d.below below' := by
  induction h with
  | nil => intro d hd; simp [findHandler] at hd
  | @cons f f' stack frames hf hrest ih =>
    intro d hd
    have hh : handles Bytecode.Frame.asHandler op f' = handles Core.Frame.asHandler op f := by
      simp [handles, hf.asHandler_eq]
    cases hx : handles Core.Frame.asHandler op f with
    | some r =>
      obtain ⟨id, h, arm⟩ := r
      simp [findHandler, hx] at hd
      subst hd
      exact ⟨[], frames, by simp [findHandler, hh, hx], .nil, hrest⟩
    | none =>
      cases hf₀ : findHandler Core.Frame.asHandler op stack with
      | none => simp [findHandler, hx, hf₀] at hd
      | some d₀ =>
        simp [findHandler, hx, hf₀] at hd
        subst hd
        obtain ⟨above', below', hv, ha, hb⟩ := ih hf₀
        exact ⟨f' :: above', below', by simp [findHandler, hh, hx, hv], .cons hf ha, hb⟩
  | @lend uniq a b stack frames hrest ih =>
    intro d hd
    cases hf₀ : findHandler Core.Frame.asHandler op stack with
    | none => simp [findHandler, handles, Core.Frame.asHandler, hf₀] at hd
    | some d₀ =>
      simp [findHandler, handles, Core.Frame.asHandler, hf₀] at hd
      subst hd
      obtain ⟨above', below', hv, ha, hb⟩ := ih hf₀
      exact ⟨above', below', hv, .lend ha, hb⟩

/-- Searching corresponding stacks for a label scope finds it in both, with
corresponding frames above and below it. -/
theorem findLabel_sim {id : Nat} {stack : List Core.Frame} {frames : List Bytecode.Frame}
    (h : MatchFrames stack frames) : ∀ {above below : List Core.Frame},
    findLabel Core.Frame.asLabel id stack = some (above, below) →
    ∃ above' below', findLabel Bytecode.Frame.asLabel id frames = some (above', below')
      ∧ MatchFrames above above' ∧ MatchFrames below below' := by
  induction h with
  | nil => intro above below hb; simp [findLabel] at hb
  | @cons f f' stack frames hf hrest ih =>
    intro above below hb
    have hl : Bytecode.Frame.asLabel f' = Core.Frame.asLabel f := hf.asLabel_eq.symm
    by_cases he : Core.Frame.asLabel f = some id
    · simp [findLabel, he] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨[], frames, by simp [findLabel, hl, he], .nil, hrest⟩
    · cases hr : findLabel Core.Frame.asLabel id stack with
      | none => simp [findLabel, he, hr] at hb
      | some r =>
        obtain ⟨above₀, below₀⟩ := r
        simp [findLabel, he, hr] at hb
        obtain ⟨rfl, rfl⟩ := hb
        obtain ⟨above', below', hv, ha, hbm⟩ := ih hr
        exact ⟨f' :: above', below', by simp [findLabel, hl, he, hv], .cons hf ha, hbm⟩
  | @lend uniq a b stack frames hrest ih =>
    intro above below hb
    cases hr : findLabel Core.Frame.asLabel id stack with
    | none => simp [findLabel, Core.Frame.asLabel, hr] at hb
    | some r =>
      obtain ⟨above₀, below₀⟩ := r
      simp [findLabel, Core.Frame.asLabel, hr] at hb
      obtain ⟨rfl, rfl⟩ := hb
      obtain ⟨above', below', hv, ha, hbm⟩ := ih hr
      exact ⟨above', below', hv, .lend ha, hbm⟩

/-- The stores correspond: matching continuation entries, the same label counter
and the same memory. -/
inductive MatchStore : Store Core.Frame → Store Bytecode.Frame → Prop where
  | mk {conts : Conts Core.Frame} {conts' : Conts Bytecode.Frame} {labels : Nat}
      {cells : Cells} :
      MatchConts conts conts' → MatchStore ⟨conts, labels, cells⟩ ⟨conts', labels, cells⟩

theorem MatchStore.release {store : Store Core.Frame} {store' : Store Bytecode.Frame}
    (h : MatchStore store store') (a : Nat) : MatchStore (store.release a) (store'.release a) := by
  cases h with
  | mk hcs => exact .mk hcs

theorem MatchStore.alloc {store : Store Core.Frame} {store' : Store Bytecode.Frame}
    (h : MatchStore store store') (v : Value) : MatchStore (store.alloc v) (store'.alloc v) := by
  cases h with
  | mk hcs => exact .mk hcs

/-- The program counter points at the compiled form of the current Core
computation, the locals are the Core environment, and the stacks and stores
correspond. -/
inductive Match : Core.State → Bytecode.State → Prop where
  | mk {tm : Core.Tm} {ρ : Env} {stack : List Core.Frame} {store : Store Core.Frame}
      {code : Code} {pc : Nat} {frames : List Bytecode.Frame} {store' : Store Bytecode.Frame} :
      CodeAt code pc (compileTm tm) → MatchFrames stack frames → MatchStore store store' →
      Match ⟨tm, ρ, stack, store⟩ ⟨code, pc, ρ, frames, store'⟩

theorem match_init (p : Core.Program) : Match (Core.init p) (Bytecode.init (compile p)) :=
  .mk (CodeAt.zero _) .nil (.mk .nil)

/--
How the outcome of a Core step relates to the outcome of the bytecode step
taken from a matching state: if Core moves on, the bytecode moves on and after
some further steps matches again, without touching its stack in between; if
Core halts, the bytecode halts with the same value; if Core is stuck, nothing
is required.
-/
inductive SimOutcome (p : Core.Program) :
    Step Core.State Value → Step Bytecode.State Value → Prop where
  | next {s' : Core.State} {t₀ t' : Bytecode.State} {k : Nat} :
      RunsThrough (Bytecode.step (compile p)) (fun t => t.frames = t'.frames) k t₀ t' →
      Match s' t' → SimOutcome p (.next s') (.next t₀)
  | halt {v : Value} : SimOutcome p (.halt v) (.halt v)
  | stuck {r : Step Bytecode.State Value} : SimOutcome p .stuck r

/-! ## Entering a function -/

/--
When Core selects a clause of a function, the bytecode enters the function's
code, and running it from the start reaches the compiled clause body with the
clause's environment as its locals.
-/
theorem invoke_run {p : Core.Program} {fn : Nat} {captures vs : List Value}
    {body : Core.Tm} {ρ' : Env} (h : Core.invoke p fn captures vs = some (body, ρ'))
    (fr : List Bytecode.Frame) (ks : Store Bytecode.Frame) :
    ∃ code k pc, Bytecode.invoke (compile p) fn captures vs = some (code, vs ++ captures)
      ∧ RunsThrough (Bytecode.step (compile p)) (fun t => t.frames = fr) k
          ⟨code, 0, vs ++ captures, fr, ks⟩ ⟨code, pc, ρ', fr, ks⟩
      ∧ CodeAt code pc (compileTm body) := by
  simp only [Core.invoke] at h
  cases hF : p.fns[fn]? with
  | none => simp [hF] at h
  | some F =>
    cases hs : Core.selectClause F.clauses vs with
    | none => simp [hF, hs] at h
    | some r =>
      obtain ⟨body', bs⟩ := r
      simp [hF, hs] at h
      obtain ⟨rfl, rfl⟩ := h
      have hargs : ∀ j v, vs[j]? = some v → (argPlace j).eval (vs ++ captures) = some v :=
        fun j v hj => argPlace_eval (getElem?_append_of_eq_some hj)
      obtain ⟨k, pc, hk, hbody⟩ :=
        select_run (P := compile p) (fr := fr) (ks := ks) hargs F.clauses 0 hs (CodeAt.zero _)
      rw [List.append_assoc] at hk
      exact ⟨compileClauses 0 F.clauses, k, pc,
        by simp [Bytecode.invoke, compile, compileFn, hF], hk, hbody⟩

section Outcomes

variable {p : Core.Program} {stack : List Core.Frame} {frames : List Bytecode.Frame}
  {store : Store Core.Frame} {store' : Store Bytecode.Frame}

theorem callFn_sim {fn : Nat} {captures vs : List Value}
    (hfr : MatchFrames stack frames) (hks : MatchStore store store') :
    SimOutcome p (Core.callFn p fn captures vs stack store)
      (Bytecode.callFn (compile p) fn captures vs frames store') := by
  cases hi : Core.invoke p fn captures vs with
  | none =>
    have h1 : Core.callFn p fn captures vs stack store = .stuck := by simp [Core.callFn, hi]
    rw [h1]
    exact .stuck
  | some r =>
    obtain ⟨body, ρ'⟩ := r
    obtain ⟨code, k, pc, hinv, hk, hbody⟩ := invoke_run hi frames store'
    have h1 : Core.callFn p fn captures vs stack store = .next ⟨body, ρ', stack, store⟩ := by
      simp [Core.callFn, hi]
    have h2 : Bytecode.callFn (compile p) fn captures vs frames store'
        = .next ⟨code, 0, vs ++ captures, frames, store'⟩ := by
      simp [Bytecode.callFn, hinv]
    rw [h1, h2]
    exact .next hk (.mk hbody hfr hks)

/-- Delivering a value to corresponding stacks, and leaving corresponding
stacks for a target, including the cleanups either may trigger. The two are
proved together because each is defined through the other. -/
theorem deliver_leave_sim (hfr : MatchFrames stack frames) (hks : MatchStore store store') :
    (∀ v : Value, SimOutcome p (Core.deliver p v stack store)
        (Bytecode.deliver (compile p) v frames store'))
    ∧ (∀ (target : Target) (after : After), SimOutcome p (Core.leave p target after stack store)
        (Bytecode.leave (compile p) target after frames store')) := by
  induction hfr generalizing store store' with
  | nil => exact ⟨fun _ => .halt, fun _ _ => .stuck⟩
  | @cons f f' stack frames hf hrest ih =>
    obtain ⟨ihd, ihl⟩ := ih hks
    refine ⟨fun v => ?_, fun target after => ?_⟩
    · cases hf with
      | @call body ρ code pc hc =>
        show SimOutcome p (.next ⟨body, ρ ++ [v], stack, store⟩)
          (.next ⟨code, pc, ρ ++ [v], frames, store'⟩)
        exact .next (RunsThrough.refl rfl) (.mk hc hrest hks)
      | handler => exact callFn_sim hrest hks
      | label => exact ihd v
      | guard => exact callFn_sim (.cons .yield hrest) hks
      | @cell a => exact (ih (hks.release a)).1 v
      | yield => exact ihd _
      | exit => exact ihl _ _
    · by_cases ht : f.isTarget target = true
      · have ht' : f'.isTarget target = true := by rw [← hf.isTarget_eq]; exact ht
        cases after with
        | yield w =>
          have h1 : Core.leave p target (.yield w) (f :: stack) store
              = Core.deliver p w stack store := by simp [Core.leave, ht]
          have h2 : Bytecode.leave (compile p) target (.yield w) (f' :: frames) store'
              = Bytecode.deliver (compile p) w frames store' := by simp [Bytecode.leave, ht']
          rw [h1, h2]
          exact ihd w
        | invoke fn captures args =>
          have h1 : Core.leave p target (.invoke fn captures args) (f :: stack) store
              = Core.callFn p fn captures args stack store := by simp [Core.leave, ht]
          have h2 : Bytecode.leave (compile p) target (.invoke fn captures args) (f' :: frames) store'
              = Bytecode.callFn (compile p) fn captures args frames store' := by
            simp [Bytecode.leave, ht']
          rw [h1, h2]
          exact callFn_sim hrest hks
      · have ht' : ¬ f'.isTarget target = true := by rw [← hf.isTarget_eq]; exact ht
        cases hf with
        | @guard fn captures =>
          have h1 : Core.leave p target after (.guard fn captures :: stack) store
              = Core.callFn p fn captures [] (.exit target after :: stack) store := by
            simp [Core.leave, ht]
          have h2 : Bytecode.leave (compile p) target after (.guard fn captures :: frames) store'
              = Bytecode.callFn (compile p) fn captures [] (.exit target after :: frames) store' := by
            simp [Bytecode.leave, ht']
          rw [h1, h2]
          exact callFn_sim (.cons .exit hrest) hks
        | @call body ρ code pc hc =>
          have h1 : Core.leave p target after (.call ρ body :: stack) store
              = Core.leave p target after stack store := by simp [Core.leave, ht]
          have h2 : Bytecode.leave (compile p) target after (.ret code pc ρ :: frames) store'
              = Bytecode.leave (compile p) target after frames store' := by
            simp [Bytecode.leave, ht']
          rw [h1, h2]
          exact ihl _ _
        | @handler id h =>
          have h1 : Core.leave p target after (.handler id h :: stack) store
              = Core.leave p target after stack store := by simp [Core.leave, ht]
          have h2 : Bytecode.leave (compile p) target after (.handler id h :: frames) store'
              = Bytecode.leave (compile p) target after frames store' := by
            simp [Bytecode.leave, ht']
          rw [h1, h2]
          exact ihl _ _
        | @label id =>
          have h1 : Core.leave p target after (.label id :: stack) store
              = Core.leave p target after stack store := by simp [Core.leave, ht]
          have h2 : Bytecode.leave (compile p) target after (.label id :: frames) store'
              = Bytecode.leave (compile p) target after frames store' := by
            simp [Bytecode.leave, ht']
          rw [h1, h2]
          exact ihl _ _
        | @cell a =>
          have h1 : Core.leave p target after (.cell a :: stack) store
              = Core.leave p target after stack (store.release a) := by simp [Core.leave, ht]
          have h2 : Bytecode.leave (compile p) target after (.cell a :: frames) store'
              = Bytecode.leave (compile p) target after frames (store'.release a) := by
            simp [Bytecode.leave, ht']
          rw [h1, h2]
          exact (ih (hks.release a)).2 _ _
        | @yield w =>
          have h1 : Core.leave p target after (.yield w :: stack) store
              = Core.leave p target after stack store := by simp [Core.leave, ht]
          have h2 : Bytecode.leave (compile p) target after (.yield w :: frames) store'
              = Bytecode.leave (compile p) target after frames store' := by
            simp [Bytecode.leave, ht']
          rw [h1, h2]
          exact ihl _ _
        | @exit t a =>
          have h1 : Core.leave p target after (.exit t a :: stack) store
              = Core.leave p target after stack store := by simp [Core.leave, ht]
          have h2 : Bytecode.leave (compile p) target after (.exit t a :: frames) store'
              = Bytecode.leave (compile p) target after frames store' := by
            simp [Bytecode.leave, ht']
          rw [h1, h2]
          exact ihl _ _

  | @lend uniq a b stack frames hrest ih =>
    obtain ⟨ihd, ihl⟩ := ih hks
    refine ⟨fun v => ihd v, fun target after => ?_⟩
    have h1 : Core.leave p target after (.lend uniq a b :: stack) store
        = Core.leave p target after stack store := by
      cases target <;> simp [Core.leave, Core.Frame.isTarget]
    rw [h1]
    exact ihl _ _

theorem deliver_sim (hfr : MatchFrames stack frames) (hks : MatchStore store store')
    {v : Value} :
    SimOutcome p (Core.deliver p v stack store) (Bytecode.deliver (compile p) v frames store') :=
  (deliver_leave_sim hfr hks).1 v

theorem leave_sim (hfr : MatchFrames stack frames) (hks : MatchStore store store')
    {target : Target} {after : After} :
    SimOutcome p (Core.leave p target after stack store)
      (Bytecode.leave (compile p) target after frames store') :=
  (deliver_leave_sim hfr hks).2 target after

theorem apply_sim {c : Callee} (hfr : MatchFrames stack frames) (hks : MatchStore store store') :
    SimOutcome p (Core.apply p c stack store) (Bytecode.apply (compile p) c frames store') := by
  cases c with
  | fn fn captures vs => exact callFn_sim hfr hks
  | cont id v =>
    obtain @⟨conts, conts', labels, cells, hcs⟩ := hks
    cases ht : takeCont conts id with
    | none =>
      have h1 : Core.apply p (.cont id v) stack ⟨conts, labels, cells⟩ = .stuck := by
        simp [Core.apply, ht]
      rw [h1]
      exact .stuck
    | some r =>
      obtain ⟨seg, conts₁⟩ := r
      obtain ⟨seg', conts₁', ht', hseg, hcs₁⟩ := hcs.take ht
      have h1 : Core.apply p (.cont id v) stack ⟨conts, labels, cells⟩
          = Core.deliver p v (seg ++ stack) ⟨conts₁, labels, cells⟩ := by
        simp [Core.apply, ht]
      have h2 : Bytecode.apply (compile p) (.cont id v) frames ⟨conts', labels, cells⟩
          = Bytecode.deliver (compile p) v (seg' ++ frames) ⟨conts₁', labels, cells⟩ := by
        simp [Bytecode.apply, ht']
      rw [h1, h2]
      exact deliver_sim (hseg.append hfr) (.mk hcs₁)
  | label id v =>
    cases hl : findLabel Core.Frame.asLabel id stack with
    | none =>
      have h1 : Core.apply p (.label id v) stack store = .stuck := by simp [Core.apply, hl]
      rw [h1]
      exact .stuck
    | some r =>
      obtain ⟨above, below⟩ := r
      obtain ⟨above', below', hl', ha, hb⟩ := findLabel_sim hfr hl
      have h1 : Core.apply p (.label id v) stack store
          = Core.leave p (.label id) (.yield v) stack store := by
        simp [Core.apply, hl]
      have h2 : Bytecode.apply (compile p) (.label id v) frames store'
          = Bytecode.leave (compile p) (.label id) (.yield v) frames store' := by
        simp [Bytecode.apply, hl']
      rw [h1, h2]
      exact leave_sim hfr hks

end Outcomes

/-! ## One Core step is one or more bytecode steps

First for steps of the machine state alone, then for programs in their world. -/

theorem step_sim (p : Core.Program) {s : Core.State} {t : Bytecode.State} (hm : Match s t) :
    SimOutcome p (Core.step p s) (Bytecode.step (compile p) t) := by
  obtain @⟨tm, ρ, stack, store, code, pc, frames, store', hcode, hfr, hstore⟩ := hm
  obtain @⟨conts, conts', labels, cells, hcs⟩ := hstore
  have hks : MatchStore ⟨conts, labels, cells⟩ ⟨conts', labels, cells⟩ := .mk hcs
  cases tm with
  | ret a =>
    have hc : CodeAt code pc [Instr.ret a] := hcode
    have hi := hc.head
    cases ha : a.eval ρ with
    | none =>
      have h1 : Core.step p ⟨.ret a, ρ, stack, ⟨conts, labels, cells⟩⟩ = .stuck := by simp [Core.step, ha]
      rw [h1]
      exact .stuck
    | some v =>
      have h1 : Core.step p ⟨.ret a, ρ, stack, ⟨conts, labels, cells⟩⟩ = Core.deliver p v stack ⟨conts, labels, cells⟩ := by
        simp [Core.step, ha]
      have h2 : Bytecode.step (compile p) ⟨code, pc, ρ, frames, ⟨conts', labels, cells⟩⟩
          = Bytecode.deliver (compile p) v frames ⟨conts', labels, cells⟩ := by
        simp [Bytecode.step, hi, ha]
      rw [h1, h2]
      exact deliver_sim hfr hks
  | let_ rhs body =>
    have hc : CodeAt code pc (Instr.op rhs :: compileTm body) := hcode
    have hi := hc.head
    cases hr : rhs.eval ρ with
    | none =>
      have h1 : Core.step p ⟨.let_ rhs body, ρ, stack, ⟨conts, labels, cells⟩⟩ = .stuck := by
        simp [Core.step, hr]
      rw [h1]
      exact .stuck
    | some v =>
      have h1 : Core.step p ⟨.let_ rhs body, ρ, stack, ⟨conts, labels, cells⟩⟩
          = .next ⟨body, ρ ++ [v], stack, ⟨conts, labels, cells⟩⟩ := by
        simp [Core.step, hr]
      have h2 : Bytecode.step (compile p) ⟨code, pc, ρ, frames, ⟨conts', labels, cells⟩⟩
          = .next ⟨code, pc + 1, ρ ++ [v], frames, ⟨conts', labels, cells⟩⟩ := by
        simp [Bytecode.step, hi, hr]
      rw [h1, h2]
      exact .next (RunsThrough.refl rfl) (.mk hc.tail hfr hks)
  | call f args body =>
    have hc : CodeAt code pc (Instr.call f args :: compileTm body) := hcode
    have hi := hc.head
    cases he : evalCall ρ f args with
    | none =>
      have h1 : Core.step p ⟨.call f args body, ρ, stack, ⟨conts, labels, cells⟩⟩ = .stuck := by
        simp [Core.step, he]
      rw [h1]
      exact .stuck
    | some c =>
      have h1 : Core.step p ⟨.call f args body, ρ, stack, ⟨conts, labels, cells⟩⟩
          = Core.apply p c (.call ρ body :: stack) ⟨conts, labels, cells⟩ := by
        simp [Core.step, he]
      have h2 : Bytecode.step (compile p) ⟨code, pc, ρ, frames, ⟨conts', labels, cells⟩⟩
          = Bytecode.apply (compile p) c (.ret code (pc + 1) ρ :: frames) ⟨conts', labels, cells⟩ := by
        simp [Bytecode.step, hi, he]
      rw [h1, h2]
      exact apply_sim (.cons (.call hc.tail) hfr) hks
  | tail f args =>
    have hc : CodeAt code pc [Instr.tail f args] := hcode
    have hi := hc.head
    cases he : evalCall ρ f args with
    | none =>
      have h1 : Core.step p ⟨.tail f args, ρ, stack, ⟨conts, labels, cells⟩⟩ = .stuck := by simp [Core.step, he]
      rw [h1]
      exact .stuck
    | some c =>
      have h1 : Core.step p ⟨.tail f args, ρ, stack, ⟨conts, labels, cells⟩⟩ = Core.apply p c stack ⟨conts, labels, cells⟩ := by
        simp [Core.step, he]
      have h2 : Bytecode.step (compile p) ⟨code, pc, ρ, frames, ⟨conts', labels, cells⟩⟩
          = Bytecode.apply (compile p) c frames ⟨conts', labels, cells⟩ := by
        simp [Bytecode.step, hi, he]
      rw [h1, h2]
      exact apply_sim hfr hks
  | handle ret ops captures thunk body =>
    have hc : CodeAt code pc (Instr.handle ret ops captures thunk :: compileTm body) := hcode
    have hi := hc.head
    cases hcap : evalAtoms ρ captures with
    | none =>
      have h1 : Core.step p ⟨.handle ret ops captures thunk body, ρ, stack, ⟨conts, labels, cells⟩⟩ = .stuck := by
        simp [Core.step, hcap]
      rw [h1]
      exact .stuck
    | some caps =>
      cases he : evalCall ρ thunk [] with
      | none =>
        have h1 : Core.step p ⟨.handle ret ops captures thunk body, ρ, stack, ⟨conts, labels, cells⟩⟩
            = .stuck := by
          simp [Core.step, hcap, he]
        rw [h1]
        exact .stuck
      | some c =>
        have h1 : Core.step p ⟨.handle ret ops captures thunk body, ρ, stack, ⟨conts, labels, cells⟩⟩
            = Core.apply p c (.handler labels ⟨ret, ops, caps⟩ :: .call ρ body :: stack)
                ⟨conts, labels + 1, cells⟩ := by
          simp [Core.step, hcap, he]
        have h2 : Bytecode.step (compile p) ⟨code, pc, ρ, frames, ⟨conts', labels, cells⟩⟩
            = Bytecode.apply (compile p) c
                (.handler labels ⟨ret, ops, caps⟩ :: .ret code (pc + 1) ρ :: frames)
                ⟨conts', labels + 1, cells⟩ := by
          simp [Bytecode.step, hi, hcap, he]
        rw [h1, h2]
        exact apply_sim (.cons .handler (.cons (.call hc.tail) hfr)) (.mk hcs)
  | raise op args =>
    have hc : CodeAt code pc [Instr.raise op args] := hcode
    have hi := hc.head
    cases hv : evalAtoms ρ args with
    | none =>
      have h1 : Core.step p ⟨.raise op args, ρ, stack, ⟨conts, labels, cells⟩⟩ = .stuck := by simp [Core.step, hv]
      rw [h1]
      exact .stuck
    | some vs =>
      cases hf : findHandler Core.Frame.asHandler op stack with
      | none =>
        have h1 : Core.step p ⟨.raise op args, ρ, stack, ⟨conts, labels, cells⟩⟩ = .stuck := by
          simp [Core.step, hv, hf]
        rw [h1]
        exact .stuck
      | some d =>
        obtain ⟨above', below', hf', habove, hbelow⟩ := find_sim hfr hf
        have h1 : Core.step p ⟨.raise op args, ρ, stack, ⟨conts, labels, cells⟩⟩
            = Core.leave p (.handler d.id) (.invoke d.arm d.handler.caps vs) stack
                ⟨conts, labels, cells⟩ := by
          simp [Core.step, hv, hf]
        have h2 : Bytecode.step (compile p) ⟨code, pc, ρ, frames, ⟨conts', labels, cells⟩⟩
            = Bytecode.leave (compile p) (.handler d.id) (.invoke d.arm d.handler.caps vs) frames
                ⟨conts', labels, cells⟩ := by
          simp [Bytecode.step, hi, hv, hf']
        rw [h1, h2]
        exact leave_sim hfr hks
  | perform op args body =>
    have hc : CodeAt code pc (Instr.perform op args :: compileTm body) := hcode
    have hi := hc.head
    cases hv : evalAtoms ρ args with
    | none =>
      have h1 : Core.step p ⟨.perform op args body, ρ, stack, ⟨conts, labels, cells⟩⟩ = .stuck := by
        simp [Core.step, hv]
      rw [h1]
      exact .stuck
    | some vs =>
      cases hf : findHandler Core.Frame.asHandler op stack with
      | none =>
        have h1 : Core.step p ⟨.perform op args body, ρ, stack, ⟨conts, labels, cells⟩⟩ = .stuck := by
          simp [Core.step, hv, hf]
        rw [h1]
        exact .stuck
      | some d =>
        obtain ⟨above', below', hf', habove, hbelow⟩ := find_sim hfr hf
        have h1 : Core.step p ⟨.perform op args body, ρ, stack, ⟨conts, labels, cells⟩⟩
            = Core.callFn p d.arm d.handler.caps (vs ++ [.cont conts.length]) d.below
                ⟨conts ++ [some (.call ρ body :: d.above ++ [.handler d.id d.handler])],
                  labels, cells⟩ := by
          simp [Core.step, hv, hf]
        have h2 : Bytecode.step (compile p) ⟨code, pc, ρ, frames, ⟨conts', labels, cells⟩⟩
            = Bytecode.callFn (compile p) d.arm d.handler.caps (vs ++ [.cont conts.length]) below'
                ⟨conts' ++ [some (.ret code (pc + 1) ρ :: above' ++ [.handler d.id d.handler])],
                  labels, cells⟩ := by
          simp [Bytecode.step, hi, hv, hf', hcs.length_eq]
        rw [h1, h2]
        exact callFn_sim hbelow
          (.mk (hcs.snoc (.full (.cons (.call hc.tail) (habove.append (.cons .handler .nil))))))
  | label thunk body =>
    have hc : CodeAt code pc (Instr.label thunk :: compileTm body) := hcode
    have hi := hc.head
    cases he : evalScope ρ thunk (.label labels) with
    | none =>
      have h1 : Core.step p ⟨.label thunk body, ρ, stack, ⟨conts, labels, cells⟩⟩ = .stuck := by
        simp [Core.step, he]
      rw [h1]
      exact .stuck
    | some c =>
      have h1 : Core.step p ⟨.label thunk body, ρ, stack, ⟨conts, labels, cells⟩⟩
          = Core.apply p c (.label labels :: .call ρ body :: stack)
              ⟨conts, labels + 1, cells⟩ := by
        simp [Core.step, he]
      have h2 : Bytecode.step (compile p) ⟨code, pc, ρ, frames, ⟨conts', labels, cells⟩⟩
          = Bytecode.apply (compile p) c
              (.label labels :: .ret code (pc + 1) ρ :: frames) ⟨conts', labels + 1, cells⟩ := by
        simp [Bytecode.step, hi, he]
      rw [h1, h2]
      exact apply_sim (.cons .label (.cons (.call hc.tail) hfr)) (.mk hcs)
  | lend uniq r thunk pre post body =>
    have hc : CodeAt code pc (Instr.lend uniq r thunk pre post :: compileTm body) := hcode
    have hi := hc.head
    cases he : evalLend ρ r thunk pre post (labels + 1) with
    | none =>
      have h1 : Core.step p ⟨.lend uniq r thunk pre post body, ρ, stack, ⟨conts, labels, cells⟩⟩
          = .stuck := by
        simp [Core.step, he]
      rw [h1]
      exact .stuck
    | some x =>
      obtain ⟨a, c⟩ := x
      have h1 : Core.step p ⟨.lend uniq r thunk pre post body, ρ, stack, ⟨conts, labels, cells⟩⟩
          = Core.apply p c (.lend uniq a (labels + 1) :: .call ρ body :: stack)
              ⟨conts, labels + 1, cells⟩ := by
        simp [Core.step, he]
      have h2 : Bytecode.step (compile p) ⟨code, pc, ρ, frames, ⟨conts', labels, cells⟩⟩
          = Bytecode.apply (compile p) c
              (.ret code (pc + 1) ρ :: frames) ⟨conts', labels + 1, cells⟩ := by
        simp [Bytecode.step, hi, he]
      rw [h1, h2]
      exact apply_sim (.lend (.cons (.call hc.tail) hfr)) (.mk hcs)
  | handleTail ret ops captures thunk =>
    have hc : CodeAt code pc [Instr.handleTail ret ops captures thunk] := hcode
    have hi := hc.head
    cases hcap : evalAtoms ρ captures with
    | none =>
      have h1 : Core.step p ⟨.handleTail ret ops captures thunk, ρ, stack, ⟨conts, labels, cells⟩⟩
          = .stuck := by
        simp [Core.step, hcap]
      rw [h1]
      exact .stuck
    | some caps =>
      cases he : evalCall ρ thunk [] with
      | none =>
        have h1 : Core.step p ⟨.handleTail ret ops captures thunk, ρ, stack, ⟨conts, labels, cells⟩⟩
            = .stuck := by
          simp [Core.step, hcap, he]
        rw [h1]
        exact .stuck
      | some c =>
        have h1 : Core.step p ⟨.handleTail ret ops captures thunk, ρ, stack, ⟨conts, labels, cells⟩⟩
            = Core.apply p c (.handler labels ⟨ret, ops, caps⟩ :: stack)
                ⟨conts, labels + 1, cells⟩ := by
          simp [Core.step, hcap, he]
        have h2 : Bytecode.step (compile p) ⟨code, pc, ρ, frames, ⟨conts', labels, cells⟩⟩
            = Bytecode.apply (compile p) c (.handler labels ⟨ret, ops, caps⟩ :: frames)
                ⟨conts', labels + 1, cells⟩ := by
          simp [Bytecode.step, hi, hcap, he]
        rw [h1, h2]
        exact apply_sim (.cons .handler hfr) (.mk hcs)
  | labelTail thunk =>
    have hc : CodeAt code pc [Instr.labelTail thunk] := hcode
    have hi := hc.head
    cases he : evalScope ρ thunk (.label labels) with
    | none =>
      have h1 : Core.step p ⟨.labelTail thunk, ρ, stack, ⟨conts, labels, cells⟩⟩ = .stuck := by
        simp [Core.step, he]
      rw [h1]
      exact .stuck
    | some c =>
      have h1 : Core.step p ⟨.labelTail thunk, ρ, stack, ⟨conts, labels, cells⟩⟩
          = Core.apply p c (.label labels :: stack) ⟨conts, labels + 1, cells⟩ := by
        simp [Core.step, he]
      have h2 : Bytecode.step (compile p) ⟨code, pc, ρ, frames, ⟨conts', labels, cells⟩⟩
          = Bytecode.apply (compile p) c (.label labels :: frames)
              ⟨conts', labels + 1, cells⟩ := by
        simp [Bytecode.step, hi, he]
      rw [h1, h2]
      exact apply_sim (.cons .label hfr) (.mk hcs)
  | cell init thunk body =>
    have hc : CodeAt code pc (Instr.cell init thunk :: compileTm body) := hcode
    have hi := hc.head
    cases hv : init.eval ρ with
    | none =>
      have h1 : Core.step p ⟨.cell init thunk body, ρ, stack, ⟨conts, labels, cells⟩⟩ = .stuck := by
        simp [Core.step, hv]
      rw [h1]
      exact .stuck
    | some v =>
      cases he : evalScope ρ thunk (.ref cells.length 0) with
      | none =>
        have h1 : Core.step p ⟨.cell init thunk body, ρ, stack, ⟨conts, labels, cells⟩⟩
            = .stuck := by
          simp [Core.step, hv, he]
        rw [h1]
        exact .stuck
      | some c =>
        have h1 : Core.step p ⟨.cell init thunk body, ρ, stack, ⟨conts, labels, cells⟩⟩
            = Core.apply p c (.cell cells.length :: .call ρ body :: stack)
                (Store.alloc ⟨conts, labels, cells⟩ v) := by
          simp [Core.step, hv, he]
        have h2 : Bytecode.step (compile p) ⟨code, pc, ρ, frames, ⟨conts', labels, cells⟩⟩
            = Bytecode.apply (compile p) c
                (.cell cells.length :: .ret code (pc + 1) ρ :: frames)
                (Store.alloc ⟨conts', labels, cells⟩ v) := by
          simp [Bytecode.step, hi, hv, he]
        rw [h1, h2]
        exact apply_sim (.cons .cell (.cons (.call hc.tail) hfr)) (hks.alloc v)
  | cellTail init thunk =>
    have hc : CodeAt code pc [Instr.cellTail init thunk] := hcode
    have hi := hc.head
    cases hv : init.eval ρ with
    | none =>
      have h1 : Core.step p ⟨.cellTail init thunk, ρ, stack, ⟨conts, labels, cells⟩⟩ = .stuck := by
        simp [Core.step, hv]
      rw [h1]
      exact .stuck
    | some v =>
      cases he : evalScope ρ thunk (.ref cells.length 0) with
      | none =>
        have h1 : Core.step p ⟨.cellTail init thunk, ρ, stack, ⟨conts, labels, cells⟩⟩
            = .stuck := by
          simp [Core.step, hv, he]
        rw [h1]
        exact .stuck
      | some c =>
        have h1 : Core.step p ⟨.cellTail init thunk, ρ, stack, ⟨conts, labels, cells⟩⟩
            = Core.apply p c (.cell cells.length :: stack)
                (Store.alloc ⟨conts, labels, cells⟩ v) := by
          simp [Core.step, hv, he]
        have h2 : Bytecode.step (compile p) ⟨code, pc, ρ, frames, ⟨conts', labels, cells⟩⟩
            = Bytecode.apply (compile p) c (.cell cells.length :: frames)
                (Store.alloc ⟨conts', labels, cells⟩ v) := by
          simp [Bytecode.step, hi, hv, he]
        rw [h1, h2]
        exact apply_sim (.cons .cell hfr) (hks.alloc v)
  | guard cleanup thunk body =>
    have hc : CodeAt code pc (Instr.guard cleanup thunk :: compileTm body) := hcode
    have hi := hc.head
    cases hcl : evalClosure ρ cleanup with
    | none =>
      have h1 : Core.step p ⟨.guard cleanup thunk body, ρ, stack, ⟨conts, labels, cells⟩⟩ = .stuck := by
        simp [Core.step, hcl]
      rw [h1]
      exact .stuck
    | some r =>
      obtain ⟨fn, captures⟩ := r
      cases he : evalCall ρ thunk [] with
      | none =>
        have h1 : Core.step p ⟨.guard cleanup thunk body, ρ, stack, ⟨conts, labels, cells⟩⟩
            = .stuck := by
          simp [Core.step, hcl, he]
        rw [h1]
        exact .stuck
      | some c =>
        have h1 : Core.step p ⟨.guard cleanup thunk body, ρ, stack, ⟨conts, labels, cells⟩⟩
            = Core.apply p c (.guard fn captures :: .call ρ body :: stack) ⟨conts, labels, cells⟩ := by
          simp [Core.step, hcl, he]
        have h2 : Bytecode.step (compile p) ⟨code, pc, ρ, frames, ⟨conts', labels, cells⟩⟩
            = Bytecode.apply (compile p) c
                (.guard fn captures :: .ret code (pc + 1) ρ :: frames) ⟨conts', labels, cells⟩ := by
          simp [Bytecode.step, hi, hcl, he]
        rw [h1, h2]
        exact apply_sim (.cons .guard (.cons (.call hc.tail) hfr)) hks
  | guardTail cleanup thunk =>
    have hc : CodeAt code pc [Instr.guardTail cleanup thunk] := hcode
    have hi := hc.head
    cases hcl : evalClosure ρ cleanup with
    | none =>
      have h1 : Core.step p ⟨.guardTail cleanup thunk, ρ, stack, ⟨conts, labels, cells⟩⟩ = .stuck := by
        simp [Core.step, hcl]
      rw [h1]
      exact .stuck
    | some r =>
      obtain ⟨fn, captures⟩ := r
      cases he : evalCall ρ thunk [] with
      | none =>
        have h1 : Core.step p ⟨.guardTail cleanup thunk, ρ, stack, ⟨conts, labels, cells⟩⟩
            = .stuck := by
          simp [Core.step, hcl, he]
        rw [h1]
        exact .stuck
      | some c =>
        have h1 : Core.step p ⟨.guardTail cleanup thunk, ρ, stack, ⟨conts, labels, cells⟩⟩
            = Core.apply p c (.guard fn captures :: stack) ⟨conts, labels, cells⟩ := by
          simp [Core.step, hcl, he]
        have h2 : Bytecode.step (compile p) ⟨code, pc, ρ, frames, ⟨conts', labels, cells⟩⟩
            = Bytecode.apply (compile p) c (.guard fn captures :: frames) ⟨conts', labels, cells⟩ := by
          simp [Bytecode.step, hi, hcl, he]
        rw [h1, h2]
        exact apply_sim (.cons .guard hfr) hks
  | cancel k body =>
    have hc : CodeAt code pc (Instr.cancel k :: compileTm body) := hcode
    have hi := hc.head
    cases hk : evalCont ρ k with
    | none =>
      have h1 : Core.step p ⟨.cancel k body, ρ, stack, ⟨conts, labels, cells⟩⟩ = .stuck := by
        simp [Core.step, hk]
      rw [h1]
      exact .stuck
    | some o =>
      cases o with
      | none =>
        have h1 : Core.step p ⟨.cancel k body, ρ, stack, ⟨conts, labels, cells⟩⟩
            = .next ⟨body, ρ ++ [Value.unit], stack, ⟨conts, labels, cells⟩⟩ := by
          simp [Core.step, hk]
        have h2 : Bytecode.step (compile p) ⟨code, pc, ρ, frames, ⟨conts', labels, cells⟩⟩
            = .next ⟨code, pc + 1, ρ ++ [Value.unit], frames, ⟨conts', labels, cells⟩⟩ := by
          simp [Bytecode.step, hi, hk]
        rw [h1, h2]
        exact .next (RunsThrough.refl rfl) (.mk hc.tail hfr (.mk hcs))
      | some id =>
        cases ht : takeCont conts id with
        | none =>
          have h1 : Core.step p ⟨.cancel k body, ρ, stack, ⟨conts, labels, cells⟩⟩ = .stuck := by
            simp [Core.step, hk, ht]
          rw [h1]
          exact .stuck
        | some r =>
          obtain ⟨seg, conts₁⟩ := r
          obtain ⟨seg', conts₁', ht', hseg, hcs₁⟩ := hcs.take ht
          have h1 : Core.step p ⟨.cancel k body, ρ, stack, ⟨conts, labels, cells⟩⟩
              = Core.leave p (.label labels) (.yield Value.unit)
                  (seg ++ .yield Value.unit :: .label labels :: .call ρ body :: stack)
                  ⟨conts₁, labels + 1, cells⟩ := by
            simp [Core.step, hk, ht]
          have h2 : Bytecode.step (compile p) ⟨code, pc, ρ, frames, ⟨conts', labels, cells⟩⟩
              = Bytecode.leave (compile p) (.label labels) (.yield Value.unit)
                  (seg' ++ .yield Value.unit :: .label labels :: .ret code (pc + 1) ρ :: frames)
                  ⟨conts₁', labels + 1, cells⟩ := by
            simp [Bytecode.step, hi, hk, ht']
          rw [h1, h2]
          exact leave_sim
            (hseg.append (.cons .yield (.cons .label (.cons (.call hc.tail) hfr)))) (.mk hcs₁)
  | mem op args body =>
    have hc : CodeAt code pc (Instr.mem op args :: compileTm body) := hcode
    have hi := hc.head
    cases hv : evalAtoms ρ args with
    | none =>
      have h1 : Core.step p ⟨.mem op args body, ρ, stack, ⟨conts, labels, cells⟩⟩ = .stuck := by
        simp [Core.step, hv]
      rw [h1]
      exact .stuck
    | some vs =>
      cases hm : op.eval cells vs with
      | none =>
        have h1 : Core.step p ⟨.mem op args body, ρ, stack, ⟨conts, labels, cells⟩⟩
            = .stuck := by
          simp [Core.step, hv, hm]
        rw [h1]
        exact .stuck
      | some r =>
        obtain ⟨res, cells'⟩ := r
        have h1 : Core.step p ⟨.mem op args body, ρ, stack, ⟨conts, labels, cells⟩⟩
            = .next ⟨body, ρ ++ [res], stack, ⟨conts, labels, cells'⟩⟩ := by
          simp [Core.step, hv, hm]
        have h2 : Bytecode.step (compile p) ⟨code, pc, ρ, frames, ⟨conts', labels, cells⟩⟩
            = .next ⟨code, pc + 1, ρ ++ [res], frames, ⟨conts', labels, cells'⟩⟩ := by
          simp [Bytecode.step, hi, hv, hm]
        rw [h1, h2]
        exact .next (RunsThrough.refl rfl) (.mk hc.tail hfr (.mk hcs))
  | host id args body =>
    -- Host operations are not steps of the machine state alone.
    have h1 : Core.step p ⟨.host id args body, ρ, stack, ⟨conts, labels, cells⟩⟩ = .stuck := rfl
    rw [h1]
    exact .stuck

/-! ## Programs in their world -/

/-- Configurations match when their machine states match in the same world. -/
inductive MatchIO : Core.Config → Bytecode.Config → Prop where
  | mk {s : Core.State} {t : Bytecode.State} {w : World} : Match s t → MatchIO ⟨s, w⟩ ⟨t, w⟩

theorem matchIO_init (p : Core.Program) (input : List Int) :
    MatchIO (Core.initIO p input) (Bytecode.initIO (compile p) input) :=
  .mk (match_init p)

theorem MatchIO.output_eq {c : Core.Config} {d : Bytecode.Config} (h : MatchIO c d) :
    c.world.output = d.world.output := by
  cases h
  rfl

section World

variable {P : Bytecode.Program}

/-- A bytecode step in a world is either a step of the machine state alone, or
a host instruction. -/
theorem stepIO_eq_lift_or_host (t : Bytecode.State) (w : World) :
    Bytecode.stepIO P ⟨t, w⟩ = Bytecode.lift w (Bytecode.step P t)
      ∨ ∃ id args, t.code[t.pc]? = some (Instr.host id args) := by
  cases hi : t.code[t.pc]? with
  | none =>
    left
    simp [Bytecode.stepIO, hi]
  | some i =>
    cases i with
    | host id args => exact Or.inr ⟨id, args, rfl⟩
    | _ =>
      left
      simp [Bytecode.stepIO, hi]

theorem stepIO_of_step_next {t t' : Bytecode.State} (w : World)
    (h : Bytecode.step P t = .next t') : Bytecode.stepIO P ⟨t, w⟩ = .next ⟨t', w⟩ := by
  rcases stepIO_eq_lift_or_host (P := P) t w with he | ⟨id, args, hi⟩
  · rw [he, h]
    rfl
  · simp [Bytecode.step, hi] at h

theorem stepIO_of_step_halt {t : Bytecode.State} {v : Value} (w : World)
    (h : Bytecode.step P t = .halt v) : Bytecode.stepIO P ⟨t, w⟩ = .halt ⟨v, w⟩ := by
  rcases stepIO_eq_lift_or_host (P := P) t w with he | ⟨id, args, hi⟩
  · rw [he, h]
    rfl
  · simp [Bytecode.step, hi] at h

/-- A run of the machine state alone is the same run in any world. -/
theorem run_lift (w : World) : ∀ (k : Nat) {t t' : Bytecode.State},
    run (Bytecode.step P) k t = .next t' →
    run (Bytecode.stepIO P) k ⟨t, w⟩ = .next ⟨t', w⟩ := by
  intro k
  induction k with
  | zero =>
    intro t t' h
    rw [run_zero] at h
    cases h
    rfl
  | succ k ih =>
    intro t t' h
    rw [run_succ] at h
    cases hs : Bytecode.step P t with
    | next t₁ =>
      rw [hs, Step.bind_next] at h
      rw [run_succ, stepIO_of_step_next w hs, Step.bind_next]
      exact ih h
    | halt v => rw [hs] at h; simp at h
    | stuck => rw [hs] at h; simp at h

/-- A run of the machine state alone is the same run in any world, with the
same property of every state along the way. -/
theorem runsThrough_lift (w : World) {I : Bytecode.State → Prop} {k : Nat}
    {t t' : Bytecode.State} (h : RunsThrough (Bytecode.step P) I k t t') :
    RunsThrough (Bytecode.stepIO P) (fun d => I d.state) k ⟨t, w⟩ ⟨t', w⟩ :=
  ⟨run_lift w k h.1, fun j hj => by
    obtain ⟨tj, htj, hI⟩ := h.2 j hj
    exact ⟨⟨tj, w⟩, run_lift w j htj, hI⟩⟩

theorem lift_next_world {w : World} {r : Step Bytecode.State Value} {d : Bytecode.Config}
    (h : Bytecode.lift w r = .next d) : d.world = w := by
  cases r with
  | next s =>
    simp [Bytecode.lift] at h
    subst h
    rfl
  | halt v => simp [Bytecode.lift] at h
  | stuck => simp [Bytecode.lift] at h

theorem lift_halt_world {w : World} {r : Step Bytecode.State Value} {res : Result}
    (h : Bytecode.lift w r = .halt res) : res.world = w := by
  cases r with
  | next s => simp [Bytecode.lift] at h
  | halt v =>
    simp [Bytecode.lift] at h
    subst h
    rfl
  | stuck => simp [Bytecode.lift] at h

/-- A bytecode step never retracts output. -/
theorem stepIO_output_next {d d' : Bytecode.Config} (h : Bytecode.stepIO P d = .next d') :
    d.world.output <+: d'.world.output := by
  obtain ⟨t, w⟩ := d
  rcases stepIO_eq_lift_or_host (P := P) t w with he | ⟨id, args, hi⟩
  · rw [he] at h
    rw [lift_next_world h]
    exact List.prefix_refl _
  · simp only [Bytecode.stepIO, hi] at h
    cases hv : evalAtoms t.locals args with
    | none => simp [hv] at h
    | some vs =>
      cases hh : Host.call w id vs with
      | none => simp [hv, hh] at h
      | some r =>
        obtain ⟨res, w'⟩ := r
        simp [hv, hh] at h
        subst h
        exact Host.call_output hh

theorem stepIO_output_halt {d : Bytecode.Config} {res : Result}
    (h : Bytecode.stepIO P d = .halt res) : d.world.output <+: res.world.output := by
  obtain ⟨t, w⟩ := d
  rcases stepIO_eq_lift_or_host (P := P) t w with he | ⟨id, args, hi⟩
  · rw [he] at h
    rw [lift_halt_world h]
    exact List.prefix_refl _
  · simp only [Bytecode.stepIO, hi] at h
    cases hv : evalAtoms t.locals args with
    | none => simp [hv] at h
    | some vs =>
      cases hh : Host.call w id vs with
      | none => simp [hv, hh] at h
      | some r => simp [hv, hh] at h

end World

/-- `SimOutcome` for programs in their world. -/
inductive SimOutcomeIO (p : Core.Program) :
    Step Core.Config Result → Step Bytecode.Config Result → Prop where
  | next {c' : Core.Config} {d₀ d' : Bytecode.Config} {k : Nat} :
      RunsThrough (Bytecode.stepIO (compile p)) (fun d => d.state.frames = d'.state.frames)
        k d₀ d' →
      MatchIO c' d' → SimOutcomeIO p (.next c') (.next d₀)
  | halt {r : Result} : SimOutcomeIO p (.halt r) (.halt r)
  | stuck {r : Step Bytecode.Config Result} : SimOutcomeIO p .stuck r

/-- A simulated step of the machine state is a simulated step in any world. -/
theorem lift_sim {p : Core.Program} {s : Core.State} {t : Bytecode.State} (w : World)
    (h : SimOutcome p (Core.step p s) (Bytecode.step (compile p) t)) :
    SimOutcomeIO p (Core.lift w (Core.step p s)) (Bytecode.stepIO (compile p) ⟨t, w⟩) := by
  generalize Core.step p s = r at h
  generalize ht : Bytecode.step (compile p) t = r' at h
  cases h with
  | @next s' t₀ t' k hk hm =>
    rw [stepIO_of_step_next w ht]
    exact .next (runsThrough_lift w hk) (.mk hm)
  | halt =>
    rw [stepIO_of_step_halt w ht]
    exact .halt
  | stuck => exact .stuck

theorem stepIO_sim (p : Core.Program) {c : Core.Config} {d : Bytecode.Config}
    (hm : MatchIO c d) : SimOutcomeIO p (Core.stepIO p c) (Bytecode.stepIO (compile p) d) := by
  obtain @⟨s, t, w, hst⟩ := hm
  obtain @⟨tm, ρ, stack, store, code, pc, frames, store', hcode, hfr, hstore⟩ := hst
  cases tm with
  | host id args body =>
    have hc : CodeAt code pc (Instr.host id args :: compileTm body) := hcode
    have hi := hc.head
    cases hv : evalAtoms ρ args with
    | none =>
      have h1 : Core.stepIO p ⟨⟨.host id args body, ρ, stack, store⟩, w⟩ = .stuck := by
        simp [Core.stepIO, hv]
      rw [h1]
      exact .stuck
    | some vs =>
      cases hh : Host.call w id vs with
      | none =>
        have h1 : Core.stepIO p ⟨⟨.host id args body, ρ, stack, store⟩, w⟩ = .stuck := by
          simp [Core.stepIO, hv, hh]
        rw [h1]
        exact .stuck
      | some r =>
        obtain ⟨res, w'⟩ := r
        have h1 : Core.stepIO p ⟨⟨.host id args body, ρ, stack, store⟩, w⟩
            = .next ⟨⟨body, ρ ++ [res], stack, store⟩, w'⟩ := by
          simp [Core.stepIO, hv, hh]
        have h2 : Bytecode.stepIO (compile p) ⟨⟨code, pc, ρ, frames, store'⟩, w⟩
            = .next ⟨⟨code, pc + 1, ρ ++ [res], frames, store'⟩, w'⟩ := by
          simp [Bytecode.stepIO, hi, hv, hh]
        rw [h1, h2]
        exact .next (RunsThrough.refl rfl) (.mk (.mk hc.tail hfr hstore))
  | _ => exact lift_sim w (step_sim p (.mk hcode hfr hstore))

/-- `MatchIO` is a forward simulation from Core to bytecode. -/
theorem forwardSim (p : Core.Program) :
    ForwardSim (Core.stepIO p) (Bytecode.stepIO (compile p)) MatchIO where
  next := by
    intro c d c' hm hs
    have h := stepIO_sim p hm
    rw [hs] at h
    generalize hstep : Bytecode.stepIO (compile p) d = r at h
    cases h with
    | @next _ d₀ d' k hk hm' =>
      exact ⟨k, d', by rw [run_succ, hstep, Step.bind_next]; exact hk.1, hm'⟩
  halt := by
    intro c d r hm hs
    have h := stepIO_sim p hm
    rw [hs] at h
    generalize hstep : Bytecode.stepIO (compile p) d = r' at h
    cases h with
    | halt => exact ⟨0, run_one_halt hstep⟩

/-- The same simulation, also accounting for the bytecode's intermediate
states: whatever state it is in, its stack is no deeper than the stack of the
Core state it is at or on its way to. -/
theorem forwardSimThrough (p : Core.Program) :
    ForwardSimThrough (Core.stepIO p) (Bytecode.stepIO (compile p)) MatchIO
      (fun c d => d.state.frames.length ≤ c.state.stack.length) where
  rel := by
    intro c d hm
    obtain @⟨s, t, w, hst⟩ := hm
    obtain ⟨_, hfr, _⟩ := hst
    exact hfr.length_le
  next := by
    intro c d c' hm hs
    have h := stepIO_sim p hm
    rw [hs] at h
    generalize hstep : Bytecode.stepIO (compile p) d = r at h
    cases h with
    | @next _ d₀ d' k hk hm' =>
      have hlen : d'.state.frames.length ≤ c'.state.stack.length := by
        obtain @⟨s, t, w, hst⟩ := hm'
        obtain ⟨_, hfr, _⟩ := hst
        exact hfr.length_le
      exact ⟨k, d₀, d', rfl, hk.imp (fun x hx => by rw [hx]; exact hlen), hm'⟩
  halt := by
    intro c d r hm hs
    have h := stepIO_sim p hm
    rw [hs] at h
    generalize hstep : Bytecode.stepIO (compile p) d = r' at h
    cases h with
    | halt => rfl

/-! ## Behaviour preservation -/

variable {p : Core.Program} {input : List Int}

/-- If the Core program halts with a result, so does its bytecode. -/
theorem compile_halts {r : Result} :
    Core.Halts p input r → Bytecode.Halts (compile p) input r :=
  (forwardSim p).halts (matchIO_init p input)

/-- If the Core program runs forever, so does its bytecode. -/
theorem compile_diverges : Core.Diverges p input → Bytecode.Diverges (compile p) input :=
  (forwardSim p).diverges (matchIO_init p input)

/-- A result computed by the bytecode is a result of the Core program, unless
the Core program goes wrong. -/
theorem compile_halts_reflect {r : Result} :
    Bytecode.Halts (compile p) input r → Core.Halts p input r ∨ Core.GoesWrong p input :=
  (forwardSim p).halts_reflect (matchIO_init p input)

/--
**Compiler correctness.** For a Core program that does not go wrong on a given
input, the compiled bytecode has exactly the same behaviour: it halts with the
same value and the same world (the same output written and input left), it
diverges exactly when the Core program does, and it never goes wrong.
-/
theorem compile_correct (p : Core.Program) (input : List Int) (safe : ¬ Core.GoesWrong p input) :
    (∀ r, Bytecode.Halts (compile p) input r ↔ Core.Halts p input r)
    ∧ (Bytecode.Diverges (compile p) input ↔ Core.Diverges p input)
    ∧ ¬ Bytecode.GoesWrong (compile p) input := by
  refine ⟨fun r => ⟨fun h => ?_, compile_halts⟩, ⟨?_, compile_diverges⟩, ?_⟩
  · exact (compile_halts_reflect h).resolve_right safe
  · exact (forwardSim p).diverges_reflect (matchIO_init p input) safe
  · exact (forwardSim p).not_goesWrong (matchIO_init p input) safe

/-! ## Output while running

`compile_correct` settles the output of programs that halt. These two theorems
cover output at every moment, so they also speak for programs that never halt.
-/

/-- Whatever the Core program has written at some point, the bytecode has
written at some point. -/
theorem compile_emits {out : List Value} :
    Core.Emits p input out → Bytecode.Emits (compile p) input out := by
  intro ⟨c, hreach, hout⟩
  obtain ⟨d, hd, hm⟩ := (forwardSim p).reaches (matchIO_init p input) hreach
  exact ⟨d, hd, by rw [← hm.output_eq]; exact hout⟩

/-- Whatever the bytecode has written at some point is the beginning of what
the Core program writes: either by some point while running, or by the time it
halts. The bytecode never writes anything the Core program does not. -/
theorem compile_emits_reflect {out : List Value} (safe : ¬ Core.GoesWrong p input) :
    Bytecode.Emits (compile p) input out →
    (∃ out', Core.Emits p input out' ∧ out <+: out')
      ∨ (∃ r, Core.Halts p input r ∧ out <+: r.world.output) := by
  intro ⟨d, hreach, hout⟩
  have h := (forwardSim p).obs_reflect (fun c => c.world.output) (fun d => d.world.output)
    (fun r => r.world.output) (fun hm => hm.output_eq) (fun hs => stepIO_output_next hs)
    (fun hs => stepIO_output_halt hs) (matchIO_init p input) safe hreach
  rcases h with ⟨c, hc, hpre⟩ | ⟨r, hr, hpre⟩
  · exact Or.inl ⟨c.world.output, ⟨c, hc, rfl⟩, by rw [← hout]; exact hpre⟩
  · exact Or.inr ⟨r, hr, by rw [← hout]; exact hpre⟩

/-! ## Stack depth

Core's stack discipline is what makes a tail call, a tail handler or a tail
label scope keep no frame. This theorem carries that discipline to the bytecode.
-/

/-- Every stack the bytecode reaches is no deeper than one the Core program
reaches: shallower only by the scopes of borrows, which the bytecode does not
keep. The bytecode therefore never uses a deeper stack than the Core semantics
does. -/
theorem compile_stack_depth (safe : ¬ Core.GoesWrong p input) {d : Bytecode.Config}
    (h : Reaches (Bytecode.stepIO (compile p)) (Bytecode.initIO (compile p) input) d) :
    ∃ c, Reaches (Core.stepIO p) (Core.initIO p input) c
      ∧ d.state.frames.length ≤ c.state.stack.length := by
  obtain ⟨m, hm⟩ := h
  exact (forwardSimThrough p).reflect m (matchIO_init p input) safe hm

end Glorious
