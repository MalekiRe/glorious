import Glorious.Proof.Simulation
import Glorious.Proof.Patterns

/-!
# Compiler correctness

The bytecode produced by `compile` has exactly the behaviour of the Core program
it was compiled from. The final statement is `compile_correct`.
-/

namespace Glorious

open Machine
open Bytecode (Instr Code)

/-! ## The simulation relation -/

/-- Stacks correspond frame by frame: a suspended Core caller is a return frame
that resumes its compiled code with the same locals; handler delimiters and
label scopes are identical. -/
inductive MatchFrames : List Core.Frame → List Bytecode.Frame → Prop where
  | nil : MatchFrames [] []
  | call {body : Core.Tm} {ρ : Env} {stack : List Core.Frame}
      {code : Code} {pc : Nat} {frames : List Bytecode.Frame} :
      CodeAt code pc (compileTm body) → MatchFrames stack frames →
      MatchFrames (.call ρ body :: stack) (.ret code pc ρ :: frames)
  | handler {h : Handler} {stack : List Core.Frame} {frames : List Bytecode.Frame} :
      MatchFrames stack frames → MatchFrames (.handler h :: stack) (.handler h :: frames)
  | label {id : Nat} {stack : List Core.Frame} {frames : List Bytecode.Frame} :
      MatchFrames stack frames → MatchFrames (.label id :: stack) (.label id :: frames)

theorem MatchFrames.append {a b : List Core.Frame} {a' b' : List Bytecode.Frame}
    (ha : MatchFrames a a') (hb : MatchFrames b b') : MatchFrames (a ++ b) (a' ++ b') := by
  induction ha with
  | nil => exact hb
  | call hc _ ih => exact .call hc ih
  | handler _ ih => exact .handler ih
  | label _ ih => exact .label ih

/-- A store entry is used up in both machines, or holds corresponding stacks. -/
inductive MatchCont : Option (List Core.Frame) → Option (List Bytecode.Frame) → Prop where
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
theorem take (h : MatchConts a b) : ∀ {id : Nat} {seg : List Core.Frame} {a₁ : Conts Core.Frame},
    takeCont a id = some (seg, a₁) →
    ∃ seg' b₁, takeCont b id = some (seg', b₁) ∧ MatchFrames seg seg' ∧ MatchConts a₁ b₁ := by
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
        = some ⟨above', d.handler, d.arm, below'⟩
      ∧ MatchFrames d.above above' ∧ MatchFrames d.below below' := by
  induction h with
  | nil => intro d hd; simp [findHandler] at hd
  | @call body ρ stack code pc frames hc hrest ih =>
    intro d hd
    cases hf : findHandler Core.Frame.asHandler op stack with
    | none => simp [findHandler, handles, Core.Frame.asHandler, hf] at hd
    | some d₀ =>
      simp [findHandler, handles, Core.Frame.asHandler, hf] at hd
      subst hd
      obtain ⟨above', below', hv, ha, hb⟩ := ih hf
      exact ⟨.ret code pc ρ :: above', below',
        by simp [findHandler, handles, Bytecode.Frame.asHandler, hv], .call hc ha, hb⟩
  | @handler h stack frames hrest ih =>
    intro d hd
    cases hl : h.ops.lookup op with
    | some arm =>
      simp [findHandler, handles, Core.Frame.asHandler, hl] at hd
      subst hd
      exact ⟨[], frames, by simp [findHandler, handles, Bytecode.Frame.asHandler, hl], .nil, hrest⟩
    | none =>
      cases hf : findHandler Core.Frame.asHandler op stack with
      | none => simp [findHandler, handles, Core.Frame.asHandler, hl, hf] at hd
      | some d₀ =>
        simp [findHandler, handles, Core.Frame.asHandler, hl, hf] at hd
        subst hd
        obtain ⟨above', below', hv, ha, hb⟩ := ih hf
        exact ⟨.handler h :: above', below',
          by simp [findHandler, handles, Bytecode.Frame.asHandler, hl, hv], .handler ha, hb⟩
  | @label id stack frames hrest ih =>
    intro d hd
    cases hf : findHandler Core.Frame.asHandler op stack with
    | none => simp [findHandler, handles, Core.Frame.asHandler, hf] at hd
    | some d₀ =>
      simp [findHandler, handles, Core.Frame.asHandler, hf] at hd
      subst hd
      obtain ⟨above', below', hv, ha, hb⟩ := ih hf
      exact ⟨.label id :: above', below',
        by simp [findHandler, handles, Bytecode.Frame.asHandler, hv], .label ha, hb⟩

/-- Searching corresponding stacks for a label scope finds it in both, with
corresponding frames below it. -/
theorem findLabel_sim {id : Nat} {stack : List Core.Frame} {frames : List Bytecode.Frame}
    (h : MatchFrames stack frames) : ∀ {below : List Core.Frame},
    findLabel Core.Frame.asLabel id stack = some below →
    ∃ below', findLabel Bytecode.Frame.asLabel id frames = some below'
      ∧ MatchFrames below below' := by
  induction h with
  | nil => intro below hb; simp [findLabel] at hb
  | call _ _ ih =>
    intro below hb
    simp [findLabel, Core.Frame.asLabel] at hb
    obtain ⟨below', hv, hm⟩ := ih hb
    exact ⟨below', by simp [findLabel, Bytecode.Frame.asLabel, hv], hm⟩
  | handler _ ih =>
    intro below hb
    simp [findLabel, Core.Frame.asLabel] at hb
    obtain ⟨below', hv, hm⟩ := ih hb
    exact ⟨below', by simp [findLabel, Bytecode.Frame.asLabel, hv], hm⟩
  | @label id' stack frames hrest ih =>
    intro below hb
    by_cases he : id' = id
    · subst he
      simp [findLabel, Core.Frame.asLabel] at hb
      subst hb
      exact ⟨frames, by simp [findLabel, Bytecode.Frame.asLabel], hrest⟩
    · simp [findLabel, Core.Frame.asLabel, he] at hb
      obtain ⟨below', hv, hm⟩ := ih hb
      exact ⟨below', by simp [findLabel, Bytecode.Frame.asLabel, he, hv], hm⟩

/-- The stores correspond: matching continuation entries and the same label counter. -/
inductive MatchStore : Store Core.Frame → Store Bytecode.Frame → Prop where
  | mk {conts : Conts Core.Frame} {conts' : Conts Bytecode.Frame} {labels : Nat} :
      MatchConts conts conts' → MatchStore ⟨conts, labels⟩ ⟨conts', labels⟩

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
some further steps matches again; if Core halts, the bytecode halts with the
same value; if Core is stuck, nothing is required.
-/
inductive SimOutcome (p : Core.Program) :
    Step Core.State Value → Step Bytecode.State Value → Prop where
  | next {s' : Core.State} {t₀ t' : Bytecode.State} {k : Nat} :
      run (Bytecode.step (compile p)) k t₀ = .next t' → Match s' t' →
      SimOutcome p (.next s') (.next t₀)
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
      ∧ run (Bytecode.step (compile p)) k ⟨code, 0, vs ++ captures, fr, ks⟩
          = .next ⟨code, pc, ρ', fr, ks⟩
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

theorem deliver_sim {v : Value} (hfr : MatchFrames stack frames) (hks : MatchStore store store') :
    SimOutcome p (Core.deliver p v stack store) (Bytecode.deliver (compile p) v frames store') := by
  induction hfr with
  | nil => exact .halt
  | @call body ρ stack code pc frames hc hrest _ =>
    show SimOutcome p (.next ⟨body, ρ ++ [v], stack, store⟩)
      (.next ⟨code, pc, ρ ++ [v], frames, store'⟩)
    exact .next (k := 0) rfl (.mk hc hrest hks)
  | handler hrest _ => exact callFn_sim hrest hks
  | label _ ih => exact ih

theorem apply_sim {c : Callee} (hfr : MatchFrames stack frames) (hks : MatchStore store store') :
    SimOutcome p (Core.apply p c stack store) (Bytecode.apply (compile p) c frames store') := by
  cases c with
  | fn fn captures vs => exact callFn_sim hfr hks
  | cont id v =>
    obtain @⟨conts, conts', labels, hcs⟩ := hks
    cases ht : takeCont conts id with
    | none =>
      have h1 : Core.apply p (.cont id v) stack ⟨conts, labels⟩ = .stuck := by
        simp [Core.apply, ht]
      rw [h1]
      exact .stuck
    | some r =>
      obtain ⟨seg, conts₁⟩ := r
      obtain ⟨seg', conts₁', ht', hseg, hcs₁⟩ := hcs.take ht
      have h1 : Core.apply p (.cont id v) stack ⟨conts, labels⟩
          = Core.deliver p v (seg ++ stack) ⟨conts₁, labels⟩ := by
        simp [Core.apply, ht]
      have h2 : Bytecode.apply (compile p) (.cont id v) frames ⟨conts', labels⟩
          = Bytecode.deliver (compile p) v (seg' ++ frames) ⟨conts₁', labels⟩ := by
        simp [Bytecode.apply, ht']
      rw [h1, h2]
      exact deliver_sim (hseg.append hfr) (.mk hcs₁)
  | label id v =>
    cases hl : findLabel Core.Frame.asLabel id stack with
    | none =>
      have h1 : Core.apply p (.label id v) stack store = .stuck := by simp [Core.apply, hl]
      rw [h1]
      exact .stuck
    | some below =>
      obtain ⟨below', hl', hb⟩ := findLabel_sim hfr hl
      have h1 : Core.apply p (.label id v) stack store = Core.deliver p v below store := by
        simp [Core.apply, hl]
      have h2 : Bytecode.apply (compile p) (.label id v) frames store'
          = Bytecode.deliver (compile p) v below' store' := by
        simp [Bytecode.apply, hl']
      rw [h1, h2]
      exact deliver_sim hb hks

end Outcomes

/-! ## One Core step is one or more bytecode steps -/

theorem step_sim (p : Core.Program) {s : Core.State} {t : Bytecode.State} (hm : Match s t) :
    SimOutcome p (Core.step p s) (Bytecode.step (compile p) t) := by
  obtain @⟨tm, ρ, stack, store, code, pc, frames, store', hcode, hfr, hstore⟩ := hm
  obtain @⟨conts, conts', labels, hcs⟩ := hstore
  have hks : MatchStore ⟨conts, labels⟩ ⟨conts', labels⟩ := .mk hcs
  cases tm with
  | ret a =>
    have hc : CodeAt code pc [Instr.ret a] := hcode
    have hi := hc.head
    cases ha : a.eval ρ with
    | none =>
      have h1 : Core.step p ⟨.ret a, ρ, stack, ⟨conts, labels⟩⟩ = .stuck := by simp [Core.step, ha]
      rw [h1]
      exact .stuck
    | some v =>
      have h1 : Core.step p ⟨.ret a, ρ, stack, ⟨conts, labels⟩⟩ = Core.deliver p v stack ⟨conts, labels⟩ := by
        simp [Core.step, ha]
      have h2 : Bytecode.step (compile p) ⟨code, pc, ρ, frames, ⟨conts', labels⟩⟩
          = Bytecode.deliver (compile p) v frames ⟨conts', labels⟩ := by
        simp [Bytecode.step, hi, ha]
      rw [h1, h2]
      exact deliver_sim hfr hks
  | let_ rhs body =>
    have hc : CodeAt code pc (Instr.op rhs :: compileTm body) := hcode
    have hi := hc.head
    cases hr : rhs.eval ρ with
    | none =>
      have h1 : Core.step p ⟨.let_ rhs body, ρ, stack, ⟨conts, labels⟩⟩ = .stuck := by
        simp [Core.step, hr]
      rw [h1]
      exact .stuck
    | some v =>
      have h1 : Core.step p ⟨.let_ rhs body, ρ, stack, ⟨conts, labels⟩⟩
          = .next ⟨body, ρ ++ [v], stack, ⟨conts, labels⟩⟩ := by
        simp [Core.step, hr]
      have h2 : Bytecode.step (compile p) ⟨code, pc, ρ, frames, ⟨conts', labels⟩⟩
          = .next ⟨code, pc + 1, ρ ++ [v], frames, ⟨conts', labels⟩⟩ := by
        simp [Bytecode.step, hi, hr]
      rw [h1, h2]
      exact .next (k := 0) rfl (.mk hc.tail hfr hks)
  | call f args body =>
    have hc : CodeAt code pc (Instr.call f args :: compileTm body) := hcode
    have hi := hc.head
    cases he : evalCall ρ f args with
    | none =>
      have h1 : Core.step p ⟨.call f args body, ρ, stack, ⟨conts, labels⟩⟩ = .stuck := by
        simp [Core.step, he]
      rw [h1]
      exact .stuck
    | some c =>
      have h1 : Core.step p ⟨.call f args body, ρ, stack, ⟨conts, labels⟩⟩
          = Core.apply p c (.call ρ body :: stack) ⟨conts, labels⟩ := by
        simp [Core.step, he]
      have h2 : Bytecode.step (compile p) ⟨code, pc, ρ, frames, ⟨conts', labels⟩⟩
          = Bytecode.apply (compile p) c (.ret code (pc + 1) ρ :: frames) ⟨conts', labels⟩ := by
        simp [Bytecode.step, hi, he]
      rw [h1, h2]
      exact apply_sim (.call hc.tail hfr) hks
  | tail f args =>
    have hc : CodeAt code pc [Instr.tail f args] := hcode
    have hi := hc.head
    cases he : evalCall ρ f args with
    | none =>
      have h1 : Core.step p ⟨.tail f args, ρ, stack, ⟨conts, labels⟩⟩ = .stuck := by simp [Core.step, he]
      rw [h1]
      exact .stuck
    | some c =>
      have h1 : Core.step p ⟨.tail f args, ρ, stack, ⟨conts, labels⟩⟩ = Core.apply p c stack ⟨conts, labels⟩ := by
        simp [Core.step, he]
      have h2 : Bytecode.step (compile p) ⟨code, pc, ρ, frames, ⟨conts', labels⟩⟩
          = Bytecode.apply (compile p) c frames ⟨conts', labels⟩ := by
        simp [Bytecode.step, hi, he]
      rw [h1, h2]
      exact apply_sim hfr hks
  | handle ret ops captures thunk body =>
    have hc : CodeAt code pc (Instr.handle ret ops captures thunk :: compileTm body) := hcode
    have hi := hc.head
    cases hcap : evalAtoms ρ captures with
    | none =>
      have h1 : Core.step p ⟨.handle ret ops captures thunk body, ρ, stack, ⟨conts, labels⟩⟩ = .stuck := by
        simp [Core.step, hcap]
      rw [h1]
      exact .stuck
    | some caps =>
      cases he : evalCall ρ thunk [] with
      | none =>
        have h1 : Core.step p ⟨.handle ret ops captures thunk body, ρ, stack, ⟨conts, labels⟩⟩
            = .stuck := by
          simp [Core.step, hcap, he]
        rw [h1]
        exact .stuck
      | some c =>
        have h1 : Core.step p ⟨.handle ret ops captures thunk body, ρ, stack, ⟨conts, labels⟩⟩
            = Core.apply p c (.handler ⟨ret, ops, caps⟩ :: .call ρ body :: stack) ⟨conts, labels⟩ := by
          simp [Core.step, hcap, he]
        have h2 : Bytecode.step (compile p) ⟨code, pc, ρ, frames, ⟨conts', labels⟩⟩
            = Bytecode.apply (compile p) c
                (.handler ⟨ret, ops, caps⟩ :: .ret code (pc + 1) ρ :: frames) ⟨conts', labels⟩ := by
          simp [Bytecode.step, hi, hcap, he]
        rw [h1, h2]
        exact apply_sim (.handler (.call hc.tail hfr)) hks
  | raise op args =>
    have hc : CodeAt code pc [Instr.raise op args] := hcode
    have hi := hc.head
    cases hv : evalAtoms ρ args with
    | none =>
      have h1 : Core.step p ⟨.raise op args, ρ, stack, ⟨conts, labels⟩⟩ = .stuck := by simp [Core.step, hv]
      rw [h1]
      exact .stuck
    | some vs =>
      cases hf : findHandler Core.Frame.asHandler op stack with
      | none =>
        have h1 : Core.step p ⟨.raise op args, ρ, stack, ⟨conts, labels⟩⟩ = .stuck := by
          simp [Core.step, hv, hf]
        rw [h1]
        exact .stuck
      | some d =>
        obtain ⟨above', below', hf', _, hbelow⟩ := find_sim hfr hf
        have h1 : Core.step p ⟨.raise op args, ρ, stack, ⟨conts, labels⟩⟩
            = Core.callFn p d.arm d.handler.caps vs d.below ⟨conts, labels⟩ := by
          simp [Core.step, hv, hf]
        have h2 : Bytecode.step (compile p) ⟨code, pc, ρ, frames, ⟨conts', labels⟩⟩
            = Bytecode.callFn (compile p) d.arm d.handler.caps vs below' ⟨conts', labels⟩ := by
          simp [Bytecode.step, hi, hv, hf']
        rw [h1, h2]
        exact callFn_sim hbelow hks
  | perform op args body =>
    have hc : CodeAt code pc (Instr.perform op args :: compileTm body) := hcode
    have hi := hc.head
    cases hv : evalAtoms ρ args with
    | none =>
      have h1 : Core.step p ⟨.perform op args body, ρ, stack, ⟨conts, labels⟩⟩ = .stuck := by
        simp [Core.step, hv]
      rw [h1]
      exact .stuck
    | some vs =>
      cases hf : findHandler Core.Frame.asHandler op stack with
      | none =>
        have h1 : Core.step p ⟨.perform op args body, ρ, stack, ⟨conts, labels⟩⟩ = .stuck := by
          simp [Core.step, hv, hf]
        rw [h1]
        exact .stuck
      | some d =>
        obtain ⟨above', below', hf', habove, hbelow⟩ := find_sim hfr hf
        have h1 : Core.step p ⟨.perform op args body, ρ, stack, ⟨conts, labels⟩⟩
            = Core.callFn p d.arm d.handler.caps (vs ++ [.cont conts.length]) d.below
                ⟨conts ++ [some (.call ρ body :: d.above ++ [.handler d.handler])], labels⟩ := by
          simp [Core.step, hv, hf]
        have h2 : Bytecode.step (compile p) ⟨code, pc, ρ, frames, ⟨conts', labels⟩⟩
            = Bytecode.callFn (compile p) d.arm d.handler.caps (vs ++ [.cont conts.length]) below'
                ⟨conts' ++ [some (.ret code (pc + 1) ρ :: above' ++ [.handler d.handler])],
                  labels⟩ := by
          simp [Bytecode.step, hi, hv, hf', hcs.length_eq]
        rw [h1, h2]
        exact callFn_sim hbelow
          (.mk (hcs.snoc (.full (.call hc.tail (habove.append (.handler .nil))))))
  | label thunk body =>
    have hc : CodeAt code pc (Instr.label thunk :: compileTm body) := hcode
    have hi := hc.head
    cases he : evalClosure ρ thunk with
    | none =>
      have h1 : Core.step p ⟨.label thunk body, ρ, stack, ⟨conts, labels⟩⟩ = .stuck := by
        simp [Core.step, he]
      rw [h1]
      exact .stuck
    | some r =>
      obtain ⟨fn, captures⟩ := r
      have h1 : Core.step p ⟨.label thunk body, ρ, stack, ⟨conts, labels⟩⟩
          = Core.callFn p fn captures [.label labels]
              (.label labels :: .call ρ body :: stack) ⟨conts, labels + 1⟩ := by
        simp [Core.step, he]
      have h2 : Bytecode.step (compile p) ⟨code, pc, ρ, frames, ⟨conts', labels⟩⟩
          = Bytecode.callFn (compile p) fn captures [.label labels]
              (.label labels :: .ret code (pc + 1) ρ :: frames) ⟨conts', labels + 1⟩ := by
        simp [Bytecode.step, hi, he]
      rw [h1, h2]
      exact callFn_sim (.label (.call hc.tail hfr)) (.mk hcs)

/-- `Match` is a forward simulation from Core to bytecode. -/
theorem forwardSim (p : Core.Program) :
    ForwardSim (Core.step p) (Bytecode.step (compile p)) Match where
  next := by
    intro s t s' hm hs
    have h := step_sim p hm
    rw [hs] at h
    generalize hstep : Bytecode.step (compile p) t = r at h
    cases h with
    | @next _ t₀ t' k hk hm' =>
      exact ⟨k, t', by rw [run_succ, hstep, Step.bind_next]; exact hk, hm'⟩
  halt := by
    intro s t v hm hs
    have h := step_sim p hm
    rw [hs] at h
    generalize hstep : Bytecode.step (compile p) t = r at h
    cases h with
    | halt => exact ⟨0, run_one_halt hstep⟩

/-! ## Behaviour preservation -/

/-- If the Core program halts with `v`, so does its bytecode. -/
theorem compile_halts {p : Core.Program} {v : Value} :
    Core.Halts p v → Bytecode.Halts (compile p) v :=
  (forwardSim p).halts (match_init p)

/-- If the Core program runs forever, so does its bytecode. -/
theorem compile_diverges {p : Core.Program} :
    Core.Diverges p → Bytecode.Diverges (compile p) :=
  (forwardSim p).diverges (match_init p)

/-- A result computed by the bytecode is a result of the Core program, unless
the Core program goes wrong. -/
theorem compile_halts_reflect {p : Core.Program} {v : Value} :
    Bytecode.Halts (compile p) v → Core.Halts p v ∨ Core.GoesWrong p :=
  (forwardSim p).halts_reflect (match_init p)

/--
**Compiler correctness.** For a Core program that does not go wrong, the
compiled bytecode has exactly the same behaviour: it halts with the same values,
it diverges exactly when the Core program does, and it never goes wrong.
-/
theorem compile_correct (p : Core.Program) (safe : ¬ Core.GoesWrong p) :
    (∀ v, Bytecode.Halts (compile p) v ↔ Core.Halts p v)
    ∧ (Bytecode.Diverges (compile p) ↔ Core.Diverges p)
    ∧ ¬ Bytecode.GoesWrong (compile p) := by
  refine ⟨fun v => ⟨fun h => ?_, compile_halts⟩, ⟨?_, compile_diverges⟩, ?_⟩
  · exact (compile_halts_reflect h).resolve_right safe
  · exact (forwardSim p).diverges_reflect (match_init p) safe
  · exact (forwardSim p).not_goesWrong (match_init p) safe

end Glorious
