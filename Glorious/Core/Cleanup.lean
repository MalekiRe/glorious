module

public import Glorious.Core.Semantics

/-!
# Every cleanup is accounted for

A cleanup is installed by a guard. This file counts, along a run of the Core
machine, how many guards were installed and how many cleanups were started, and
proves that the two differ by exactly the guards that are still waiting: those
on the stack, and those inside resumptions that have not been taken.

So when a program finishes, every cleanup it installed was started, except the
ones captured by a resumption that was never resumed or cancelled. Nothing here
depends on typing; it is a fact about the machine.

The count is of cleanups started. One that is started may itself not finish.
Guards are counted, not told apart: the statement is that none is lost and none
is made from nothing, which leaves no room for one to run twice.
-/

@[expose] public section

namespace Glorious.Core

/-- The guards among some frames. -/
def guards : List Frame → Nat
  | [] => 0
  | .guard _ _ :: stack => guards stack + 1
  | .call _ _ :: stack => guards stack
  | .handler _ _ :: stack => guards stack
  | .label _ :: stack => guards stack
  | .cell _ :: stack => guards stack
  | .lend _ _ _ :: stack => guards stack
  | .yield _ :: stack => guards stack
  | .exit _ _ :: stack => guards stack

/-- The guards inside resumptions that have not been taken. -/
def held : Conts Frame → Nat
  | [] => 0
  | some segment :: conts => guards segment + held conts
  | none :: conts => held conts

/-- The guards whose cleanup is still to run: on the stack, or captured. -/
def owed (s : State) : Nat := guards s.stack + held s.store.conts

mutual

/-- How many cleanups delivering a value to a stack starts: one, if the first
frame that does not simply pass the value on is a guard. -/
def deliverStarts : List Frame → Nat
  | [] => 0
  | .call _ _ :: _ => 0
  | .handler _ _ :: _ => 0
  | .label _ :: stack => deliverStarts stack
  | .guard _ _ :: _ => 1
  | .cell _ :: stack => deliverStarts stack
  | .lend _ _ _ :: stack => deliverStarts stack
  | .yield _ :: stack => deliverStarts stack
  | .exit target after :: stack => leaveStarts target after stack

/-- How many cleanups leaving for `target` starts: one, if a guard is met
before the target, or once the target yields. -/
def leaveStarts (target : Target) (after : After) : List Frame → Nat
  | [] => 0
  | fr :: stack =>
    if fr.isTarget target then
      match after with
      | .yield _ => deliverStarts stack
      | .invoke _ _ _ => 0
    else
      match fr with
      | .guard _ _ => 1
      | _ => leaveStarts target after stack

end

/-- How many cleanups applying a callee starts. -/
def applyStarts (c : Callee) (stack : List Frame) (store : Store Frame) : Nat :=
  match c with
  | .fn _ _ _ => 0
  | .cont id _ =>
    match takeCont store.conts id with
    | some (segment, _) => deliverStarts (segment ++ stack)
    | none => 0
  | .label id v => leaveStarts (.label id) (.yield v) stack

/-- How many cleanups a step of the machine starts: none or one. It follows
`step` case by case. -/
def starts (s : State) : Nat :=
  match s.tm with
  | .ret _ => deliverStarts s.stack
  | .let_ _ _ => 0
  | .call f args body =>
    match evalCall s.env f args with
    | some c => applyStarts c (.call s.env body :: s.stack) s.store
    | none => 0
  | .tail f args =>
    match evalCall s.env f args with
    | some c => applyStarts c s.stack s.store
    | none => 0
  | .handle ret ops captures thunk body =>
    match evalAtoms s.env captures, evalCall s.env thunk [] with
    | some caps, some c =>
      applyStarts c (.handler s.store.labels ⟨ret, ops, caps⟩ :: .call s.env body :: s.stack)
        ⟨s.store.conts, s.store.labels + 1, s.store.cells⟩
    | _, _ => 0
  | .raise op args =>
    match evalAtoms s.env args with
    | none => 0
    | some vs =>
      match findHandler Frame.asHandler op s.stack with
      | none => 0
      | some d => leaveStarts (.handler d.id) (.invoke d.arm d.handler.caps vs) s.stack
  | .perform _ _ _ => 0
  | .label thunk body =>
    match evalScope s.env thunk (.label s.store.labels) with
    | none => 0
    | some c =>
      applyStarts c (.label s.store.labels :: .call s.env body :: s.stack)
        ⟨s.store.conts, s.store.labels + 1, s.store.cells⟩
  | .handleTail ret ops captures thunk =>
    match evalAtoms s.env captures, evalCall s.env thunk [] with
    | some caps, some c =>
      applyStarts c (.handler s.store.labels ⟨ret, ops, caps⟩ :: s.stack)
        ⟨s.store.conts, s.store.labels + 1, s.store.cells⟩
    | _, _ => 0
  | .labelTail thunk =>
    match evalScope s.env thunk (.label s.store.labels) with
    | none => 0
    | some c =>
      applyStarts c (.label s.store.labels :: s.stack)
        ⟨s.store.conts, s.store.labels + 1, s.store.cells⟩
  | .guard cleanup thunk body =>
    match evalClosure s.env cleanup, evalCall s.env thunk [] with
    | some (fn, captures), some c =>
      applyStarts c (.guard fn captures :: .call s.env body :: s.stack) s.store
    | _, _ => 0
  | .guardTail cleanup thunk =>
    match evalClosure s.env cleanup, evalCall s.env thunk [] with
    | some (fn, captures), some c => applyStarts c (.guard fn captures :: s.stack) s.store
    | _, _ => 0
  | .cancel k body =>
    match evalCont s.env k with
    | some (some id) =>
      match takeCont s.store.conts id with
      | some (segment, _) =>
        leaveStarts (.label s.store.labels) (.yield .unit)
          (segment ++ .yield .unit :: .label s.store.labels :: .call s.env body :: s.stack)
      | none => 0
    | _ => 0
  | .cell init thunk body =>
    match init.eval s.env, evalScope s.env thunk (.ref s.store.cells.size 0 []) with
    | some v, some c =>
      applyStarts c (.cell s.store.cells.size :: .call s.env body :: s.stack) (s.store.alloc v)
    | _, _ => 0
  | .cellTail init thunk =>
    match init.eval s.env, evalScope s.env thunk (.ref s.store.cells.size 0 []) with
    | some v, some c => applyStarts c (.cell s.store.cells.size :: s.stack) (s.store.alloc v)
    | _, _ => 0
  | .lend uniq r thunk pre post body =>
    match evalLend s.env r thunk pre post (s.store.labels + 1) with
    | none => 0
    | some (a, c) =>
      applyStarts c (.lend uniq a (s.store.labels + 1) :: .call s.env body :: s.stack)
        ⟨s.store.conts, s.store.labels + 1, s.store.cells⟩
  | .mem _ _ _ | .host _ _ _ => 0

/-- How many guards a step installs: one, if it is a guard that is stepping. -/
def installs (s : State) : Nat :=
  match s.tm with
  | .guard _ _ _ => 1
  | .guardTail _ _ => 1
  | _ => 0

/-! ## The frames -/

theorem guards_append (a b : List Frame) : guards (a ++ b) = guards a + guards b := by
  induction a with
  | nil => simp [guards]
  | cons fr a ih => cases fr <;> simp [guards, ih] <;> omega

theorem held_snoc (conts : Conts Frame) (segment : List Frame) :
    held (conts ++ [some segment]) = held conts + guards segment := by
  induction conts with
  | nil => simp [held]
  | cons c conts ih => cases c <;> simp [held, ih] <;> omega

theorem takeCont_held {conts conts' : Conts Frame} {id : Nat} {segment : List Frame}
    (h : takeCont conts id = some (segment, conts')) :
    held conts = guards segment + held conts' := by
  induction conts generalizing id conts' with
  | nil => simp [takeCont] at h
  | cons c conts ih =>
    cases id with
    | zero =>
      cases c with
      | none => simp [takeCont] at h
      | some x =>
        simp only [takeCont, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [held]
    | succ id =>
      simp only [takeCont] at h
      cases ht : takeCont conts id with
      | none => rw [ht] at h; cases h
      | some r =>
        obtain ⟨x, cs'⟩ := r
        rw [ht] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have := ih ht
        cases c <;> simp [held] <;> omega

/-- The frames a handler is found under and the frames below it are all the
guards there are: the handler itself is not one. -/
theorem findHandler_guards {op : Nat} {stack : List Frame} {d : Dispatch Frame}
    (h : findHandler Frame.asHandler op stack = some d) :
    guards stack = guards d.above + guards d.below := by
  induction stack generalizing d with
  | nil => simp [findHandler] at h
  | cons fr stack ih =>
    simp only [findHandler] at h
    cases hh : handles Frame.asHandler op fr with
    | some x =>
      obtain ⟨id, hd, arm⟩ := x
      rw [hh] at h
      simp only [Option.some.injEq] at h
      subst h
      cases fr <;> simp [handles, Frame.asHandler] at hh <;> simp [guards]
    | none =>
      rw [hh] at h
      cases hf : findHandler Frame.asHandler op stack with
      | none => rw [hf] at h; cases h
      | some d' =>
        rw [hf] at h
        simp only [Option.some.injEq] at h
        subst h
        have := ih hf
        cases fr <;> simp [guards] <;> omega

/-! ## One step -/

theorem callFn_next {p : Program} {fn : Nat} {captures vs : List Value} {stack : List Frame}
    {store : Store Frame} {s' : State} (h : callFn p fn captures vs stack store = .next s') :
    s'.stack = stack ∧ s'.store = store := by
  unfold callFn at h
  cases hi : invoke p fn captures vs with
  | none => rw [hi] at h; cases h
  | some r =>
    obtain ⟨body, ρ⟩ := r
    rw [hi] at h
    cases h
    exact ⟨rfl, rfl⟩

theorem callFn_not_halt {p : Program} {fn : Nat} {captures vs : List Value} {stack : List Frame}
    {store : Store Frame} {v : Value} : callFn p fn captures vs stack store ≠ .halt v := by
  unfold callFn
  cases invoke p fn captures vs with
  | none => simp
  | some r => simp

/-- Delivering and leaving neither lose a guard nor make one: each guard that
goes from the stack has its cleanup started. Resumptions are not touched. -/
theorem deliver_leave_next (p : Program) (stack : List Frame) :
    (∀ (v : Value) (store : Store Frame) (s' : State), deliver p v stack store = .next s' →
        guards s'.stack + deliverStarts stack = guards stack ∧ s'.store.conts = store.conts)
    ∧ (∀ (target : Target) (after : After) (store : Store Frame) (s' : State),
        leave p target after stack store = .next s' →
        guards s'.stack + leaveStarts target after stack = guards stack
          ∧ s'.store.conts = store.conts) := by
  induction stack with
  | nil =>
    refine ⟨fun v store s' h => ?_, fun target after store s' h => ?_⟩
    · simp [deliver] at h
    · simp [leave] at h
  | cons fr stack ih =>
    obtain ⟨ihd, ihl⟩ := ih
    refine ⟨fun v store s' h => ?_, fun target after store s' h => ?_⟩
    · cases fr <;> simp only [deliver] at h <;>
        first
        | (cases h; simp [deliverStarts, guards]; done)
        | exact (fun ⟨e₁, e₂⟩ => by simp [deliverStarts, guards, e₁, e₂]) (callFn_next h)
        | simpa [deliverStarts, guards, Store.release] using ihd _ _ s' h
        | simpa [deliverStarts, guards] using ihl _ _ _ s' h
    · simp only [leave] at h
      cases ht : fr.isTarget target with
      | true =>
        simp only [ht, ↓reduceIte] at h
        have hg : guards (fr :: stack) = guards stack := by
          cases fr <;> cases target <;> simp [Frame.isTarget] at ht <;> simp [guards]
        cases after with
        | yield v =>
          simp only at h
          have := ihd v store s' h
          simpa [leaveStarts, ht, hg] using this
        | invoke fn captures args =>
          simp only at h
          obtain ⟨e₁, e₂⟩ := callFn_next h
          simp [leaveStarts, ht, hg, e₁, e₂]
      | false =>
        simp only [ht, Bool.false_eq_true, ↓reduceIte] at h
        cases fr <;> simp only at h <;>
          first
          | exact (fun ⟨e₁, e₂⟩ => by simp [leaveStarts, ht, guards, e₁, e₂]) (callFn_next h)
          | simpa [leaveStarts, ht, guards, Store.release] using ihl target after _ s' h

/-- A machine does not finish past a guard: finishing means the stack held none. -/
theorem deliver_leave_halt (p : Program) (stack : List Frame) :
    (∀ (v w : Value) (store : Store Frame), deliver p v stack store = .halt w →
        guards stack = 0)
    ∧ (∀ (target : Target) (after : After) (store : Store Frame) (w : Value),
        leave p target after stack store = .halt w → guards stack = 0) := by
  induction stack with
  | nil =>
    refine ⟨fun v w store _ => rfl, fun target after store w h => ?_⟩
    simp [leave] at h
  | cons fr stack ih =>
    obtain ⟨ihd, ihl⟩ := ih
    refine ⟨fun v w store h => ?_, fun target after store w h => ?_⟩
    · cases fr <;> simp only [deliver] at h <;>
        first
        | exact absurd h callFn_not_halt
        | simpa [guards] using ihd _ w _ h
        | simpa [guards] using ihl _ _ _ w h
        | simp at h
    · simp only [leave] at h
      cases ht : fr.isTarget target with
      | true =>
        simp only [ht, ↓reduceIte] at h
        have hg : guards (fr :: stack) = guards stack := by
          cases fr <;> cases target <;> simp [Frame.isTarget] at ht <;> simp [guards]
        cases after with
        | yield v => simp only at h; rw [hg]; exact ihd v w store h
        | invoke fn captures args => simp only at h; exact absurd h callFn_not_halt
      | false =>
        simp only [ht, Bool.false_eq_true, ↓reduceIte] at h
        cases fr <;> simp only at h <;>
          first
          | exact absurd h callFn_not_halt
          | simpa [guards] using ihl target after _ w h

theorem apply_next {p : Program} {c : Callee} {stack : List Frame} {store : Store Frame}
    {s' : State} (h : apply p c stack store = .next s') :
    owed s' + applyStarts c stack store = guards stack + held store.conts := by
  cases c with
  | fn fn captures vs =>
    simp only [apply] at h
    obtain ⟨e₁, e₂⟩ := callFn_next h
    simp [owed, applyStarts, e₁, e₂]
  | cont id v =>
    simp only [apply] at h
    cases ht : takeCont store.conts id with
    | none => rw [ht] at h; cases h
    | some r =>
      obtain ⟨segment, conts⟩ := r
      rw [ht] at h
      simp only at h
      obtain ⟨e₁, e₂⟩ := (deliver_leave_next p (segment ++ stack)).1 v _ s' h
      have hk := takeCont_held ht
      have ha := guards_append segment stack
      simp only [owed, applyStarts, ht]
      simp only at e₂
      rw [e₂]
      omega
  | label id v =>
    simp only [apply] at h
    cases hf : findLabel Frame.asLabel id stack with
    | none => rw [hf] at h; cases h
    | some r =>
      rw [hf] at h
      simp only at h
      obtain ⟨e₁, e₂⟩ := (deliver_leave_next p stack).2 _ _ store s' h
      simp only [owed, applyStarts]
      rw [e₂]
      omega

theorem apply_halt {p : Program} {c : Callee} {stack : List Frame} {store : Store Frame}
    {w : Value} (h : apply p c stack store = .halt w) : guards stack = 0 := by
  cases c <;> simp only [apply] at h <;> (repeat' split at h) <;>
    first
    | exact absurd h callFn_not_halt
    | (cases h; done)
    | exact (deliver_leave_halt p stack).2 _ _ store w h
    | (have := (deliver_leave_halt p _).1 _ w _ h
       rw [guards_append] at this
       omega)

/-- **One step keeps the account.** The guards still owed, and the cleanups the
step started, are the guards that were owed and the one it may have installed. -/
theorem step_accounts {p : Program} {s s' : State} (h : step p s = .next s') :
    owed s' + starts s = owed s + installs s := by
  obtain ⟨tm, env, stack, store⟩ := s
  cases tm with
  | ret a =>
    simp only [step] at h
    cases ha : a.eval env with
    | none => rw [ha] at h; cases h
    | some v =>
      rw [ha] at h
      obtain ⟨e₁, e₂⟩ := (deliver_leave_next p stack).1 v store s' h
      simp only [owed, starts, installs]
      rw [e₂]
      omega
  | raise op args =>
    simp only [step] at h
    cases hvs : evalAtoms env args with
    | none => rw [hvs] at h; cases h
    | some vs =>
      rw [hvs] at h
      cases hd : findHandler Frame.asHandler op stack with
      | none => rw [hd] at h; cases h
      | some d =>
        rw [hd] at h
        obtain ⟨e₁, e₂⟩ := (deliver_leave_next p stack).2 _ _ store s' h
        simp only [owed, starts, installs, hvs, hd]
        rw [e₂]
        omega
  | perform op args body =>
    simp only [step] at h
    cases hvs : evalAtoms env args with
    | none => rw [hvs] at h; cases h
    | some vs =>
      rw [hvs] at h
      cases hd : findHandler Frame.asHandler op stack with
      | none => rw [hd] at h; cases h
      | some d =>
        rw [hd] at h
        obtain ⟨e₁, e₂⟩ := callFn_next h
        have hg := findHandler_guards hd
        have hk := held_snoc store.conts (.call env body :: d.above ++ [.handler d.id d.handler])
        have hx : guards (.call env body :: d.above ++ [.handler d.id d.handler])
            = guards d.above := by
          show guards (.call env body :: (d.above ++ [.handler d.id d.handler])) = guards d.above
          simp [guards, guards_append]
        simp only [owed, starts, installs, e₁, e₂]
        omega
  | cancel k body =>
    simp only [step] at h
    cases hd : dropOf p.drops env k with
    | some r =>
      obtain ⟨d, captures⟩ := r
      rw [hd] at h
      obtain ⟨e₁, e₂⟩ := callFn_next h
      have hk := evalCont_of_dropOf hd
      simp only [owed, starts, installs, hk, e₁, e₂]
      simp [guards]
    | none =>
    rw [hd] at h
    cases hk : evalCont env k with
    | none => rw [hk] at h; cases h
    | some o =>
      cases o with
      | none => rw [hk] at h; cases h; simp [owed, starts, installs, hk]
      | some id =>
        rw [hk] at h
        simp only at h
        cases ht : takeCont store.conts id with
        | none => rw [ht] at h; cases h
        | some r =>
          obtain ⟨segment, conts⟩ := r
          rw [ht] at h
          simp only at h
          obtain ⟨e₁, e₂⟩ := (deliver_leave_next p _).2 _ _ _ s' h
          have hh := takeCont_held ht
          have ha := guards_append segment
            (.yield .unit :: .label store.labels :: .call env body :: stack)
          simp only [guards] at ha
          simp only [owed, starts, installs, hk, ht]
          simp only at e₂
          rw [e₂]
          omega
  | call _ _ _
  | tail _ _
  | handle _ _ _ _ _
  | handleTail _ _ _ _
  | label _ _
  | labelTail _
  | guard _ _ _
  | guardTail _ _
  | cell _ _ _
  | cellTail _ _
  | lend _ _ _ _ _ _
  | let_ _ _
  | mem _ _ _ =>
    simp only [step] at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | (cases h; simp [owed, starts, installs]; done)
      | (have := apply_next h
         simp_all only [owed, starts, installs, guards, Store.alloc]
         omega)
  | host id args body => simp [step] at h

/-- A machine that finishes has no guard left on its stack, and its last step
installs none. -/
theorem step_halt {p : Program} {s : State} {w : Value} (h : step p s = .halt w) :
    guards s.stack = 0 := by
  obtain ⟨tm, env, stack, store⟩ := s
  cases tm <;> simp only [step] at h <;> (repeat' split at h) <;>
    first
    | (cases h; done)
    | exact absurd h callFn_not_halt
    | exact (deliver_leave_halt p stack).1 _ w _ h
    | exact (deliver_leave_halt p stack).2 _ _ _ w h
    | simpa [guards] using apply_halt h
    | (have := (deliver_leave_halt p _).2 _ _ _ w h
       rw [guards_append] at this
       simp only [guards] at this
       show guards stack = 0
       omega)

/-! ## A whole run -/

theorem stepIO_accounts {p : Program} {c c' : Config} (h : stepIO p c = .next c') :
    owed c'.state + starts c.state = owed c.state + installs c.state := by
  obtain ⟨s, w⟩ := c
  unfold stepIO at h
  by_cases hh : ∃ id args body, s.tm = .host id args body
  · obtain ⟨id, args, body, e⟩ := hh
    simp only [e] at h
    cases hvs : evalAtoms s.env args with
    | none => rw [hvs] at h; cases h
    | some vs =>
      rw [hvs] at h
      simp only at h
      cases hc : Host.call w id vs with
      | none => rw [hc] at h; cases h
      | some x =>
        rw [hc] at h
        cases h
        simp [owed, starts, installs, e]
  · have e : stepIO p ⟨s, w⟩ = lift w (step p s) := by
      unfold stepIO
      split
      · next id args body e => exact absurd ⟨id, args, body, e⟩ hh
      · rfl
    unfold stepIO at e
    rw [e] at h
    cases hs : step p s with
    | next s' =>
      rw [hs] at h
      cases h
      exact step_accounts hs
    | halt v => rw [hs] at h; cases h
    | stuck => rw [hs] at h; cases h

theorem stepIO_halt {p : Program} {c : Config} {r : Result} (h : stepIO p c = .halt r) :
    guards c.state.stack = 0 := by
  obtain ⟨s, w⟩ := c
  unfold stepIO at h
  split at h
  · next id args body e =>
    cases hvs : evalAtoms s.env args with
    | none => rw [hvs] at h; cases h
    | some vs =>
      rw [hvs] at h
      simp only at h
      cases hc : Host.call w id vs with
      | none => rw [hc] at h; cases h
      | some x => rw [hc] at h; cases h
  · cases hs : step p s with
    | next s' => rw [hs] at h; cases h
    | halt v => exact step_halt hs
    | stuck => rw [hs] at h; cases h

/-- The guards installed in the first `n` steps from `c`. -/
def installed (p : Program) : Nat → Config → Nat
  | 0, _ => 0
  | n + 1, c =>
    match stepIO p c with
    | .next c' => installs c.state + installed p n c'
    | _ => 0

/-- The cleanups started in the first `n` steps from `c`. -/
def started (p : Program) : Nat → Config → Nat
  | 0, _ => 0
  | n + 1, c =>
    match stepIO p c with
    | .next c' => starts c.state + started p n c'
    | _ => 0

/-- **Along a run, the account is kept.** After `n` steps the guards still owed
and the cleanups started are the guards owed at the outset and those installed. -/
theorem run_accounts (p : Program) (n : Nat) {c c' : Config}
    (h : Machine.run (stepIO p) n c = .next c') :
    owed c'.state + started p n c = owed c.state + installed p n c := by
  induction n generalizing c with
  | zero =>
    rw [Machine.run_zero] at h
    cases h
    simp [started, installed]
  | succ n ih =>
    rw [Machine.run_succ] at h
    cases hs : stepIO p c with
    | next c₁ =>
      rw [hs, Step.bind_next] at h
      have h₁ := stepIO_accounts hs
      have h₂ := ih h
      simp only [started, installed, hs]
      omega
    | halt v => rw [hs] at h; simp at h
    | stuck => rw [hs] at h; simp at h

/-- **Every cleanup is accounted for.** If a program runs for `n` steps and
then finishes, every guard it installed had its cleanup started, except those
held in resumptions that were never taken. -/
theorem cleanup_accounting {p : Program} {input : List Int} {n : Nat} {c : Config} {r : Result}
    (hrun : Machine.run (stepIO p) n (initIO p input) = .next c)
    (hhalt : stepIO p c = .halt r) :
    installed p n (initIO p input) = started p n (initIO p input) + held c.state.store.conts := by
  have h := run_accounts p n hrun
  have hz := stepIO_halt hhalt
  have h0 : owed (initIO p input).state = 0 := rfl
  rw [h0] at h
  unfold owed at h
  omega

/-- The same of a program that halts: there is a last state, and at it the
account stands. -/
theorem halts_cleanup_accounting {p : Program} {input : List Int} {r : Result}
    (h : Halts p input r) :
    ∃ n c, Machine.run (stepIO p) n (initIO p input) = .next c ∧ stepIO p c = .halt r
      ∧ installed p n (initIO p input)
          = started p n (initIO p input) + held c.state.store.conts := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨n, c, hrun, hhalt⟩ := Machine.halt_last hk
  exact ⟨n, c, hrun, hhalt, cleanup_accounting hrun hhalt⟩

/-- No resumption is left untaken. -/
def AllTaken (conts : Conts Frame) : Prop := ∀ o, o ∈ conts → o = none

theorem held_of_allTaken {conts : Conts Frame} (h : AllTaken conts) : held conts = 0 := by
  induction conts with
  | nil => rfl
  | cons o conts ih =>
    have ho := h o (List.mem_cons_self ..)
    subst ho
    exact ih fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- **Exactly as many cleanups start as were installed**, in a program that
finishes having taken every resumption it captured. -/
theorem cleanup_exact {p : Program} {input : List Int} {n : Nat} {c : Config} {r : Result}
    (hrun : Machine.run (stepIO p) n (initIO p input) = .next c)
    (hhalt : stepIO p c = .halt r) (htaken : AllTaken c.state.store.conts) :
    installed p n (initIO p input) = started p n (initIO p input) := by
  have := cleanup_accounting hrun hhalt
  rw [held_of_allTaken htaken] at this
  exact this

end Glorious.Core
