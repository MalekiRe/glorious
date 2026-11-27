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
        { s.store with labels := s.store.labels + 1 }
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
        { s.store with labels := s.store.labels + 1 }
  | .handleTail ret ops captures thunk =>
    match evalAtoms s.env captures, evalCall s.env thunk [] with
    | some caps, some c =>
      applyStarts c (.handler s.store.labels ⟨ret, ops, caps⟩ :: s.stack)
        { s.store with labels := s.store.labels + 1 }
    | _, _ => 0
  | .labelTail thunk =>
    match evalScope s.env thunk (.label s.store.labels) with
    | none => 0
    | some c =>
      applyStarts c (.label s.store.labels :: s.stack)
        { s.store with labels := s.store.labels + 1 }
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
  | .cellL l init thunk body =>
    match (init.eval s.env).bind (s.store.allocLaid l) with
    | some (a, store) =>
      match evalScope s.env thunk (.ref a 0 []) with
      | some c => applyStarts c (.cell a :: .call s.env body :: s.stack) store
      | none => 0
    | none => 0
  | .cellTailL l init thunk =>
    match (init.eval s.env).bind (s.store.allocLaid l) with
    | some (a, store) =>
      match evalScope s.env thunk (.ref a 0 []) with
      | some c => applyStarts c (.cell a :: s.stack) store
      | none => 0
    | none => 0
  | .lend uniq r thunk pre post body =>
    match evalLend s.env r thunk pre post (s.store.labels + 1) with
    | none => 0
    | some (a, c) =>
      applyStarts c (.lend uniq a (s.store.labels + 1) :: .call s.env body :: s.stack)
        { s.store with labels := s.store.labels + 1 }
  | .mem _ _ _ | .host _ _ _ => 0

/-- How many guards a step installs: one, if it is a guard that is stepping. -/
def installs (s : State) : Nat :=
  match s.tm with
  | .guard _ _ _ => 1
  | .guardTail _ _ => 1
  | _ => 0

/-! ## The frames -/

/-! ## One step -/

/-! ## A whole run -/

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

end Glorious.Core
