import Glorious.Machine
import Glorious.Control
import Glorious.Core.Ast

/-!
# Core semantics

The meaning of a Core program, as an abstract machine. This file is the
definition the compiler is proved against.
-/

namespace Glorious.Core

mutual

/-- Match a value against a pattern. On success, the bound values in binder order. -/
def Pat.matchVal : Pat → Value → Option (List Value)
  | .wild, _ => some []
  | .bind, v => some [v]
  | .int n, .int m => if n = m then some [] else none
  | .int _, .data _ _ => none
  | .int _, .clo _ _ => none
  | .int _, .cont _ => none
  | .ctor tag ps, .data t fields => if tag = t then Pat.matchVals ps fields else none
  | .ctor _ _, .int _ => none
  | .ctor _ _, .clo _ _ => none
  | .ctor _ _, .cont _ => none

/-- Match values against patterns pointwise. The two lists must have the same length. -/
def Pat.matchVals : List Pat → List Value → Option (List Value)
  | [], [] => some []
  | p :: ps, v :: vs =>
    match p.matchVal v, Pat.matchVals ps vs with
    | some b, some bs => some (b ++ bs)
    | _, _ => none
  | [], _ :: _ => none
  | _ :: _, [] => none

end

/-- The first clause whose patterns match the arguments: its body and bindings.
A clause with the wrong number of patterns has no meaning. -/
def selectClause : List Clause → List Value → Option (Tm × List Value)
  | [], _ => none
  | c :: cs, vs =>
    if c.pats.length = vs.length then
      match Pat.matchVals c.pats vs with
      | some bs => some (c.body, bs)
      | none => selectClause cs vs
    else none

/-- A stack frame. -/
inductive Frame where
  /-- A suspended caller: the environment and the code waiting for a result. -/
  | call (env : Env) (body : Tm)
  /-- The delimiter of an installed handler. -/
  | handler (h : Handler)

def Frame.asHandler : Frame → Option Handler
  | .call _ _ => none
  | .handler h => some h

structure State where
  tm : Tm
  env : Env
  stack : List Frame
  conts : Conts Frame

/-- Select the clause of function `fn` matching the arguments: its body and the
environment it starts in, `arguments ++ captures ++ bindings`. -/
def invoke (p : Program) (fn : Nat) (captures vs : List Value) : Option (Tm × Env) :=
  match p.fns[fn]? with
  | some F =>
    match selectClause F.clauses vs with
    | some (body, bs) => some (body, vs ++ captures ++ bs)
    | none => none
  | none => none

/-- Start running a function on top of `stack`. -/
def callFn (p : Program) (fn : Nat) (captures vs : List Value) (stack : List Frame)
    (conts : Conts Frame) : Step State Value :=
  match invoke p fn captures vs with
  | some (body, ρ) => .next ⟨body, ρ, stack, conts⟩
  | none => .stuck

/-- Deliver a result to the top of `stack`. A caller binds it; a handler's
delimiter is removed and its completion function runs outside it. -/
def deliver (p : Program) (v : Value) (stack : List Frame) (conts : Conts Frame) :
    Step State Value :=
  match stack with
  | [] => .halt v
  | .call ρ body :: stack => .next ⟨body, ρ ++ [v], stack, conts⟩
  | .handler h :: stack => callFn p h.ret h.caps [v] stack conts

/-- Apply a callee on top of `stack`: enter a function, or reinstate a captured
continuation and deliver the argument to it. -/
def apply (p : Program) (c : Callee) (stack : List Frame) (conts : Conts Frame) :
    Step State Value :=
  match c with
  | .fn fn captures vs => callFn p fn captures vs stack conts
  | .cont id v =>
    match takeCont conts id with
    | some (segment, conts') => deliver p v (segment ++ stack) conts'
    | none => .stuck

def step (p : Program) (s : State) : Step State Value :=
  match s.tm with
  | .ret a =>
    match a.eval s.env with
    | none => .stuck
    | some v => deliver p v s.stack s.conts
  | .let_ rhs body =>
    match rhs.eval s.env with
    | none => .stuck
    | some v => .next ⟨body, s.env ++ [v], s.stack, s.conts⟩
  | .call f args body =>
    match evalCall s.env f args with
    | none => .stuck
    | some c => apply p c (.call s.env body :: s.stack) s.conts
  | .tail f args =>
    match evalCall s.env f args with
    | none => .stuck
    | some c => apply p c s.stack s.conts
  | .handle ret ops captures thunk body =>
    match evalAtoms s.env captures, evalCall s.env thunk [] with
    | some caps, some c =>
      apply p c (.handler ⟨ret, ops, caps⟩ :: .call s.env body :: s.stack) s.conts
    | _, _ => .stuck
  | .raise op args =>
    match evalAtoms s.env args with
    | none => .stuck
    | some vs =>
      match findHandler Frame.asHandler op s.stack with
      | none => .stuck
      | some d => callFn p d.arm d.handler.caps vs d.below s.conts
  | .perform op args body =>
    match evalAtoms s.env args with
    | none => .stuck
    | some vs =>
      match findHandler Frame.asHandler op s.stack with
      | none => .stuck
      | some d =>
        -- The continuation runs from the performer up to and including the
        -- handler, so resuming it reinstalls the handler: handlers are deep.
        callFn p d.arm d.handler.caps (vs ++ [.cont s.conts.length]) d.below
          (s.conts ++ [some (.call s.env body :: d.above ++ [.handler d.handler])])

def init (p : Program) : State := ⟨p.main, [], [], []⟩

/-- The program finishes with result `v`. -/
def Halts (p : Program) (v : Value) : Prop := Machine.Halts (step p) (init p) v

/-- The program reaches a state the semantics gives no meaning to. -/
def GoesWrong (p : Program) : Prop := Machine.GoesWrong (step p) (init p)

/-- The program runs forever. -/
def Diverges (p : Program) : Prop := Machine.Diverges (step p) (init p)

end Glorious.Core
