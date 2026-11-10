import Glorious.Machine
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
  | .ctor tag ps, .data t fields => if tag = t then Pat.matchVals ps fields else none
  | .ctor _ _, .int _ => none
  | .ctor _ _, .clo _ _ => none

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

/-- A suspended caller: the environment and the code waiting for a call's result. -/
structure Frame where
  env : Env
  body : Tm

structure State where
  tm : Tm
  env : Env
  stack : List Frame

/-- Resolve a call: the selected clause body and the environment it starts in.
The call is undefined unless the callee is a callable of a known function and
one of its clauses matches the arguments. -/
def enter (p : Program) (ρ : Env) (f : Atom) (args : List Atom) : Option (Tm × Env) :=
  match evalCall ρ f args with
  | some (fn, captures, vs) =>
    match p.fns[fn]? with
    | some F =>
      match selectClause F.clauses vs with
      | some (body, bs) => some (body, vs ++ captures ++ bs)
      | none => none
    | none => none
  | none => none

def step (p : Program) (s : State) : Step State Value :=
  match s.tm with
  | .ret a =>
    match a.eval s.env with
    | none => .stuck
    | some v =>
      match s.stack with
      | [] => .halt v
      | fr :: stack => .next ⟨fr.body, fr.env ++ [v], stack⟩
  | .let_ rhs body =>
    match rhs.eval s.env with
    | none => .stuck
    | some v => .next ⟨body, s.env ++ [v], s.stack⟩
  | .call f args body =>
    match enter p s.env f args with
    | none => .stuck
    | some (callee, ρ) => .next ⟨callee, ρ, ⟨s.env, body⟩ :: s.stack⟩
  | .tail f args =>
    match enter p s.env f args with
    | none => .stuck
    | some (callee, ρ) => .next ⟨callee, ρ, s.stack⟩

def init (p : Program) : State := ⟨p.main, [], []⟩

/-- The program finishes with result `v`. -/
def Halts (p : Program) (v : Value) : Prop := Machine.Halts (step p) (init p) v

/-- The program reaches a state the semantics gives no meaning to. -/
def GoesWrong (p : Program) : Prop := Machine.GoesWrong (step p) (init p)

/-- The program runs forever. -/
def Diverges (p : Program) : Prop := Machine.Diverges (step p) (init p)

end Glorious.Core
