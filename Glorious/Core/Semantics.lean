import Glorious.Machine
import Glorious.Core.Ast

/-!
# Core semantics

The meaning of a Core program, as an abstract machine. This file is the
definition the compiler is proved against.
-/

namespace Glorious.Core

/-- A suspended caller: the environment and the code waiting for a call's result. -/
structure Frame where
  env : Env
  body : Tm

structure State where
  tm : Tm
  env : Env
  stack : List Frame

/-- Resolve a call: the callee's body and the environment it starts in. The
call is undefined unless the callee is a callable of a known function and the
argument count matches. -/
def enter (p : Program) (ρ : Env) (f : Atom) (args : List Atom) : Option (Tm × Env) :=
  match evalCall ρ f args with
  | some (fn, captures, vs) =>
    match p.fns[fn]? with
    | some F => if vs.length = F.arity then some (F.body, captures ++ vs) else none
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
