import Glorious.Value

/-!
# Core syntax

Core is the elaborated kernel language: every intermediate result is named and
every callable is a closed function with an explicit capture list. This file
covers data, closures, calls, tail calls and pattern callables.
-/

namespace Glorious.Core

/-- A structural pattern. Binders are positional: each `bind` appends the
matched value to the environment, left to right. -/
inductive Pat where
  /-- Matches anything and binds nothing. -/
  | wild
  /-- Matches anything and binds it. -/
  | bind
  /-- Matches one integer constant. -/
  | int (n : Int)
  /-- Matches a `struct` or `enum` value with this constructor tag and one
  sub-pattern per field. -/
  | ctor (tag : Nat) (args : List Pat)

/-- A Core computation. Each binding form appends its result to the environment. -/
inductive Tm where
  /-- Return a value to the caller. -/
  | ret (a : Atom)
  /-- Bind the result of a control-free computation. -/
  | let_ (rhs : Rhs) (body : Tm)
  /-- Call a callable and bind its result. -/
  | call (f : Atom) (args : List Atom) (body : Tm)
  /-- Call a callable in place of the current activation. -/
  | tail (f : Atom) (args : List Atom)

/-- One clause of a callable: one pattern per argument, and a body. The body
runs in the environment `arguments ++ captures ++ pattern bindings`. -/
structure Clause where
  pats : List Pat
  body : Tm

/-- A callable: ordered clauses, the first matching one runs. -/
structure Fn where
  clauses : List Clause

structure Program where
  fns : List Fn
  main : Tm

end Glorious.Core
