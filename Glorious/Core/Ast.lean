import Glorious.Value

/-!
# Core syntax

Core is the elaborated kernel language: every intermediate result is named and
every callable is a closed function with an explicit capture list. This file
covers the first fragment: data, closures, calls and tail calls.
-/

namespace Glorious.Core

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

/-- A function. Its body runs in the environment `captures ++ arguments`. -/
structure Fn where
  arity : Nat
  body : Tm

structure Program where
  fns : List Fn
  main : Tm

end Glorious.Core
