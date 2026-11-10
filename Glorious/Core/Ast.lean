import Glorious.Value

/-!
# Core syntax

Core is the elaborated kernel language: every intermediate result is named and
every callable is a closed function with an explicit capture list. This file
covers data, closures, calls, tail calls, pattern callables, and effects with
handlers and one-shot resumptions, label scopes, guaranteed cleanup, and host
operations.
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
  /-- Run the callable `thunk` under a handler and bind the handler's result.
  `ret` is the function run on normal completion; `ops` maps each handled
  operation to the function serving it; all of them share `captures`. -/
  | handle (ret : Nat) (ops : List (Nat × Nat)) (captures : List Atom) (thunk : Atom) (body : Tm)
  /-- Perform a terminal operation: the computation up to its handler is abandoned. -/
  | raise (op : Nat) (args : List Atom)
  /-- Perform a resumptive operation and bind the value it is resumed with. The
  serving function receives the arguments followed by the resumption. -/
  | perform (op : Nat) (args : List Atom) (body : Tm)
  /-- Run the callable `thunk` inside a fresh label scope, passing it the label,
  and bind the scope's result. Applying the label to a value leaves the scope
  with that value. -/
  | label (thunk : Atom) (body : Tm)
  /-- `handle` whose result is the result of the current activation: no caller
  frame is kept, so a handler re-installed by a tail call does not grow the stack. -/
  | handleTail (ret : Nat) (ops : List (Nat × Nat)) (captures : List Atom) (thunk : Atom)
  /-- `label` whose result is the result of the current activation. -/
  | labelTail (thunk : Atom)
  /-- Run the callable `thunk` and bind its result, with `cleanup` guaranteed to
  run when `thunk`'s computation is left by any path: a normal return, a label
  exit, a terminal operation, or cancellation of a resumption that captured it. -/
  | guard (cleanup : Atom) (thunk : Atom) (body : Tm)
  /-- `guard` whose result is the result of the current activation. -/
  | guardTail (cleanup : Atom) (thunk : Atom)
  /-- Give up a resumption without resuming it: the cleanups of the continuation
  it captured run, innermost first, and the result is unit. -/
  | cancel (k : Atom) (body : Tm)
  /-- Ask the host to perform operation `id` and bind its result. -/
  | host (id : Nat) (args : List Atom) (body : Tm)

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
