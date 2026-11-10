import Glorious.Value

/-!
# Control structures shared by both machines

Handlers, the search for the handler of an operation, and the store of
captured continuations. Both machines use these definitions on their own kind
of stack frame.
-/

namespace Glorious

/-- An installed handler: the callable run on normal completion, the callable
serving each handled operation, and the captured values they all share. -/
structure Handler where
  ret : Nat
  ops : List (Nat × Nat)
  caps : List Value

/-- What a call applies to. -/
inductive Callee where
  /-- A function with its captured values and arguments. -/
  | fn (fn : Nat) (captures : List Value) (args : List Value)
  /-- A resumption and the value to resume it with. -/
  | cont (id : Nat) (arg : Value)

/-- Evaluate the callee and arguments of a call. A resumption takes exactly one argument. -/
def evalCall (ρ : Env) (f : Atom) (args : List Atom) : Option Callee :=
  match f.eval ρ, evalAtoms ρ args with
  | some (.clo fn captures), some vs => some (.fn fn captures vs)
  | some (.cont id), some [v] => some (.cont id v)
  | _, _ => none

/-- The nearest handler of an operation: the frames above it, the handler, the
callable serving the operation, and the frames below it. -/
structure Dispatch (φ : Type) where
  above : List φ
  handler : Handler
  arm : Nat
  below : List φ

/-- Does this frame handle `op`? -/
def handles {φ : Type} (asHandler : φ → Option Handler) (op : Nat) (fr : φ) :
    Option (Handler × Nat) :=
  match asHandler fr with
  | some h =>
    match h.ops.lookup op with
    | some arm => some (h, arm)
    | none => none
  | none => none

/-- Search a stack, top first, for the nearest handler with an arm for `op`.
Handlers without one are skipped. -/
def findHandler {φ : Type} (asHandler : φ → Option Handler) (op : Nat) :
    List φ → Option (Dispatch φ)
  | [] => none
  | fr :: stack =>
    match handles asHandler op fr with
    | some (h, arm) => some ⟨[], h, arm, stack⟩
    | none =>
      match findHandler asHandler op stack with
      | some d => some ⟨fr :: d.above, d.handler, d.arm, d.below⟩
      | none => none

/-- Captured continuations, indexed by resumption identity. An entry is emptied
when its resumption is used: resumptions are one-shot. -/
abbrev Conts (φ : Type) := List (Option (List φ))

/-- Take a captured continuation out of the store, leaving its entry empty. -/
def takeCont {α : Type} : List (Option α) → Nat → Option (α × List (Option α))
  | [], _ => none
  | c :: cs, 0 =>
    match c with
    | some x => some (x, none :: cs)
    | none => none
  | c :: cs, id + 1 =>
    match takeCont cs id with
    | some (x, cs') => some (x, c :: cs')
    | none => none

end Glorious
