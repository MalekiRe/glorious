import Glorious.Value

/-!
# Control structures shared by both machines

Handlers, the search for the handler of an operation, the search for a label
scope, the store of captured continuations, and memory. Both machines use these definitions on their own kind
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
  /-- A label and the value to leave its scope with. -/
  | label (id : Nat) (arg : Value)

/-- Evaluate the callee and arguments of a call. A resumption and a label each
take exactly one argument. -/
def evalCall (ρ : Env) (f : Atom) (args : List Atom) : Option Callee :=
  match f.eval ρ, evalAtoms ρ args with
  | some (.clo fn captures), some vs => some (.fn fn captures vs)
  | some (.cont id), some [v] => some (.cont id v)
  | some (.label id), some [v] => some (.label id v)
  | _, _ => none

/-- Evaluate an operand that must be a function closure. -/
def evalClosure (ρ : Env) (a : Atom) : Option (Nat × List Value) :=
  match a.eval ρ with
  | some (.clo fn captures) => some (fn, captures)
  | _ => none

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

/-- Captured continuations, indexed by resumption identity. A resumption is
one-shot: its entry holds the captured frames until it is resumed or cancelled,
and is empty afterwards. -/
abbrev Conts (φ : Type) := List (Option (List φ))

/-- Take a resumption's captured frames, leaving its entry empty. Resuming and
cancelling both do this, so a resumption that has been used cannot be used again. -/
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

/-- Evaluate an operand that must be a resumption. -/
def evalCont (ρ : Env) (a : Atom) : Option Nat :=
  match a.eval ρ with
  | some (.cont id) => some id
  | _ => none

/-- The frames above and below the scope of label `id`, if that scope is on the stack. -/
def findLabel {φ : Type} (asLabel : φ → Option Nat) (id : Nat) :
    List φ → Option (List φ × List φ)
  | [] => none
  | fr :: stack =>
    if asLabel fr = some id then some ([], stack)
    else
      match findLabel asLabel id stack with
      | some (above, below) => some (fr :: above, below)
      | none => none

/-- Operations on memory cells. -/
inductive MemOp where
  /-- Allocate a cell holding a value; the result is a reference to it. -/
  | alloc
  /-- Read the value a reference points to. -/
  | load
  /-- Replace the value a reference points to. -/
  | store
  /-- Release a cell. Using it afterwards has no meaning. -/
  | free

/-- Memory: a cell is live with a value, or has been freed. Addresses are never reused. -/
abbrev Cells := List (Option Value)

/-- Perform a memory operation: its result and the memory afterwards. -/
def MemOp.eval (cells : Cells) : MemOp → List Value → Option (Value × Cells)
  | .alloc, [v] => some (.ref cells.length, cells ++ [some v])
  | .load, [.ref a] =>
    match cells[a]? with
    | some (some v) => some (v, cells)
    | _ => none
  | .store, [.ref a, v] =>
    match cells[a]? with
    | some (some _) => some (.unit, cells.set a (some v))
    | _ => none
  | .free, [.ref a] =>
    match cells[a]? with
    | some (some _) => some (.unit, cells.set a none)
    | _ => none
  | _, _ => none

/-- The machine state that is not on the stack. -/
structure Store (φ : Type) where
  conts : Conts φ
  /-- How many label scopes have been entered; the identity of the next one. -/
  labels : Nat
  cells : Cells

end Glorious
