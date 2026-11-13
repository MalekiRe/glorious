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

/-- Where an exit is going: the scope of a label, or an installed handler. Each
is named by a number given to it when it was put on the stack. -/
inductive Target where
  | label (id : Nat)
  | handler (id : Nat)
  deriving DecidableEq

/-- What an exit does once it has arrived and removed its target. -/
inductive After where
  /-- Deliver a value to what is below. -/
  | yield (v : Value)
  /-- Run a function on what is below. -/
  | invoke (fn : Nat) (captures : List Value) (args : List Value)

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

/-- Evaluate the callable a label scope runs, applied to the scope's label. Any
callable taking one value will do: a function, a resumption or another label. -/
def evalScope (ρ : Env) (thunk : Atom) (label : Value) : Option Callee :=
  match thunk.eval ρ with
  | some (.clo fn captures) => some (.fn fn captures [label])
  | some (.cont id) => some (.cont id label)
  | some (.label id) => some (.label id label)
  | _ => none

/-- Evaluate a reference being lent and the call its scope makes: the callable
applied to `pre`, a reference to the same cell as the borrow `borrow`, and
`post`. Gives the address and the callee. The new reference is one more local
for as long as this takes, which makes it a call like any other. -/
def evalLend (ρ : Env) (r thunk : Atom) (pre post : List Atom) (borrow : Nat) :
    Option (Nat × Callee) :=
  match r.eval ρ with
  | some (.ref a _ path) =>
    match evalCall (ρ ++ [.ref a borrow path]) thunk (pre ++ .var ρ.length :: post) with
    | some c => some (a, c)
    | none => none
  | _ => none

/-- Evaluate an operand that must be a function closure. -/
def evalClosure (ρ : Env) (a : Atom) : Option (Nat × List Value) :=
  match a.eval ρ with
  | some (.clo fn captures) => some (fn, captures)
  | _ => none

/-- The nearest handler of an operation: the frames above it, its identity,
the handler, the callable serving the operation, and the frames below it. -/
structure Dispatch (φ : Type) where
  above : List φ
  id : Nat
  handler : Handler
  arm : Nat
  below : List φ

/-- Does this frame handle `op`? -/
def handles {φ : Type} (asHandler : φ → Option (Nat × Handler)) (op : Nat) (fr : φ) :
    Option (Nat × Handler × Nat) :=
  match asHandler fr with
  | some (id, h) =>
    match h.ops.lookup op with
    | some arm => some (id, h, arm)
    | none => none
  | none => none

/-- Search a stack, top first, for the nearest handler with an arm for `op`.
Handlers without one are skipped. -/
def findHandler {φ : Type} (asHandler : φ → Option (Nat × Handler)) (op : Nat) :
    List φ → Option (Dispatch φ)
  | [] => none
  | fr :: stack =>
    match handles asHandler op fr with
    | some (id, h, arm) => some ⟨[], id, h, arm, stack⟩
    | none =>
      match findHandler asHandler op stack with
      | some d => some ⟨fr :: d.above, d.id, d.handler, d.arm, d.below⟩
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

/-- Evaluate the operand of `cancel`, which gives up a callable without calling
it: a resumption, by its identity, or a function or label, for which there is
nothing to do. Anything else has no meaning. -/
def evalCont (ρ : Env) (a : Atom) : Option (Option Nat) :=
  match a.eval ρ with
  | some (.cont id) => some (some id)
  | some (.clo _ _) => some none
  | some (.label _) => some none
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

/-- Operations on memory cells. A cell is made and released by the scope it
belongs to, not by an operation: see `Tm.cell`. -/
inductive MemOp where
  /-- Read the value a reference points to. -/
  | load
  /-- Replace the value a reference points to. -/
  | store
  /-- Replace the value a reference points to, giving back the value that was
  there. The old value is moved out, not copied, so a cell can hold something
  that must not be duplicated. -/
  | swap
  /-- Which constructor built what a reference points to, or the field of it
  that a path of field numbers leads to. Nothing is read out: a cell can be
  asked this whatever it holds. -/
  | tag
  /-- A reference to a field of what a reference points to: the same cell and
  the same borrow, one field further in. Nothing is read, so whether the field
  is there is found when the reference is used. No field has a number below
  zero. Given a constructor as well, the field is that constructor's: the
  reference then leads somewhere only while the value is built by it. -/
  | focus

/-- The constructor of the value a path of field numbers leads to; `-1` if the
path leads nowhere, or to something no constructor built. -/
def tagAt : Value → List Value → Int
  | .data tag _, [] => tag
  | .data _ fields, .int i :: path =>
    if 0 ≤ i then
      match fields[i.toNat]? with
      | some field => tagAt field path
      | none => -1
    else -1
  | _, _ => -1

/-- Memory: a cell is live with a value, or has been freed. Addresses are never reused. -/
abbrev Cells := List (Option Value)

/-- Perform a memory operation: its result and the memory afterwards. -/
def MemOp.eval (cells : Cells) : MemOp → List Value → Option (Value × Cells)
  | .load, [.ref a _ p] =>
    match cells[a]? with
    | some (some v) => (v.part p).map (·, cells)
    | _ => none
  | .store, [.ref a _ p, w] =>
    match cells[a]? with
    | some (some v) => (v.putPart p w).map fun v' => (.unit, cells.set a (some v'))
    | _ => none
  | .swap, [.ref a _ p, w] =>
    match cells[a]? with
    | some (some v) =>
      match v.part p, v.putPart p w with
      | some old, some v' => some (old, cells.set a (some v'))
      | _, _ => none
    | _ => none
  | .tag, .ref a _ p :: path =>
    match cells[a]? with
    | some (some v) => (v.part p).map fun w => (.int (tagAt w path), cells)
    | _ => none
  | .focus, [.ref a b p, .int i] =>
    if 0 ≤ i then some (.ref a b (p ++ [⟨none, i.toNat⟩]), cells) else none
  -- The field of one of several constructors: the step says which.
  | .focus, [.ref a b p, .int i, .int built] =>
    if 0 ≤ i ∧ 0 ≤ built then some (.ref a b (p ++ [⟨some built.toNat, i.toNat⟩]), cells) else none
  | _, _ => none

/-- The machine state that is not on the stack. -/
structure Store (φ : Type) where
  conts : Conts φ
  /-- How many label scopes and handlers have been put on a stack; the identity
  of the next one. -/
  labels : Nat
  cells : Cells

/-- The store after the scope of cell `a` has ended: the cell is released. -/
def Store.release {φ : Type} (store : Store φ) (a : Nat) : Store φ :=
  ⟨store.conts, store.labels, store.cells.set a none⟩

/-- The store with a new cell holding `v`; its address is the old number of cells. -/
def Store.alloc {φ : Type} (store : Store φ) (v : Value) : Store φ :=
  ⟨store.conts, store.labels, store.cells ++ [some v]⟩

end Glorious
