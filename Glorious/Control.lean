module

public import Glorious.Value
public import Glorious.Lay

/-!
# Control structures shared by both machines

Handlers, the search for the handler of an operation, the search for a label
scope, the store of captured continuations, and memory. Both machines use these definitions on their own kind
of stack frame.
-/

@[expose] public section

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

/-- The function that destroys what a closure captured, and the captures, if
`a` is a closure of a function that `drops` says has one. -/
def dropOf (drops : List (Nat × Nat)) (ρ : Env) (a : Atom) : Option (Nat × List Value) :=
  match a.eval ρ with
  | some (.clo fn captures) => (drops.lookup fn).map (·, captures)
  | _ => none

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
  /-- Memory by address (`Memory`): a new block of so many bytes at a
  multiple of an alignment, zeroed; its address. -/
  | alloc
  /-- The block that starts at an address, freed. -/
  | free
  /-- The whole number in so many bits at an address (with a sign if the
  width is positive). -/
  | readBits
  /-- A whole number written in so many bits at an address. -/
  | writeBits
  /-- So many bytes copied, as if through a buffer of their own. -/
  | copy
  /-- How many bytes, and at what alignment, a value of the type a pointer
  or reference is to takes: what the typed lowering makes a number. -/
  | sizeOf
  | alignOf
  /-- What a raw pointer points to, as a reference: given the pointer and the
  tag of the pointer type's constructor, for its type. What the typed
  lowering makes the address. -/
  | deref
  /-- Where the program's static block `i` is. -/
  | staticAt
  /-- Where the first element of a `[T; N]` a reference is to is, as a
  `*mut T`: given the reference and the tag of `*mut T`'s constructor. -/
  | addressOf
  /-- `load`, `store`, `swap`, `tag` and `focus` of a reference that is an
  address (a cell of memory, `Tm.cellL`), of a value laid out so (the
  typed lowering's). -/
  | loadL (l : Lay)
  | storeL (l : Lay)
  | swapL (l : Lay)
  | tagL (l : Lay)
  | focusL (l : Lay)
  deriving Hashable, BEq

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
abbrev Cells := Array (Option Value)

/-- Perform an operation on memory by address: its result and the memory
afterwards. -/
def MemOp.evalBytes (m : Memory) : MemOp → List Value → Option (Value × Memory)
  | .staticAt, [.int i] => do pure (.int (← m.statics[i.toNat]?), m)
  | .alloc, [.int size, .int align] =>
    if 0 ≤ size ∧ 0 < align then
      let (addr, m) := m.alloc size.toNat align.toNat
      some (.int addr, m)
    else none
  | .free, [.int addr] => do
    if addr < 0 then none
    pure (.unit, ← m.free addr.toNat)
  | .readBits, [.int addr, .int width] => do
    if addr < 0 then none
    pure (.int (ofBits (← m.read addr.toNat (width.natAbs / 8)) width), m)
  | .writeBits, [.int addr, .int width, .int v] => do
    if addr < 0 then none
    pure (.unit, ← m.write addr.toNat (width.natAbs / 8) (bitsOf v (width.natAbs / 8)))
  | .copy, [.int to, .int src, .int n] => do
    unless 0 ≤ to ∧ 0 ≤ src ∧ 0 ≤ n do none
    pure (.unit, ← m.copy to.toNat src.toNat n.toNat)
  | _, _ => none

/-- The layout a path of field numbers leads to from `addr`, and its address:
through a value of several constructors by the one its tag says. At what the
machine holds, the rest of the path is in the value it holds. -/
partial def Lay.path (m : Memory) (addr : Nat) : Lay → List Value → Option (Nat × Lay × List Value)
  | .held, rest => some (addr, .held, rest)
  | l, [] => some (addr, l, [])
  | .fields _ fs, .int i :: rest => do
    let (at_, l) ← fs[i.toNat]?
    if i < 0 then none
    Lay.path m (addr + at_) l rest
  | .tagged cs, .int i :: rest => do
    let (_, fs) ← cs[← m.read addr 1]?
    let (at_, l) ← fs[i.toNat]?
    if i < 0 then none
    Lay.path m (addr + at_) l rest
  | _, _ => none

/-- Which constructor built what is laid out so at `addr`. -/
def Lay.tagAt (m : Memory) (addr : Nat) : Lay → Option Nat
  | .fields tag _ => some tag
  | .tagged cs => do pure (← cs[← m.read addr 1]?).1
  | _ => none

/-- A memory operation's name, for saying what went wrong. -/
def MemOp.name : MemOp → String
  | .load => "load" | .store => "store" | .swap => "swap" | .tag => "tag" | .focus => "focus"
  | .alloc => "alloc" | .free => "free" | .readBits => "read" | .writeBits => "write"
  | .copy => "copy" | .sizeOf => "size" | .alignOf => "align" | .deref => "deref" | .staticAt => "static" | .addressOf => "address"
  | .loadL l => s!"load as {l.show}" | .storeL l => s!"store as {l.show}"
  | .swapL l => s!"swap as {l.show}" | .tagL l => s!"tag as {l.show}" | .focusL l => s!"focus as {l.show}"

/-- The value the machine holds at `addr` (`Lay.held`), with its id. -/
def heldAt (m : Memory) (held : Held) (addr : Nat) : Option (Nat × Value) := do
  let id ← m.read addr 8
  pure (id, ← held.values[id]?)

/-- Perform a memory operation of a reference that is an address (`loadL` and
the rest), on memory and what is held for it. A reference into a value the
machine holds is the address of its id and a path into it, and what is done
there is done to that value as to a cell's. -/
def MemOp.evalLaid (m : Memory) (held : Held) : MemOp → List Value → Option (Value × Memory × Held)
  | .loadL _, [.ref a _ (s :: p)] => do pure (← (← heldAt m held a).2.part (s :: p), m, held)
  | .storeL _, [.ref a _ (s :: p), w] => do
    let (id, v) ← heldAt m held a
    pure (.unit, m, { held with values := held.values.insert id (← v.putPart (s :: p) w) })
  | .swapL _, [.ref a _ (s :: p), w] => do
    let (id, v) ← heldAt m held a
    pure (← v.part (s :: p), m, { held with values := held.values.insert id (← v.putPart (s :: p) w) })
  | .tagL _, .ref a _ (s :: p) :: path => do
    pure (.int (tagAt (← (← heldAt m held a).2.part (s :: p)) path), m, held)
  | .loadL l, [.ref a _ []] => do pure (← l.read m held a, m, held)
  | .storeL l, [.ref a _ [], w] => do
    let (m, held) ← l.write m held a w
    pure (.unit, m, held)
  | .swapL l, [.ref a _ [], w] => do
    let old ← l.read m held a
    let (m, held) ← l.write m held a w
    pure (old, m, held)
  | .tagL l, .ref a _ [] :: path => do
    match Lay.path m a l path with
    | some (a', .held, rest) => do
      pure (.int (tagAt (← heldAt m held a').2 rest), m, held)
    | some (a', l', _) => pure (.int ((l'.tagAt m a').map Int.ofNat |>.getD (-1)), m, held)
    | none => pure (.int (-1), m, held)
  | .focusL (.fields _ fs), [.ref a b [], .int i, .int (-1)] => do
    let (at_, _) ← fs[i.toNat]?
    if i < 0 then none
    pure (.ref (a + at_) b [], m, held)
  | .focusL (.fields _ fs), [.ref a b [], .int i] => do
    let (at_, _) ← fs[i.toNat]?
    if i < 0 then none
    pure (.ref (a + at_) b [], m, held)
  | .focusL (.tagged cs), [.ref a b [], .int i, .int built] => do
    let fs ← cs.lookup built.toNat
    let (at_, _) ← fs[i.toNat]?
    if i < 0 then none
    pure (.ref (a + at_) b [], m, held)
  | .addressOf, [.ref a _ [], .int c] => if 0 ≤ c then some (.data c.toNat [.int a], m, held) else none
  -- (Into a value the machine holds, or further into one.)
  | .focusL _, [.ref a b p, .int i] =>
    if 0 ≤ i then some (.ref a b (p ++ [⟨none, i.toNat⟩]), m, held) else none
  | .focusL _, [.ref a b p, .int i, .int (-1)] =>
    if 0 ≤ i then some (.ref a b (p ++ [⟨none, i.toNat⟩]), m, held) else none
  | .focusL _, [.ref a b p, .int i, .int built] =>
    if 0 ≤ i ∧ 0 ≤ built then some (.ref a b (p ++ [⟨some built.toNat, i.toNat⟩]), m, held) else none
  | _, _ => none

/-- Perform a memory operation: its result and the memory afterwards. -/
def MemOp.eval (cells : Cells) : MemOp → List Value → Option (Value × Cells)
  | .load, [.ref a _ p] =>
    match cells[a]? with
    | some (some v) => (v.part p).map (·, cells)
    | _ => none
  | .store, [.ref a _ p, w] =>
    match cells[a]? with
    | some (some v) => (v.putPart p w).map fun v' => (.unit, cells.setIfInBounds a (some v'))
    | _ => none
  | .swap, [.ref a _ p, w] =>
    match cells[a]? with
    | some (some v) =>
      match v.part p, v.putPart p w with
      | some old, some v' => some (old, cells.setIfInBounds a (some v'))
      | _, _ => none
    | _ => none
  | .tag, .ref a _ p :: path =>
    match cells[a]? with
    | some (some v) => (v.part p).map fun w => (.int (tagAt w path), cells)
    | _ => none
  | .focus, [.ref a b p, .int i] =>
    if 0 ≤ i then some (.ref a b (p ++ [⟨none, i.toNat⟩]), cells) else none
  -- The field of one of several constructors: the step says which.
  -- (A place in a `[T; N]` found when the program runs: as an array's.)
  | .focus, [.ref a b p, .int i, .int (-1)] =>
    if 0 ≤ i then some (.ref a b (p ++ [⟨none, i.toNat⟩]), cells) else none
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
  /-- Memory by address: what `alloc` makes, and the values held for what
  is not bytes yet (`Lay.held`). -/
  mem : Memory := {}
  held : Held := {}

/-- The store after the scope of cell `a` has ended: the cell is released (a
cell of memory, `Tm.cellL`, has an address from `memBase` on; its block is
freed). -/
def Store.release {φ : Type} (store : Store φ) (a : Nat) : Store φ :=
  let ⟨conts, labels, cells, mem, held⟩ := store
  if memBase ≤ a then
    -- (Whether it can be freed asked first: the memory is then freed in
    -- place, not held for the other answer.)
    if mem.blocks.contains a then ⟨conts, labels, cells, (mem.free a).getD {}, held⟩
    else ⟨conts, labels, cells, mem, held⟩
  else ⟨conts, labels, cells.setIfInBounds a none, mem, held⟩

/-- The store with a new cell holding `v`; its address is the old number of cells. -/
def Store.alloc {φ : Type} (store : Store φ) (v : Value) : Store φ :=
  { store with cells := store.cells.push (some v) }

/-- Perform a memory operation on the store. -/
def Store.memOp {φ : Type} (store : Store φ) (op : MemOp) (vs : List Value) : Option (Value × Store φ) :=
  -- (Each part given to what changes it alone, the store taken apart: held
  -- by the store too, a part would be copied whole by its first change.)
  let ⟨conts, labels, cells, mem, held⟩ := store
  -- Of a cell, or a step into one: the cell's.
  let ofCell := match op, vs with
    | .focus, _ => true
    | .load, .ref a _ _ :: _ | .store, .ref a _ _ :: _ | .swap, .ref a _ _ :: _ | .tag, .ref a _ _ :: _ =>
      decide (a < cells.size)
    | _, _ => false
  let onCell := if ofCell then op.eval cells vs else none
  match onCell with
  | some (r, cells) => some (r, ⟨conts, labels, cells, mem, held⟩)
  | none =>
    match op with
    | .staticAt | .alloc | .free | .readBits | .writeBits | .copy =>
      (op.evalBytes mem vs).map fun (r, mem) => (r, ⟨conts, labels, cells, mem, held⟩)
    | _ =>
      -- (An address seen as a whole number, `transmute`, is the reference.)
      let vs : List Value := match vs with
        | .int a :: rest => if 0 ≤ a then .ref a.toNat 0 [] :: rest else vs
        | _ => vs
      -- Where the program is not laid out, a value in memory is one the
      -- machine holds, in a place of 8 bytes: what a size, an alignment and
      -- a place in memory are then.
      let unlaid : Option MemOp := match op with
        | .load => some (.loadL .held) | .store => some (.storeL .held) | .swap => some (.swapL .held)
        | .tag => some (.tagL .held) | .focus => some (.focusL .held) | _ => none
      match op, vs with
      | .sizeOf, [_] | .alignOf, [_] => some (Value.int 8, ⟨conts, labels, cells, mem, held⟩)
      | .deref, [_, .int at_, _] =>
        if 0 ≤ at_ then some (Value.ref at_.toNat 0 [], ⟨conts, labels, cells, mem, held⟩) else none
      | _, _ =>
        ((unlaid.getD op).evalLaid mem held vs).map fun (r, mem, held) => (r, ⟨conts, labels, cells, mem, held⟩)

/-- The store with a new cell of memory (`Tm.cellL`) holding `v`, laid out so;
its address. -/
def Store.allocLaid {φ : Type} (store : Store φ) (l : Laid) (v : Value) : Option (Nat × Store φ) := do
  let ⟨conts, labels, cells, mem, held⟩ := store
  let (a, mem) := mem.alloc l.size l.align
  let (mem, held) ← l.lay.write mem held a v
  pure (a, ⟨conts, labels, cells, mem, held⟩)

end Glorious
