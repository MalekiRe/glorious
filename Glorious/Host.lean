module

public import Glorious.Value
public import Std.Data.HashMap

/-!
# The host boundary

The finite set of things a program can ask of the outside world. Both machines
call the same `Host.call`, and nothing else touches the world.
-/

@[expose] public section

namespace Glorious

/-- Where memory by address starts: far past any cell's number, which a
reference to a cell holds where one to memory holds an address. -/
def memBase : Nat := 1099511627776

/-- Memory: bytes by address, each byte of a live block there (a new block
is zeroed); and each live block's size, by where it starts. A block's
address is never given again: one freed is gone. -/
structure Memory where
  bytes : Std.HashMap Nat UInt8 := {}
  blocks : Std.HashMap Nat Nat := {}
  /-- Where the next block may start. -/
  next : Nat := memBase
  /-- Where each of the program's static blocks is (`MemOp.staticAt`). -/
  statics : Array Nat := #[]

namespace Memory

/-- The `n` bytes from `at`, little-endian, as a whole number; none if one of
them is in no live block. -/
def read (m : Memory) (addr n : Nat) : Option Nat :=
  (List.range n).foldr (fun i acc => do
    let rest ← acc
    let b ← m.bytes[addr + i]?
    pure (b.toNat + 256 * rest)) (some 0)

/-- The low `n` bytes of `v` written from `at`; none if one of them is in no
live block. -/
def write (m : Memory) (addr n v : Nat) : Option Memory :=
  -- (What is left of `v` past the bytes written, carried: dividing it by
  -- `256 ^ i` at each byte is quadratic in a wide write.)
  let ⟨bytes, blocks, next, statics⟩ := m
  let written := (List.range n).foldlM (fun ((bytes, rest) : Std.HashMap Nat UInt8 × Nat) i =>
    if bytes.contains (addr + i) then some (bytes.insert (addr + i) rest.toUInt8, rest / 256)
    else none) (bytes, v)
  written.map fun (bytes, _) => ⟨bytes, blocks, next, statics⟩

/-- The `n` bytes from `src` put at `to`, as they were before any is put
(the two may overlap); none if one of them is in no live block. A byte at a
time: read as one number, a wide copy is quadratic. -/
def copy (m : Memory) (to src n : Nat) : Option Memory := do
  let bs ← (List.range n).mapM fun i => m.bytes[src + i]?
  let ⟨bytes, blocks, next, statics⟩ := m
  let bytes ← (bs.zipIdx).foldlM (fun bytes (b, i) =>
    if bytes.contains (to + i) then some (bytes.insert (to + i) b) else none) bytes
  pure ⟨bytes, blocks, next, statics⟩

/-- A new block of `size` bytes at a multiple of `align`, zeroed. -/
def alloc (m : Memory) (size align : Nat) : Nat × Memory :=
  -- (Taken apart first: the bytes then change in place, not as a copy.)
  let ⟨bytes, blocks, next, statics⟩ := m
  let align := max align 1
  let addr := (next + align - 1) / align * align
  let bytes := (List.range size).foldl (fun b i => b.insert (addr + i) 0) bytes
  (addr, ⟨bytes, blocks.insert addr size, addr + max size 1, statics⟩)

/-- Memory with the program's static blocks in it, each its bytes. -/
def withStatics (blocks : List (List Nat)) : Memory :=
  blocks.foldl (fun m bs =>
    let (addr, m) := m.alloc bs.length 1
    let m := bs.zipIdx.foldl (fun m (b, i) => (m.write (addr + i) 1 b).getD m) m
    { m with statics := m.statics.push addr }) {}

/-- The block that starts at `addr`, freed; none if no live block starts there. -/
def free (m : Memory) (addr : Nat) : Option Memory := do
  let ⟨bytes, blocks, next, statics⟩ := m
  let size ← blocks[addr]?
  let bytes := (List.range size).foldl (fun b i => b.erase (addr + i)) bytes
  pure ⟨bytes, blocks.erase addr, next, statics⟩

end Memory

/-- A whole number of `bits` (with a sign if positive) as the `|bits| / 8`
bytes it is held in, and back. -/
def bitsOf (v : Int) (n : Nat) : Nat := (v % (2 ^ (8 * n) : Int)).toNat

def ofBits (raw : Nat) (width : Int) : Int :=
  let n := 8 * (width.natAbs / 8)
  if 0 < width ∧ n > 0 ∧ raw ≥ 2 ^ (n - 1) then (raw : Int) - 2 ^ n else raw

/-- The world outside the program: input not yet read, and output written so
far; and cells that more than one holder reaches, by number (`heap`): what
the library's shared values and threads are kept in. -/
structure World where
  input : List Int
  output : List Value
  heap : List (Option Value) := []
  /-- The characters of the line being written (`call` 21), not yet ended. -/
  line : List Int := []
  /-- The program's functions' names, by index (`call` 9). -/
  names : Array String := #[]

/-- What a finished program leaves behind. -/
structure Result where
  value : Value
  world : World

namespace Host

/--
Perform host operation `id`.

* `0`, one argument: write the value; the result is unit.
* `1`, no arguments: read an integer; the result is the pair `(1, n)`, or
  `(0, 0)` when the input is exhausted.
* `6`, one argument: a new shared cell holding the value; the result is its
  number.
* `7`, a cell's number: the value it holds, taken out (the cell is then
  empty); none if it is empty.
* `8`, a cell's number and a value: the value put in it; the result is unit.
* `9`, a value: the pair of the name of the function it is a callable of,
  as an array of its characters' codes (none, of any other value), and the
  value itself, given back.
* `14`, a value: the value as it is (`transmute`: of another type).
* `21`, a character's code: put at the end of the line being written.
* `22`, no arguments: the line being written ended, written as one value
  (`textLineTag`).

Memory by address is the machine's (`MemOp.alloc` and the rest), not the host's.
-/
def call (w : World) (id : Nat) (args : List Value) : Option (Value × World) :=
  if id = 0 then
    match args with
    | [v] => some (.data 0 [], { w with output := w.output ++ [v] })
    | _ => none
  else if id = 1 then
    match args with
    | [] =>
      match w.input with
      | n :: rest => some (.data 0 [.int 1, .int n], { w with input := rest })
      | [] => some (.data 0 [.int 0, .int 0], w)
    | _ => none
  else if id = 6 then
    match args with
    | [v, _] => some (.int w.heap.length, { w with heap := w.heap ++ [some v] })
    | _ => none
  else if id = 7 then
    match args with
    | [.int n, _] =>
      match w.heap[n.toNat]? with
      | some (some v) => if 0 ≤ n then some (v, { w with heap := w.heap.set n.toNat none }) else none
      | _ => none
    | _ => none
  else if id = 8 then
    match args with
    | [.int n, v, _] =>
      if 0 ≤ n ∧ n.toNat < w.heap.length then some (.data 0 [], { w with heap := w.heap.set n.toNat (some v) }) else none
    | _ => none
  else if id = 21 then
    match args with
    | [.int c] => some (.data 0 [], { w with line := w.line ++ [c] })
    | _ => none
  else if id = 22 then
    match args with
    | [] => some (.data 0 [], { w with output := w.output ++ [.data textLineTag (w.line.map Value.int)], line := [] })
    | _ => none
  else if id = 14 then
    -- (`transmute`: the value as it is.)
    match args with
    | [v] => some (v, w)
    | _ => none
  else if id = 9 then
    -- (The character at a place of the name of the function a callable is
    -- of, `-1` past its end; and the callable back.)
    match args with
    | [v, .int i] =>
      let name := match v with
        | .clo f _ => (w.names[f]?).getD ""
        | _ => ""
      let code : Int := if 0 ≤ i then ((name.toList[i.toNat]?).map (·.toNat : Char → Int)).getD (-1) else -1
      some (.data 0 [.int code, v], w)
    | _ => none
  else none

end Host

end Glorious
