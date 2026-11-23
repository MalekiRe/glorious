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

/-- Memory: bytes by address, each byte of a live block there (a new block
is zeroed); and each live block's size, by where it starts. A block's
address is never given again: one freed is gone. -/
structure Memory where
  bytes : Std.HashMap Nat UInt8 := {}
  blocks : Std.HashMap Nat Nat := {}
  /-- Where the next block may start. -/
  next : Nat := 4096

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
  (List.range n).foldlM (fun (m : Memory) i =>
    if m.bytes.contains (addr + i) then some { m with bytes := m.bytes.insert (addr + i) (v / 256 ^ i).toUInt8 }
    else none) m

/-- A new block of `size` bytes at a multiple of `align`, zeroed. -/
def alloc (m : Memory) (size align : Nat) : Nat × Memory :=
  let align := max align 1
  let addr := (m.next + align - 1) / align * align
  let bytes := (List.range size).foldl (fun b i => b.insert (addr + i) 0) m.bytes
  (addr, { bytes, blocks := m.blocks.insert addr size, next := addr + max size 1 })

/-- The block that starts at `addr`, freed; none if no live block starts there. -/
def free (m : Memory) (addr : Nat) : Option Memory := do
  let size ← m.blocks[addr]?
  let bytes := (List.range size).foldl (fun b i => b.erase (addr + i)) m.bytes
  pure { m with bytes, blocks := m.blocks.erase addr }

end Memory

/-- A whole number of `bits` (with a sign if positive) as the `|bits| / 8`
bytes it is held in, and back. -/
def bitsOf (v : Int) (n : Nat) : Nat := (v % (2 ^ (8 * n) : Int)).toNat

def ofBits (raw : Nat) (width : Int) : Int :=
  let n := 8 * (width.natAbs / 8)
  if 0 < width ∧ n > 0 ∧ raw ≥ 2 ^ (n - 1) then (raw : Int) - 2 ^ n else raw

/-- The world outside the program: input not yet read, and output written so
far; cells that more than one holder reaches, by number (`heap`): what the
library's shared values and threads are kept in; and memory, by address. -/
structure World where
  input : List Int
  output : List Value
  heap : List (Option Value) := []
  /-- The program's functions' names, by index (`call` 9). -/
  names : Array String := #[]
  mem : Memory := {}

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
* `3`, an address and a width: the whole number in the `|width| / 8` bytes
  there (with a sign if the width is positive); none if a byte is in no
  live block. `4`, an address, a width and a whole number: written there.
* `11`, a size and an alignment: a new block of memory, zeroed; its address.
  `12`, an address: the block that starts there freed. `13`, where to, where
  from and how many: the bytes copied, as if through a buffer of their own.
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
    | [v] => some (.int w.heap.length, { w with heap := w.heap ++ [some v] })
    | _ => none
  else if id = 7 then
    match args with
    | [.int n] =>
      match w.heap[n.toNat]? with
      | some (some v) => if 0 ≤ n then some (v, { w with heap := w.heap.set n.toNat none }) else none
      | _ => none
    | _ => none
  else if id = 8 then
    match args with
    | [.int n, v] =>
      if 0 ≤ n ∧ n.toNat < w.heap.length then some (.data 0 [], { w with heap := w.heap.set n.toNat (some v) }) else none
    | _ => none
  else if id = 3 then
    match args with
    | [.int addr, .int width] => do
      let raw ← w.mem.read addr.toNat (width.natAbs / 8)
      if 0 ≤ addr then some (.int (ofBits raw width), w) else none
    | _ => none
  else if id = 4 then
    match args with
    | [.int addr, .int width, .int v] => do
      let mem ← w.mem.write addr.toNat (width.natAbs / 8) (bitsOf v (width.natAbs / 8))
      if 0 ≤ addr then some (.data 0 [], { w with mem }) else none
    | _ => none
  else if id = 11 then
    match args with
    | [.int size, .int align] =>
      if 0 ≤ size ∧ 0 < align then
        let (addr, mem) := w.mem.alloc size.toNat align.toNat
        some (.int addr, { w with mem })
      else none
    | _ => none
  else if id = 12 then
    match args with
    | [.int addr] => do
      let mem ← w.mem.free addr.toNat
      if 0 ≤ addr then some (.data 0 [], { w with mem }) else none
    | _ => none
  else if id = 13 then
    match args with
    | [.int to, .int src, .int n] => do
      unless 0 ≤ to ∧ 0 ≤ src ∧ 0 ≤ n do none
      let raw ← w.mem.read src.toNat n.toNat
      let mem ← w.mem.write to.toNat n.toNat raw
      some (.data 0 [], { w with mem })
    | _ => none
  else if id = 14 then
    -- (`transmute`: the value as it is.)
    match args with
    | [v] => some (v, w)
    | _ => none
  else if id = 9 then
    match args with
    | [v] =>
      let name := match v with
        | .clo f _ => (w.names[f]?).getD ""
        | _ => ""
      let codes := name.toList.map fun c => Value.int c.toNat
      some (.data 0 [.data (arrayBase + codes.length) codes, v], w)
    | _ => none
  else none

/-%proof (commented out while the machines become bytes)
/-- A host operation never retracts output. -/
theorem call_output {w w' : World} {id : Nat} {args : List Value} {r : Value}
    (h : call w id args = some (r, w')) : w.output <+: w'.output := by
  unfold call at h
  repeat' split at h
  all_goals (simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h)
  all_goals (try obtain ⟨_, rfl⟩ := h)
  all_goals (first | exact List.prefix_append _ _ | exact List.prefix_refl _ | simp_all)
%proof-/

end Host

end Glorious
