module

public import Glorious.Host

/-!
# How a value is laid out in memory

What the machines read and write where a cell is: a value's bytes, laid out
as Rust lays out a type (each field at its alignment, in order; a type of
several constructors a tag byte first, then the one it is's fields), and
read back. A value that is not bytes yet (a callable, a resumption, a label,
an array, a value of a type that holds itself) is held by the machine, and
memory has an id for it: what replaces that is the next stage's
(`docs/decisions.md`, "A systems language").
-/

@[expose] public section

namespace Glorious

/-- How a value of some type is laid out. -/
inductive Lay where
  /-- A whole number in so many bytes, with a sign or without. -/
  | int (bytes : Nat) (signed : Bool)
  /-- The fields of a constructor that is its type's only one, or of a tuple
  (`tag` 0), each at its offset. -/
  | fields (tag : Nat) (at_ : List (Nat × Lay))
  /-- One of several constructors: a tag byte at 0, then the one it is's
  fields, each at its offset. -/
  | tagged (ctors : List (Nat × List (Nat × Lay)))
  /-- An address: a reference. -/
  | addr
  /-- What is not bytes yet, held by the machine: an id for it. -/
  | held
  /-- Nothing: a type with no values. -/
  | nothing
  deriving Inhabited, BEq, Hashable

/-- A layout written out, for saying what went wrong. -/
partial def Lay.show : Lay → String
  | .int n s => s!"{if s then "i" else "u"}{8 * n}"
  | .fields tag fs => s!"#{tag}(" ++ ", ".intercalate (fs.map fun (o, l) => s!"{o}:{l.show}") ++ ")"
  | .tagged cs => "<" ++ " | ".intercalate (cs.map fun (t, fs) => (Lay.fields t fs).show) ++ ">"
  | .addr => "&"
  | .held => "held"
  | .nothing => "!"

/-- A layout, with the size and alignment it has. -/
structure Laid where
  lay : Lay
  size : Nat
  align : Nat
  deriving Inhabited, BEq, Hashable

/-- Where the next field goes after `size` bytes, at alignment `align`. -/
def alignUp (size align : Nat) : Nat := (size + align - 1) / max align 1 * max align 1

/-- Fields one after another, from `start`: each at its offset, and the size
and alignment of all of them. -/
def placeFields (start : Nat) (fs : List Laid) : List (Nat × Lay) × Nat × Nat :=
  fs.foldl (fun (out, size, align) f =>
    let at_ := alignUp size f.align
    (out ++ [(at_, f.lay)], at_ + f.size, max align f.align)) ([], start, 1)

/-- Values held by the machine where memory has an id for them. -/
structure Held where
  values : Std.HashMap Nat Value := {}
  next : Nat := 1
  deriving Inhabited

/-- What marks a reference written in memory as one that is held (`Lay.write`). -/
def heldRefBit : Nat := 9223372036854775808

namespace Lay

/-- The value written at `addr` in `mem`, with what is held for it; none if
a byte is in no live block, or the value is not of the layout. -/
partial def write (mem : Memory) (held : Held) (addr : Nat) : Lay → Value → Option (Memory × Held)
  | .int n _, .int v => do pure (← mem.write addr n (bitsOf v n), held)
  -- (A reference seen as a whole number, `transmute`: its address.)
  | .int n _, .ref a _ [] => do pure (← mem.write addr n a, held)
  | .fields _ fs, .data _ vs => writeAll mem held addr fs vs
  | .tagged cs, .data tag vs => do
    let fs ← cs.lookup tag
    let i := (cs.map (·.1)).idxOf tag
    let mem ← mem.write addr 1 i
    writeAll mem held addr fs vs
  | .addr, .ref a _ [] => do pure (← mem.write addr 8 a, held)
  -- (A reference into a value the machine holds is not an address alone:
  -- it is held, and its id written with the top bit set.)
  | .addr, v@(.ref _ _ (_ :: _)) => do
    let mem ← mem.write addr 8 (heldRefBit + held.next)
    pure (mem, { values := held.values.insert held.next v, next := held.next + 1 })
  | .held, v => do
    let mem ← mem.write addr 8 held.next
    pure (mem, { values := held.values.insert held.next v, next := held.next + 1 })
  | .nothing, _ => some (mem, held)
  | _, _ => none
where
  writeAll (mem : Memory) (held : Held) (addr : Nat) : List (Nat × Lay) → List Value → Option (Memory × Held)
    | [], [] => some (mem, held)
    | (at_, l) :: fs, v :: vs => do
      let (mem, held) ← write mem held (addr + at_) l v
      writeAll mem held addr fs vs
    | _, _ => none

/-- The value at `addr`; none if a byte is in no live block or holds what no
value of the layout is. `ctors` is what a constructor is told by: for a
reference, the borrow it is given. -/
partial def read (mem : Memory) (held : Held) (addr : Nat) : Lay → Option Value
  | .int n signed => do
    let raw ← mem.read addr n
    pure (.int (ofBits raw (if signed then (8 * n : Nat) else -(8 * n : Nat))))
  | .fields tag fs => do pure (.data tag (← fs.mapM fun (at_, l) => read mem held (addr + at_) l))
  | .tagged cs => do
    let i ← mem.read addr 1
    let (tag, fs) ← cs[i]?
    pure (.data tag (← fs.mapM fun (at_, l) => read mem held (addr + at_) l))
  | .addr => do
    let a ← mem.read addr 8
    if heldRefBit ≤ a then held.values[a - heldRefBit]? else pure (.ref a 0 [])
  | .held => do held.values[← mem.read addr 8]?
  | .nothing => none

end Lay

end Glorious
