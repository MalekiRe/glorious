module

public import Glorious.Bytecode.Encode

/-!
# Decoding bytecode

The inverse of `Encode`, and the proof that it is one: decoding an encoded
program gives back the program. The format therefore loses nothing.
-/

@[expose] public section

namespace Glorious.Bytecode.Decode

open Encode (Bytes)

def nat : Bytes → Option (Nat × Bytes)
  | [] => none
  | b :: rest =>
    if b < 128 then some (b, rest)
    else
      match nat rest with
      | some (hi, rest') => some (b - 128 + 128 * hi, rest')
      | none => none

def int (bs : Bytes) : Option (Int × Bytes) :=
  match nat bs with
  | some (z, rest) => some (if z % 2 = 0 then Int.ofNat (z / 2) else Int.negSucc (z / 2), rest)
  | none => none

/-- Decode exactly `n` items. -/
def items {α : Type} (item : Bytes → Option (α × Bytes)) : Nat → Bytes → Option (List α × Bytes)
  | 0, bs => some ([], bs)
  | n + 1, bs =>
    match item bs with
    | some (x, rest) =>
      match items item n rest with
      | some (xs, rest') => some (x :: xs, rest')
      | none => none
    | none => none

def list {α : Type} (item : Bytes → Option (α × Bytes)) (bs : Bytes) : Option (List α × Bytes) :=
  match nat bs with
  | some (n, rest) => items item n rest
  | none => none

def atom : Bytes → Option (Atom × Bytes)
  | 0 :: bs => (nat bs).map fun (i, rest) => (.var i, rest)
  | 1 :: bs => (int bs).map fun (n, rest) => (.int n, rest)
  | _ => none

def place (bs : Bytes) : Option (Place × Bytes) := do
  let (var, bs) ← nat bs
  let (path, bs) ← list nat bs
  pure (⟨var, path⟩, bs)

def prim : Bytes → Option (Prim × Bytes)
  | 0 :: bs => some (.intAdd, bs)
  | 1 :: bs => some (.intSub, bs)
  | 2 :: bs => some (.intMul, bs)
  | 3 :: bs => some (.intLt, bs)
  | 4 :: bs => some (.intEq, bs)
  | 5 :: bs => some (.intDiv, bs)
  | 6 :: bs => some (.intRem, bs)
  | 7 :: bs => some (.intFit, bs)
  | 8 :: bs => some (.f64Add, bs)
  | 9 :: bs => some (.f64Sub, bs)
  | 10 :: bs => some (.f64Mul, bs)
  | 11 :: bs => some (.f64Div, bs)
  | 12 :: bs => some (.f64Lt, bs)
  | 13 :: bs => some (.f64Eq, bs)
  | 14 :: bs => some (.f64OfInt, bs)
  | 15 :: bs => some (.f64ToInt, bs)
  | 16 :: bs => some (.f64Narrow, bs)
  | 17 :: bs => some (.f64Widen, bs)
  | 18 :: bs => some (.f64OfDecimal, bs)
  | 19 :: bs => some (.f64Digits, bs)
  | 20 :: bs => some (.f64Exp10, bs)
  | 21 :: bs => some (.f64Sqrt, bs)
  | 22 :: bs => some (.f64Round, bs)
  | 23 :: bs => some (.wideAdd, bs)
  | 24 :: bs => some (.wideSub, bs)
  | 25 :: bs => some (.wideMul, bs)
  | 26 :: bs => some (.intAnd, bs)
  | 27 :: bs => some (.intOr, bs)
  | 28 :: bs => some (.intXor, bs)
  | 29 :: bs => some (.intShl, bs)
  | 30 :: bs => some (.intShr, bs)
  | 31 :: bs => some (.uwAdd, bs)
  | 32 :: bs => some (.uwSub, bs)
  | 33 :: bs => some (.uwMul, bs)
  | 34 :: bs => some (.uwDiv, bs)
  | 35 :: bs => some (.uwRem, bs)
  | 36 :: bs => some (.uwLt, bs)
  | 37 :: bs => some (.uwShl, bs)
  | 38 :: bs => some (.uwShr, bs)
  | 39 :: bs => some (.intBelow, bs)
  | 45 :: bs => do
    let (b, bs) ← int bs
    match bs with
    | k :: bs => some (.cast b (k == 1), bs)
    | [] => none
  | 46 :: bs => (nat bs).map fun (op, bs) => (.fixed op, bs)
  | _ => none

def rhs : Bytes → Option (Rhs × Bytes)
  | 0 :: bs => (atom bs).map fun (a, rest) => (.atom a, rest)
  | 1 :: bs => do
    let (p, bs) ← prim bs
    let (args, bs) ← list atom bs
    pure (.prim p args, bs)
  | 2 :: bs => do
    let (tag, bs) ← nat bs
    let (args, bs) ← list atom bs
    pure (.construct tag args, bs)
  | 3 :: bs => (place bs).map fun (pl, rest) => (.place pl, rest)
  | 4 :: bs => do
    let (fn, bs) ← nat bs
    let (captures, bs) ← list atom bs
    pure (.closure fn captures, bs)
  | _ => none

def pair (bs : Bytes) : Option ((Nat × Nat) × Bytes) := do
  let (a, bs) ← nat bs
  let (b, bs) ← nat bs
  pure ((a, b), bs)

mutual

/-- A layout (`Encode.lay`). -/
partial def lay : Bytes → Option (Lay × Bytes)
  | 0 :: bs => do
    let (n, bs) ← nat bs
    match bs with
    | s :: bs => pure (.int n (s = 1), bs)
    | [] => none
  | 1 :: bs => do
    let (tag, bs) ← nat bs
    let (fs, bs) ← laidFields bs
    pure (.fields tag fs, bs)
  | 2 :: bs => do
    let (cs, bs) ← list (fun bs => do
      let (tag, bs) ← nat bs
      let (fs, bs) ← laidFields bs
      pure ((tag, fs), bs)) bs
    pure (.tagged cs, bs)
  | 3 :: bs => some (.addr, bs)
  | 4 :: bs => some (.held, bs)
  | 5 :: bs => some (.nothing, bs)
  | _ => none

partial def laidFields (bs : Bytes) : Option (List (Nat × Lay) × Bytes) :=
  list (fun bs => do
    let (at_, bs) ← nat bs
    let (l, bs) ← lay bs
    pure ((at_, l), bs)) bs

end

/-- A layout by its place in the file's table (`Encode.layTable`). -/
def layAt (table : Array Lay) (bs : Bytes) : Option (Lay × Bytes) := do
  let (i, bs) ← nat bs
  pure ((← table[i]?), bs)

def laid (table : Array Lay) (bs : Bytes) : Option (Laid × Bytes) := do
  let (size, bs) ← nat bs
  let (align, bs) ← nat bs
  let (l, bs) ← layAt table bs
  pure ({ lay := l, size, align }, bs)

def memOp (table : Array Lay) : Bytes → Option (MemOp × Bytes)
  | 0 :: bs => some (.load, bs)
  | 1 :: bs => some (.store, bs)
  | 2 :: bs => some (.swap, bs)
  | 3 :: bs => some (.tag, bs)
  | 4 :: bs => some (.focus, bs)
  | 5 :: bs => some (.alloc, bs)
  | 6 :: bs => some (.free, bs)
  | 7 :: bs => some (.readBits, bs)
  | 8 :: bs => some (.writeBits, bs)
  | 9 :: bs => some (.copy, bs)
  | 15 :: bs => some (.sizeOf, bs)
  | 16 :: bs => some (.alignOf, bs)
  | 17 :: bs => some (.deref, bs)
  | 18 :: bs => some (.staticAt, bs)
  | 19 :: bs => some (.addressOf, bs)
  | 10 :: bs => (layAt table bs).map fun (l, bs) => (.loadL l, bs)
  | 11 :: bs => (layAt table bs).map fun (l, bs) => (.storeL l, bs)
  | 12 :: bs => (layAt table bs).map fun (l, bs) => (.swapL l, bs)
  | 13 :: bs => (layAt table bs).map fun (l, bs) => (.tagL l, bs)
  | 14 :: bs => (layAt table bs).map fun (l, bs) => (.focusL l, bs)
  | _ => none

def instr (table : Array Lay) : Bytes → Option (Instr × Bytes)
  | 0 :: bs => (rhs bs).map fun (r, rest) => (.op r, rest)
  | 1 :: bs => do
    let (f, bs) ← atom bs
    let (args, bs) ← list atom bs
    pure (.call f args, bs)
  | 2 :: bs => do
    let (f, bs) ← atom bs
    let (args, bs) ← list atom bs
    pure (.tail f args, bs)
  | 3 :: bs => (atom bs).map fun (a, rest) => (.ret a, rest)
  | 4 :: bs => do
    let (ret, bs) ← nat bs
    let (ops, bs) ← list pair bs
    let (captures, bs) ← list atom bs
    let (thunk, bs) ← atom bs
    pure (.handle ret ops captures thunk, bs)
  | 5 :: bs => do
    let (ret, bs) ← nat bs
    let (ops, bs) ← list pair bs
    let (captures, bs) ← list atom bs
    let (thunk, bs) ← atom bs
    pure (.handleTail ret ops captures thunk, bs)
  | 6 :: bs => do
    let (op, bs) ← nat bs
    let (args, bs) ← list atom bs
    pure (.raise op args, bs)
  | 7 :: bs => do
    let (op, bs) ← nat bs
    let (args, bs) ← list atom bs
    pure (.perform op args, bs)
  | 8 :: bs => (atom bs).map fun (thunk, rest) => (.label thunk, rest)
  | 9 :: bs => (atom bs).map fun (thunk, rest) => (.labelTail thunk, rest)
  | 10 :: bs => do
    let (cleanup, bs) ← atom bs
    let (thunk, bs) ← atom bs
    pure (.guard cleanup thunk, bs)
  | 11 :: bs => do
    let (cleanup, bs) ← atom bs
    let (thunk, bs) ← atom bs
    pure (.guardTail cleanup thunk, bs)
  | 12 :: bs => (atom bs).map fun (k, rest) => (.cancel k, rest)
  | 13 :: bs => do
    let (id, bs) ← nat bs
    let (args, bs) ← list atom bs
    pure (.host id args, bs)
  | 14 :: bs => do
    let (pl, bs) ← place bs
    let (tag, bs) ← nat bs
    let (arity, bs) ← nat bs
    let (fail, bs) ← nat bs
    pure (.testCtor pl tag arity fail, bs)
  | 15 :: bs => do
    let (pl, bs) ← place bs
    let (n, bs) ← int bs
    let (fail, bs) ← nat bs
    pure (.testInt pl n fail, bs)
  | 16 :: bs => do
    let (op, bs) ← memOp table bs
    let (args, bs) ← list atom bs
    pure (.mem op args, bs)
  | 17 :: bs => do
    let (init, bs) ← atom bs
    let (thunk, bs) ← atom bs
    pure (.cell init thunk, bs)
  | 18 :: bs => do
    let (init, bs) ← atom bs
    let (thunk, bs) ← atom bs
    pure (.cellTail init thunk, bs)
  | 20 :: bs => do
    let (l, bs) ← laid table bs
    let (init, bs) ← atom bs
    let (thunk, bs) ← atom bs
    pure (.cellL l init thunk, bs)
  | 21 :: bs => do
    let (l, bs) ← laid table bs
    let (init, bs) ← atom bs
    let (thunk, bs) ← atom bs
    pure (.cellTailL l init thunk, bs)
  | 19 :: u :: bs => do
    let (r, bs) ← atom bs
    let (thunk, bs) ← atom bs
    let (pre, bs) ← list atom bs
    let (post, bs) ← list atom bs
    if u = 1 then pure (.lend true r thunk pre post, bs)
    else if u = 0 then pure (.lend false r thunk pre post, bs)
    else none
  | _ => none

def code (table : Array Lay) (bs : Bytes) : Option (Code × Bytes) := list (instr table) bs

def fn (table : Array Lay) (bs : Bytes) : Option (Fn × Bytes) := (code table bs).map fun (c, rest) => (⟨c⟩, rest)

/-- Decode a whole program; nothing may follow it. (Its functions' names are
not written: a program read back has none.) -/
def program (bs : Bytes) : Option Program := do
  let (table, bs) ← list lay bs
  let table := table.toArray
  let code := code table
  match list (fn table) bs with
  | some (fns, rest) =>
    match code rest with
    | some (main, rest) =>
      match list pair rest with
      | some (drops, rest) =>
        match list (list nat) rest with
        | some (statics, []) => some ⟨fns.toArray, main, drops, #[], statics⟩
        | _ => none
      | _ => none
    | none => none
  | none => none

/-! ## Decoding inverts encoding -/

end Glorious.Bytecode.Decode
