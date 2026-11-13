import Glorious.Bytecode.Encode

/-!
# Decoding bytecode

The inverse of `Encode`, and the proof that it is one: decoding an encoded
program gives back the program. The format therefore loses nothing.
-/

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
  | 5 :: bs => do
    let (a, bs) ← atom bs
    let (fn, bs) ← nat bs
    pure (.rebind a fn, bs)
  | _ => none

def pair (bs : Bytes) : Option ((Nat × Nat) × Bytes) := do
  let (a, bs) ← nat bs
  let (b, bs) ← nat bs
  pure ((a, b), bs)

def memOp : Bytes → Option (MemOp × Bytes)
  | 0 :: bs => some (.load, bs)
  | 1 :: bs => some (.store, bs)
  | 2 :: bs => some (.swap, bs)
  | _ => none

def instr : Bytes → Option (Instr × Bytes)
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
    let (op, bs) ← memOp bs
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
  | 19 :: u :: bs => do
    let (r, bs) ← atom bs
    let (thunk, bs) ← atom bs
    let (pre, bs) ← list atom bs
    let (post, bs) ← list atom bs
    if u = 1 then pure (.lend true r thunk pre post, bs)
    else if u = 0 then pure (.lend false r thunk pre post, bs)
    else none
  | _ => none

def code (bs : Bytes) : Option (Code × Bytes) := list instr bs

def fn (bs : Bytes) : Option (Fn × Bytes) := (code bs).map fun (c, rest) => (⟨c⟩, rest)

/-- Decode a whole program; nothing may follow it. -/
def program (bs : Bytes) : Option Program :=
  match list fn bs with
  | some (fns, rest) =>
    match code rest with
    | some (main, []) => some ⟨fns, main⟩
    | _ => none
  | none => none

/-! ## Decoding inverts encoding -/

@[simp] theorem nat_encode (n : Nat) (rest : Bytes) :
    nat (Encode.nat n ++ rest) = some (n, rest) := by
  rw [Encode.nat]
  by_cases h : n < 128
  · simp [h, nat]
  · have ih := nat_encode (n / 128) rest
    have hb : ¬ (n % 128 + 128 < 128) := by omega
    simp only [h, ite_false, List.cons_append, nat, hb, ih]
    congr 2
    omega
termination_by n
decreasing_by omega

@[simp] theorem int_encode (n : Int) (rest : Bytes) :
    int (Encode.int n ++ rest) = some (n, rest) := by
  cases n with
  | ofNat m =>
    have h2 : 2 * m / 2 = m := by omega
    simp [int, Encode.int, h2]
  | negSucc m =>
    have h2 : (2 * m + 1) / 2 = m := by omega
    simp [int, Encode.int, h2]

theorem items_encode {α : Type} {enc : α → Bytes} {dec : Bytes → Option (α × Bytes)}
    (h : ∀ x rest, dec (enc x ++ rest) = some (x, rest)) (xs : List α) (rest : Bytes) :
    items dec xs.length (xs.flatMap enc ++ rest) = some (xs, rest) := by
  induction xs with
  | nil => simp [items]
  | cons x xs ih => simp [items, h, ih]

theorem list_encode {α : Type} {enc : α → Bytes} {dec : Bytes → Option (α × Bytes)}
    (h : ∀ x rest, dec (enc x ++ rest) = some (x, rest)) (xs : List α) (rest : Bytes) :
    list dec (Encode.list enc xs ++ rest) = some (xs, rest) := by
  simp [list, Encode.list, items_encode h]

@[simp] theorem atom_encode (a : Atom) (rest : Bytes) :
    atom (Encode.atom a ++ rest) = some (a, rest) := by
  cases a <;> simp [atom, Encode.atom]

@[simp] theorem atoms_encode (xs : List Atom) (rest : Bytes) :
    list atom (Encode.list Encode.atom xs ++ rest) = some (xs, rest) :=
  list_encode atom_encode xs rest

@[simp] theorem nats_encode (xs : List Nat) (rest : Bytes) :
    list nat (Encode.list Encode.nat xs ++ rest) = some (xs, rest) :=
  list_encode nat_encode xs rest

@[simp] theorem place_encode (pl : Place) (rest : Bytes) :
    place (Encode.place pl ++ rest) = some (pl, rest) := by
  simp [place, Encode.place]

@[simp] theorem prim_encode (p : Prim) (rest : Bytes) :
    prim (Encode.prim p ++ rest) = some (p, rest) := by
  cases p <;> simp [prim, Encode.prim]

@[simp] theorem rhs_encode (r : Rhs) (rest : Bytes) :
    rhs (Encode.rhs r ++ rest) = some (r, rest) := by
  cases r <;> simp [rhs, Encode.rhs]

@[simp] theorem pair_encode (p : Nat × Nat) (rest : Bytes) :
    pair (Encode.pair p ++ rest) = some (p, rest) := by
  simp [pair, Encode.pair]

@[simp] theorem pairs_encode (xs : List (Nat × Nat)) (rest : Bytes) :
    list pair (Encode.list Encode.pair xs ++ rest) = some (xs, rest) :=
  list_encode pair_encode xs rest

@[simp] theorem memOp_encode (op : MemOp) (rest : Bytes) :
    memOp (Encode.memOp op ++ rest) = some (op, rest) := by
  cases op <;> simp [memOp, Encode.memOp]

@[simp] theorem instr_encode (i : Instr) (rest : Bytes) :
    instr (Encode.instr i ++ rest) = some (i, rest) := by
  cases i with
  | lend uniq r thunk pre post => cases uniq <;> simp [instr, Encode.instr]
  | _ => simp [instr, Encode.instr]

@[simp] theorem code_encode (c : Code) (rest : Bytes) :
    code (Encode.code c ++ rest) = some (c, rest) :=
  list_encode instr_encode c rest

theorem fn_encode (f : Fn) (rest : Bytes) :
    fn (Encode.code f.code ++ rest) = some (f, rest) := by
  simp [fn]

/-- **The format is lossless.** Decoding an encoded program gives the program back. -/
theorem program_encode (p : Program) : program (Encode.program p) = some p := by
  have h := list_encode (enc := fun f : Fn => Encode.code f.code) fn_encode p.fns
    (Encode.code p.main)
  have hmain := code_encode p.main []
  simp only [List.append_nil] at hmain
  simp only [program, Encode.program, h, hmain]

end Glorious.Bytecode.Decode
