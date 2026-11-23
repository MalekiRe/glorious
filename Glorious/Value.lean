module

public import Glorious.Float

/-!
# Runtime values and operands

Core and bytecode share one notion of runtime value and one notion of operand.
An activation's environment only grows, so an operand names a local by its
position in that environment.
-/

@[expose] public section

namespace Glorious

/-- A step from a value to one of its fields: the field's number, and the
constructor the value has to have been built by for the field to be the one
meant, where a type has several. -/
structure PathStep where
  tag : Option Nat
  field : Nat

/-- Does a value built by constructor `built` have the field a step means? -/
def PathStep.fits (s : PathStep) (built : Nat) : Bool :=
  match s.tag with
  | none => true
  | some t => t == built

/-- A runtime value. -/
inductive Value where
  /-- An integer. Arithmetic keeps it within 64 bits; see `checked`. -/
  | int (n : Int)
  /-- A `struct` or `enum` value: a constructor tag and its fields. -/
  | data (tag : Nat) (fields : List Value)
  /-- A callable: the index of its function and the values it captured. -/
  | clo (fn : Nat) (captures : List Value)
  /-- A resumption: the identity of a captured continuation. -/
  | cont (id : Nat)
  /-- A label: the identity of a label scope. -/
  | label (id : Nat)
  /-- A reference: the address of a memory cell, which borrow of the cell it
  is, and the way from what the cell holds to the part of it the reference is
  to: the steps to take, none for the whole. The cell's own reference
  is borrow zero. Nothing the machine does depends on the borrow: it is there
  so that what it means for a borrow to be respected can be said. -/
  | ref (addr : Nat) (borrow : Nat) (path : List PathStep)

/-- The constructors that build arrays: the one that takes `n` elements is
`arrayBase + n`, above every constructor a program declares. And the name
kept for the type of arrays. -/
def arrayBase : Nat := 4611686018427387904

theorem arrayBase_pos : 0 < arrayBase := by decide

-- Nothing is to count down from it.
attribute [irreducible] arrayBase

def arrayName : Nat := 4611686018427387904

/-- The locals of one activation, oldest first. -/
abbrev Env := List Value

/-- An operand: something that is already a value once locals are looked up. -/
inductive Atom where
  /-- The local at position `i` of the current environment. -/
  | var (i : Nat)
  | int (n : Int)
  deriving Hashable

/-- A field path into a local: `var.path₀.path₁...`. -/
structure Place where
  var : Nat
  path : List Nat
  deriving Hashable

/-- Machine intrinsics. Their meaning is shared by both machines. -/
inductive Prim where
  | intAdd
  | intSub
  | intMul
  /-- `1` if the first integer is smaller, else `0`. -/
  | intLt
  /-- `1` if the integers are equal, else `0`. -/
  | intEq
  /-- The quotient, towards zero. No meaning if the divisor is zero. -/
  | intDiv
  /-- What is left of that division. No meaning if the divisor is zero. -/
  | intRem
  /-- The first integer, if it fits in the width the second says: so many
  bits with a sign if positive, without one if negative. Else no meaning. -/
  | intFit
  /-- Floating point: an integer is the bits of a 64-bit IEEE 754 number, and
  the result of each is the true result rounded to nearest, ties to even. -/
  | f64Add
  | f64Sub
  | f64Mul
  | f64Div
  /-- `1` if the first number is smaller, else `0`; `0` if either is a NaN. -/
  | f64Lt
  /-- `1` if the numbers are equal, else `0`; `0` if either is a NaN. -/
  | f64Eq
  /-- The number nearest the first integer. The second is not read. -/
  | f64OfInt
  /-- The number without what is after its point. No meaning for infinity, a
  NaN, or what does not fit. The second is not read. -/
  | f64ToInt
  /-- The bits of the 32-bit number nearest. The second is not read. -/
  | f64Narrow
  /-- The 64-bit number a 32-bit one is. The second is not read. -/
  | f64Widen
  /-- The number nearest the first integer times ten to the second. -/
  | f64OfDecimal
  /-- The number to as many digits as the second integer says, 1 to 17: the
  digits as an integer, without the sign. No meaning for infinity or a NaN. -/
  | f64Digits
  /-- With `f64Digits`: the power of ten its digits are to be multiplied by. -/
  | f64Exp10
  /-- The square root. The second is not read. -/
  | f64Sqrt
  /-- The number without what is after its point, the way the second integer
  says: 0 down, 1 up, 2 towards zero, 3 to the nearest. -/
  | f64Round
  /-- Arithmetic kept within 128 bits rather than 64. -/
  | wideAdd
  | wideSub
  | wideMul
  /-- Bit by bit, on the two's complement of the integers. -/
  | intAnd
  | intOr
  | intXor
  /-- The first integer with its bits moved up by the second, from 0 to 127;
  no meaning if the result does not fit in 128 bits. -/
  | intShl
  /-- The first integer with its bits moved down by the second, its sign kept. -/
  | intShr
  /-- Arithmetic on integers read as 128 bits without a sign. A result that
  does not fit, or would be below zero, has no meaning. -/
  | uwAdd
  | uwSub
  | uwMul
  | uwDiv
  | uwRem
  /-- `1` if the first is smaller, read so, else `0`. -/
  | uwLt
  | uwShl
  | uwShr
  /-- The first integer, if it is at least zero and below the second: a place
  in something of that many places. Else no meaning. -/
  | intBelow
  /-- Arrays. A value made of fields, however many, is read and changed at a
  place given by an integer: the field at a place; the value with another
  field there; how many fields; the value with one more field after the
  last, built by the next constructor; and the value without its last, built
  by the one before, paired with the last. None has a meaning at a place
  that is not there, or of a value that is not made of fields. -/
  | arrGet
  | arrSet
  | arrLen
  | arrPush
  | arrPop
  deriving Hashable

/-- A computation that produces a value without transferring control. -/
inductive Rhs where
  | atom (a : Atom)
  | prim (p : Prim) (args : List Atom)
  | construct (tag : Nat) (args : List Atom)
  /-- Read a field path out of a local. -/
  | place (pl : Place)
  | closure (fn : Nat) (captures : List Atom)
  /-- What a closure captured, under the code of another function: the closure
  `a` is given up and `fn` runs in its place. -/
  | rebind (a : Atom) (fn : Nat)
  deriving Hashable

namespace Value

/-- The unit value: the empty tuple. -/
def unit : Value := .data 0 []

/-- Follow a field path into a value. -/
def follow : Value → List Nat → Option Value
  | v, [] => some v
  | .data _ fields, i :: path =>
    match fields[i]? with
    | some field => field.follow path
    | none => none
  | .int _, _ :: _ => none
  | .clo _ _, _ :: _ => none
  | .cont _, _ :: _ => none
  | .label _, _ :: _ => none
  | .ref _ _ _, _ :: _ => none

/-- The part of a value that steps lead to. There is none where a field is
not there, or where the value was built by another constructor than a step
expects. -/
def part : Value → List PathStep → Option Value
  | v, [] => some v
  | .data tag fields, s :: path =>
    match s.fits tag, fields[s.field]? with
    | true, some field => field.part path
    | _, _ => none
  | .int _, _ :: _ => none
  | .clo _ _, _ :: _ => none
  | .cont _, _ :: _ => none
  | .label _, _ :: _ => none
  | .ref _ _ _, _ :: _ => none

/-- A value with the part that steps lead to replaced. -/
def putPart : Value → List PathStep → Value → Option Value
  | _, [], w => some w
  | .data tag fields, s :: path, w =>
    match s.fits tag, fields[s.field]? with
    | true, some field =>
      match field.putPart path w with
      | some field' => some (.data tag (fields.set s.field field'))
      | none => none
    | _, _ => none
  | .int _, _ :: _, _ => none
  | .clo _ _, _ :: _, _ => none
  | .cont _, _ :: _, _ => none
  | .label _, _ :: _, _ => none
  | .ref _ _ _, _ :: _, _ => none

/-- A step with no constructor in mind fits any. -/
@[simp] theorem _root_.Glorious.PathStep.fits_none (i built : Nat) : (PathStep.mk none i).fits built = true := rfl

/-- A step with a constructor in mind fits that one. -/
theorem _root_.Glorious.PathStep.fits_some {tag i built : Nat} :
    (PathStep.mk (some tag) i).fits built = true ↔ tag = built := by
  simp [PathStep.fits]

/-- What it is for a step and then more to lead somewhere. -/
theorem part_cons {v : Value} {s : PathStep} {path : List PathStep} {w : Value}
    (h : v.part (s :: path) = some w) :
    ∃ tag fields x, v = .data tag fields ∧ s.fits tag = true ∧ fields[s.field]? = some x ∧
      x.part path = some w := by
  cases v with
  | data tag fields =>
    simp only [part] at h
    cases hfit : s.fits tag with
    | false => simp [hfit] at h
    | true =>
      cases hx : fields[s.field]? with
      | none => simp [hfit, hx] at h
      | some x =>
        simp only [hfit, hx] at h
        exact ⟨tag, fields, x, rfl, hfit, hx, h⟩
  | int _ | clo _ _ | cont _ | label _ | ref _ _ _ => simp [part] at h

theorem part_data {tag : Nat} {fields : List Value} {s : PathStep} {x : Value} (path : List PathStep)
    (hfit : s.fits tag = true) (hx : fields[s.field]? = some x) :
    (Value.data tag fields).part (s :: path) = x.part path := by
  simp [part, hfit, hx]

theorem putPart_data {tag : Nat} {fields : List Value} {s : PathStep} {x : Value} (path : List PathStep)
    (w : Value) (hfit : s.fits tag = true) (hx : fields[s.field]? = some x) :
    (Value.data tag fields).putPart (s :: path) w
      = (x.putPart path w).map fun x' => .data tag (fields.set s.field x') := by
  simp only [putPart, hfit, hx]
  cases x.putPart path w <;> rfl

/-- What it is for a part a step and then more leads to, to have been replaced. -/
theorem putPart_cons {v : Value} {s : PathStep} {path : List PathStep} {w v' : Value}
    (h : v.putPart (s :: path) w = some v') :
    ∃ tag fields x x', v = .data tag fields ∧ s.fits tag = true ∧ fields[s.field]? = some x ∧
      x.putPart path w = some x' ∧ v' = .data tag (fields.set s.field x') := by
  cases v with
  | data tag fields =>
    cases hfit : s.fits tag with
    | false => simp [putPart, hfit] at h
    | true =>
      cases hx : fields[s.field]? with
      | none => simp [putPart, hfit, hx] at h
      | some x =>
        rw [putPart_data path w hfit hx] at h
        cases hx' : x.putPart path w with
        | none => simp [hx'] at h
        | some x' =>
          simp only [hx', Option.map_some, Option.some.injEq] at h
          exact ⟨tag, fields, x, x', rfl, hfit, hx, hx', h.symm⟩
  | int _ | clo _ _ | cont _ | label _ | ref _ _ _ => simp [putPart] at h

/-- A part that is there can be replaced. -/
theorem putPart_of_part : ∀ {path : List PathStep} {v old : Value} (w : Value),
    v.part path = some old → ∃ v', v.putPart path w = some v'
  | [], _, _, w, _ => ⟨w, by simp [putPart]⟩
  | s :: path, v, _, w, h => by
    obtain ⟨tag, fields, x, rfl, hfit, hx, hp⟩ := part_cons h
    obtain ⟨x', hx'⟩ := putPart_of_part (path := path) w hp
    exact ⟨_, by rw [putPart_data path w hfit hx, hx']; rfl⟩

/-- A part that is not there cannot be. -/
theorem putPart_none_of_part : ∀ {path : List PathStep} {v : Value} (w : Value),
    v.part path = none → v.putPart path w = none
  | [], _, _, h => by simp [part] at h
  | s :: path, v, w, h => by
    cases hp : v.putPart (s :: path) w with
    | none => rfl
    | some v' =>
      obtain ⟨tag, fields, x, x', rfl, hfit, hx, hx', _⟩ := putPart_cons hp
      rw [part_data path hfit hx] at h
      rw [putPart_none_of_part (path := path) w h] at hx'
      cases hx'

/-- Is this value built by constructor `tag` with exactly `arity` fields? -/
def isCtor (v : Value) (tag arity : Nat) : Bool :=
  match v with
  | .data t fields => tag == t && arity == fields.length
  | .int _ => false
  | .clo _ _ => false
  | .cont _ => false
  | .label _ => false
  | .ref _ _ _ => false

/-- Is this value the integer `n`? -/
def isInt (v : Value) (n : Int) : Bool :=
  match v with
  | .int m => n == m
  | .data _ _ => false
  | .clo _ _ => false
  | .cont _ => false
  | .label _ => false
  | .ref _ _ _ => false

end Value

namespace Place

def eval (ρ : Env) (pl : Place) : Option Value :=
  match ρ[pl.var]? with
  | some v => v.follow pl.path
  | none => none

/-- The place of field `i` of this place. -/
def child (pl : Place) (i : Nat) : Place := ⟨pl.var, pl.path ++ [i]⟩

end Place

/-- Integers are 64-bit and arithmetic is checked: a result outside this range
has no meaning. -/
def checked (n : Int) : Option Value :=
  if -9223372036854775808 ≤ n ∧ n ≤ 9223372036854775807 then some (.int n) else none

/-- An integer within 128 bits. What holds an integer on either machine holds
this much; `checked` is what the integers of `Int` are kept to. -/
def checkedWide (n : Int) : Option Value :=
  if -170141183460469231731687303715884105728 ≤ n ∧ n ≤ 170141183460469231731687303715884105727
  then some (.int n) else none

/-- The 128 bits of an integer, read without a sign. -/
def unsigned (a : Int) : Nat := (a % 340282366920938463463374607431768211456).toNat

/-- The integer whose 128 bits these are, if they fit in 128. -/
def ofUnsigned (n : Nat) : Option Value :=
  if n < 170141183460469231731687303715884105728 then some (.int n)
  else if n < 340282366920938463463374607431768211456 then
    some (.int ((n : Int) - 340282366920938463463374607431768211456))
  else none

/-- Does an integer fit in a width: so many bits with a sign if the width is
positive, without one if it is negative? -/
def fits (a width : Int) : Bool :=
  if width > 0 then -(2 ^ (width.toNat - 1) : Int) ≤ a && a < 2 ^ (width.toNat - 1)
  else if width < 0 then 0 ≤ a && a < 2 ^ (-width).toNat
  else false

/-- An integer that may have no meaning, as a value. -/
def checkedOpt : Option Int → Option Value
  | some n => checked n
  | none => none

def Prim.eval : Prim → List Value → Option Value
  | .intAdd, [.int a, .int b] => checked (a + b)
  | .intSub, [.int a, .int b] => checked (a - b)
  | .intMul, [.int a, .int b] => checked (a * b)
  | .intLt, [.int a, .int b] => some (.int (if a < b then 1 else 0))
  | .intEq, [.int a, .int b] => some (.int (if a = b then 1 else 0))
  | .intDiv, [.int a, .int b] => if b = 0 then none else checkedWide (Int.tdiv a b)
  | .intRem, [.int a, .int b] => if b = 0 then none else checkedWide (Int.tmod a b)
  | .intFit, [.int a, .int b] => if fits a b then checkedWide a else none
  | .f64Add, [.int a, .int b] => checked (Ieee.f64Add a b)
  | .f64Sub, [.int a, .int b] => checked (Ieee.f64Sub a b)
  | .f64Mul, [.int a, .int b] => checked (Ieee.f64Mul a b)
  | .f64Div, [.int a, .int b] => checked (Ieee.f64Div a b)
  | .f64Lt, [.int a, .int b] => checked (Ieee.f64Lt a b)
  | .f64Eq, [.int a, .int b] => checked (Ieee.f64Eq a b)
  | .f64OfInt, [.int a, .int _] => checked (Ieee.f64OfInt a)
  | .f64ToInt, [.int a, .int _] => checkedOpt (Ieee.f64ToInt a)
  | .f64Narrow, [.int a, .int _] => checked (Ieee.f64Narrow a)
  | .f64Widen, [.int a, .int _] => checked (Ieee.f64Widen a)
  | .f64OfDecimal, [.int a, .int b] => checked (Ieee.f64OfDecimal a b)
  | .f64Digits, [.int a, .int b] => checkedOpt (Ieee.f64Digits a b)
  | .f64Exp10, [.int a, .int b] => checkedOpt (Ieee.f64Exp10 a b)
  | .f64Sqrt, [.int a, .int _] => checked (Ieee.f64Sqrt a)
  | .f64Round, [.int a, .int b] => checkedOpt (Ieee.f64Round a b)
  | .wideAdd, [.int a, .int b] => checkedWide (a + b)
  | .wideSub, [.int a, .int b] => checkedWide (a - b)
  | .wideMul, [.int a, .int b] => checkedWide (a * b)
  | .intAnd, [.int a, .int b] => ofUnsigned (unsigned a &&& unsigned b)
  | .intOr, [.int a, .int b] => ofUnsigned (unsigned a ||| unsigned b)
  | .intXor, [.int a, .int b] => ofUnsigned (unsigned a ^^^ unsigned b)
  | .intShl, [.int a, .int b] =>
    if 0 ≤ b ∧ b < 128 then checkedWide (a * 2 ^ b.toNat) else none
  | .intShr, [.int a, .int b] => if 0 ≤ b then checkedWide (a >>> b.toNat) else none
  | .uwAdd, [.int a, .int b] => ofUnsigned (unsigned a + unsigned b)
  | .uwSub, [.int a, .int b] =>
    if unsigned b ≤ unsigned a then ofUnsigned (unsigned a - unsigned b) else none
  | .uwMul, [.int a, .int b] => ofUnsigned (unsigned a * unsigned b)
  | .uwDiv, [.int a, .int b] =>
    if unsigned b = 0 then none else ofUnsigned (unsigned a / unsigned b)
  | .uwRem, [.int a, .int b] =>
    if unsigned b = 0 then none else ofUnsigned (unsigned a % unsigned b)
  | .uwLt, [.int a, .int b] => some (.int (if unsigned a < unsigned b then 1 else 0))
  | .uwShl, [.int a, .int b] =>
    if 0 ≤ b ∧ b < 128 then ofUnsigned (unsigned a * 2 ^ b.toNat) else none
  | .uwShr, [.int a, .int b] => if 0 ≤ b then ofUnsigned (unsigned a / 2 ^ b.toNat) else none
  | .intBelow, [.int a, .int b] => if 0 ≤ a ∧ a < b then checkedWide a else none
  | .arrGet, [.data _ fields, .int i] => if 0 ≤ i then fields[i.toNat]? else none
  | .arrSet, [.data tag fields, .int i, v] =>
    if 0 ≤ i ∧ i.toNat < fields.length then some (.data tag (fields.set i.toNat v)) else none
  | .arrLen, [.data _ fields, _] => some (.int fields.length)
  | .arrPush, [.data tag fields, v] => some (.data (tag + 1) (fields ++ [v]))
  | .arrPop, [.data tag fields, _] =>
    match fields.getLast? with
    | some last => some (.data 0 [.data (tag - 1) fields.dropLast, last])
    | none => none
  | _, _ => none

def Atom.eval (ρ : Env) : Atom → Option Value
  | .var i => ρ[i]?
  | .int n => some (.int n)

def evalAtoms (ρ : Env) : List Atom → Option (List Value)
  | [] => some []
  | a :: as =>
    match a.eval ρ, evalAtoms ρ as with
    | some v, some vs => some (v :: vs)
    | _, _ => none

def Rhs.eval (ρ : Env) : Rhs → Option Value
  | .atom a => a.eval ρ
  | .prim p args =>
    match evalAtoms ρ args with
    | some vs => p.eval vs
    | none => none
  | .construct tag args =>
    match evalAtoms ρ args with
    | some vs => some (.data tag vs)
    | none => none
  | .place pl => pl.eval ρ
  | .closure fn captures =>
    match evalAtoms ρ captures with
    | some vs => some (.clo fn vs)
    | none => none
  | .rebind a fn =>
    match a.eval ρ with
    | some (.clo _ captured) => some (.clo fn captured)
    | _ => none

end Glorious
