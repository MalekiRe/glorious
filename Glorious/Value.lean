import Glorious.Float

/-!
# Runtime values and operands

Core and bytecode share one notion of runtime value and one notion of operand.
An activation's environment only grows, so an operand names a local by its
position in that environment.
-/

namespace Glorious

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
  /-- A reference: the address of a memory cell, and which borrow of the cell
  it is. The cell's own reference is borrow zero. Nothing the machine does
  depends on the borrow: it is there so that what it means for a borrow to be
  respected can be said. -/
  | ref (addr : Nat) (borrow : Nat)

/-- The locals of one activation, oldest first. -/
abbrev Env := List Value

/-- An operand: something that is already a value once locals are looked up. -/
inductive Atom where
  /-- The local at position `i` of the current environment. -/
  | var (i : Nat)
  | int (n : Int)

/-- A field path into a local: `var.path₀.path₁...`. -/
structure Place where
  var : Nat
  path : List Nat

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
  | .ref _ _, _ :: _ => none

/-- Is this value built by constructor `tag` with exactly `arity` fields? -/
def isCtor (v : Value) (tag arity : Nat) : Bool :=
  match v with
  | .data t fields => tag == t && arity == fields.length
  | .int _ => false
  | .clo _ _ => false
  | .cont _ => false
  | .label _ => false
  | .ref _ _ => false

/-- Is this value the integer `n`? -/
def isInt (v : Value) (n : Int) : Bool :=
  match v with
  | .int m => n == m
  | .data _ _ => false
  | .clo _ _ => false
  | .cont _ => false
  | .label _ => false
  | .ref _ _ => false

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
  | .intDiv, [.int a, .int b] => if b = 0 then none else checked (Int.tdiv a b)
  | .intRem, [.int a, .int b] => if b = 0 then none else checked (Int.tmod a b)
  | .intFit, [.int a, .int b] => if fits a b then checked a else none
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
