import Glorious.Semantics.Layout

namespace Glorious.Semantics

def unicodeScalar (n : Nat) : Bool := n ≤ 0x10ffff && !(0xd800 ≤ n && n ≤ 0xdfff)

def intRange (target : Target) (signed : Bool) (width : IntWidth) : Int × Int :=
  let bits := width.bits target
  if signed then (-(Int.ofNat (2 ^ (bits - 1))), Int.ofNat (2 ^ (bits - 1)) - 1)
  else (0, Int.ofNat (2 ^ bits) - 1)

def integerFits (target : Target) (signed : Bool) (width : IntWidth) (value : Int) : Bool :=
  let (minimum, maximum) := intRange target signed width
  minimum ≤ value && value ≤ maximum

def wrappingInteger (target : Target) (signed : Bool) (width : IntWidth) (value : Int) : Int :=
  let modulus := Int.ofNat (2 ^ width.bits target)
  let bits := value % modulus
  if signed && bits ≥ modulus / 2 then bits - modulus else bits

def validateScalar (target : Target) (value : ScalarValue) : Check Unit :=
  match value with
  | .integer signed width value => require (integerFits target signed width value) .invalidScalar "integer value is out of range"
  | .character value => require (unicodeScalar value) .invalidScalar "invalid Unicode scalar value"
  | .floating width bits => require (bits < 2 ^ (if width == .w32 then 32 else 64)) .invalidScalar "floating bits exceed selected width"

inductive IntegerOperation where
  | add | sub | mul | div | rem | neg | bitAnd | bitOr | bitXor | bitNot
  | shl | shr | eq | ne | lt | le | gt | ge | convert
  deriving BEq, DecidableEq, Repr

inductive OverflowMode where
  | checked | wrapping
  deriving BEq, DecidableEq, Repr

def integerOperation (target : Target) (operation : IntegerOperation) (mode : OverflowMode)
    (signed : Bool) (width : IntWidth) (left right : Int) : Check ScalarValue := do
  let bits := width.bits target
  let mask := 2 ^ bits - 1
  let comparison (answer : Bool) : ScalarValue := .integer false .w32 (if answer then 1 else 0)
  match operation with
  | .eq => return comparison (left == right)
  | .ne => return comparison (left != right)
  | .lt => return comparison (left < right)
  | .le => return comparison (left ≤ right)
  | .gt => return comparison (left > right)
  | .ge => return comparison (left ≥ right)
  | _ => pure ()
  let raw ← match operation with
    | .add => pure (left + right)
    | .sub => pure (left - right)
    | .mul => pure (left * right)
    | .neg => pure (-left)
    | .div | .rem => do
      require (right != 0) .invalidScalar "integer division by zero"
      let magnitude := left.natAbs / right.natAbs
      let quotient := if (left < 0) != (right < 0) then -(Int.ofNat magnitude) else Int.ofNat magnitude
      pure (if operation == .div then quotient else left - quotient * right)
    | .bitAnd => pure (Int.ofNat (Nat.land (left % Int.ofNat (2 ^ bits)).toNat (right % Int.ofNat (2 ^ bits)).toNat))
    | .bitOr => pure (Int.ofNat (Nat.lor (left % Int.ofNat (2 ^ bits)).toNat (right % Int.ofNat (2 ^ bits)).toNat))
    | .bitXor => pure (Int.ofNat (Nat.xor (left % Int.ofNat (2 ^ bits)).toNat (right % Int.ofNat (2 ^ bits)).toNat))
    | .bitNot => pure (Int.ofNat (Nat.xor (left % Int.ofNat (2 ^ bits)).toNat mask))
    | .shl => do
      require (right ≥ 0 && right < Int.ofNat bits) .invalidScalar "integer shift count exceeds width"
      pure (left * Int.ofNat (2 ^ right.toNat))
    | .shr => do
      require (right ≥ 0 && right < Int.ofNat bits) .invalidScalar "integer shift count exceeds width"
      pure (left / Int.ofNat (2 ^ right.toNat))
    | .convert => pure left
    | _ => reject .malformedCore "comparison used as arithmetic"
  let isBitwise := [.bitAnd, .bitOr, .bitXor, .bitNot, .shl, .shr].contains operation
  let value := if mode == .wrapping || isBitwise then wrappingInteger target signed width raw else raw
  require (integerFits target signed width value) .invalidScalar "checked integer overflow"
  return .integer signed width value

structure FloatFormat where
  fractionBits : Nat
  exponentBits : Nat
  bias : Nat
  deriving Repr

def floatFormat : FloatWidth → FloatFormat
  | .w32 => ⟨23, 8, 127⟩
  | .w64 => ⟨52, 11, 1023⟩

inductive BinaryFloat where
  | zero (negative : Bool)
  | finite (negative : Bool) (significand : Nat) (exponent : Int)
  | infinity (negative : Bool)
  | nan
  deriving Repr

def decodeFloat (width : FloatWidth) (bits : Nat) : BinaryFloat :=
  let f := floatFormat width
  let sign := (bits / 2 ^ (f.fractionBits + f.exponentBits)) % 2 == 1
  let exponent := (bits / 2 ^ f.fractionBits) % 2 ^ f.exponentBits
  let fraction := bits % 2 ^ f.fractionBits
  if exponent == 2 ^ f.exponentBits - 1 then
    if fraction == 0 then .infinity sign else .nan
  else if exponent == 0 then
    if fraction == 0 then .zero sign else .finite sign fraction (1 - Int.ofNat f.bias - Int.ofNat f.fractionBits)
  else .finite sign (2 ^ f.fractionBits + fraction) (Int.ofNat exponent - Int.ofNat f.bias - Int.ofNat f.fractionBits)

def signBits (width : FloatWidth) (negative : Bool) : Nat :=
  let f := floatFormat width
  if negative then 2 ^ (f.fractionBits + f.exponentBits) else 0

def infinityBits (width : FloatWidth) (negative : Bool) : Nat :=
  let f := floatFormat width
  signBits width negative + (2 ^ f.exponentBits - 1) * 2 ^ f.fractionBits

def canonicalNaN (width : FloatWidth) : Nat :=
  let f := floatFormat width
  infinityBits width false + 2 ^ (f.fractionBits - 1)

/-- Exact ties-to-even rounding of a nonnegative rational; there is no wider
    host float parse and hence no hidden double rounding of f32 literals. -/
def roundEven (numerator denominator : Nat) : Nat :=
  let quotient := numerator / denominator
  let remainder := numerator % denominator
  if 2 * remainder > denominator || (2 * remainder == denominator && quotient % 2 == 1)
  then quotient + 1 else quotient

def scaledRatio (numerator denominator : Nat) (shift : Int) : Nat × Nat :=
  if shift ≥ 0 then (numerator * 2 ^ shift.toNat, denominator)
  else (numerator, denominator * 2 ^ shift.natAbs)

def floorLogRatio (fuel numerator denominator : Nat) : Check Int := do
  require (numerator > 0 && denominator > 0) .invalidScalar "logarithm needs a positive finite rational"
  let estimate := Int.ofNat numerator.log2 - Int.ofNat denominator.log2
  let rec adjust : Nat → Int → Check Int
    | 0, _ => reject .resourceLimit "floating normalization exhausted"
    | n + 1, exponent =>
      let (a, b) := scaledRatio numerator denominator (-exponent)
      if a < b then adjust n (exponent - 1)
      else if a ≥ 2 * b then adjust n (exponent + 1)
      else return exponent
  adjust fuel estimate

def roundFloat (fuel : Nat) (width : FloatWidth) (negative : Bool)
    (numerator denominator : Nat) (literal : Bool := false) : Check Nat := do
  require (denominator != 0) .invalidScalar "zero rational denominator"
  if numerator == 0 then return signBits width negative
  let f := floatFormat width
  let exponent ← floorLogRatio fuel numerator denominator
  let minimum := 1 - Int.ofNat f.bias
  let maximum := Int.ofNat (2 ^ f.exponentBits - 2) - Int.ofNat f.bias
  let quantum := max exponent minimum - Int.ofNat f.fractionBits
  let (a, b) := scaledRatio numerator denominator (-quantum)
  let significand := roundEven a b
  let (significand, quantum) := if significand ≥ 2 ^ (f.fractionBits + 1)
    then (significand / 2, quantum + 1) else (significand, quantum)
  let roundedExponent := quantum + Int.ofNat f.fractionBits
  if roundedExponent > maximum then
    require (!literal) .invalidScalar "finite floating literal overflows its selected width"
    return infinityBits width negative
  if significand < 2 ^ f.fractionBits then return signBits width negative + significand
  let exponentField := (roundedExponent + Int.ofNat f.bias).toNat
  return signBits width negative + exponentField * 2 ^ f.fractionBits + (significand - 2 ^ f.fractionBits)

def decimalFloatBits (fuel : Nat) (width : FloatWidth) (negative : Bool)
    (significand : Nat) (decimalExponent : Int) : Check Nat := do
  require (decimalExponent.natAbs ≤ fuel) .resourceLimit "decimal literal exponent exceeds normalization budget"
  let (numerator, denominator) := if decimalExponent ≥ 0
    then (significand * 10 ^ decimalExponent.toNat, 1) else (significand, 10 ^ decimalExponent.natAbs)
  roundFloat fuel width negative numerator denominator true

def floatRational : BinaryFloat → Option (Int × Nat)
  | .zero _ => some (0, 1)
  | .finite negative significand exponent =>
    let (numerator, denominator) := scaledRatio significand 1 exponent
    some (if negative then -(Int.ofNat numerator) else Int.ofNat numerator, denominator)
  | _ => none

def floatSign : BinaryFloat → Bool
  | .zero sign | .finite sign .. | .infinity sign => sign
  | .nan => false

inductive FloatOperation where
  | add | sub | mul | div | rem | neg | eq | ne | lt | le | gt | ge
  deriving BEq, DecidableEq, Repr

def floatOperation (fuel : Nat) (width : FloatWidth) (operation : FloatOperation)
    (leftBits rightBits : Nat) : Check ScalarValue := do
  let left := decodeFloat width leftBits
  let right := decodeFloat width rightBits
  let float (bits : Nat) := ScalarValue.floating width bits
  let boolean (answer : Bool) := ScalarValue.integer false .w32 (if answer then 1 else 0)
  if operation == .neg then
    return float (match left with | .nan => canonicalNaN width | _ => Nat.xor leftBits (signBits width true))
  let unordered := match left, right with | .nan, _ | _, .nan => true | _, _ => false
  if [.eq, .ne, .lt, .le, .gt, .ge].contains operation then
    let ordering : Int := match left, right with
      | .infinity false, .infinity false | .infinity true, .infinity true => 0
      | .infinity true, _ | _, .infinity false => -1
      | .infinity false, _ | _, .infinity true => 1
      | _, _ => match floatRational left, floatRational right with
        | some (a, b), some (c, d) => if a * Int.ofNat d < c * Int.ofNat b then -1 else if a * Int.ofNat d > c * Int.ofNat b then 1 else 0
        | _, _ => 0
    return boolean (match operation with
      | .eq => !unordered && ordering == 0 | .ne => unordered || ordering != 0
      | .lt => !unordered && ordering < 0 | .le => !unordered && ordering ≤ 0
      | .gt => !unordered && ordering > 0 | .ge => !unordered && ordering ≥ 0 | _ => false)
  if unordered then return float (canonicalNaN width)
  let right := if operation == .sub then match right with
    | .zero s => .zero (!s) | .finite s m e => .finite (!s) m e | .infinity s => .infinity (!s) | .nan => .nan
    else right
  let operation := if operation == .sub then .add else operation
  let sign := floatSign left != floatSign right
  match left, right with
  | .infinity a, .infinity b =>
    return float (if operation == .div || operation == .rem || (operation == .add && a != b)
      then canonicalNaN width else infinityBits width (if operation == .add then a else sign))
  | .infinity a, .zero _ | .zero _, .infinity a =>
    return float (if operation == .mul || operation == .rem then canonicalNaN width
      else if operation == .div && (floatRational left).isSome then signBits width sign
      else infinityBits width (if operation == .add then a else sign))
  | .infinity a, _ => return float (if operation == .rem then canonicalNaN width else infinityBits width (if operation == .add then a else sign))
  | _, .infinity b => return float (if operation == .div then signBits width sign else if operation == .rem then leftBits
      else infinityBits width (if operation == .add then b else sign))
  | _, _ =>
    let (a, b) ← getRequired (floatRational left) .invalidScalar "nonfinite floating operand"
    let (c, d) ← getRequired (floatRational right) .invalidScalar "nonfinite floating operand"
    if operation == .div && c == 0 then
      return float (if a == 0 then canonicalNaN width else infinityBits width sign)
    if operation == .rem && c == 0 then return float (canonicalNaN width)
    let (numerator, denominator) := match operation with
      | .add => (a * Int.ofNat d + c * Int.ofNat b, b * d)
      | .mul => (a * c, b * d)
      | .div => (if c < 0 then -(a * Int.ofNat d) else a * Int.ofNat d, b * c.natAbs)
      | .rem =>
        let qAbs := (a.natAbs * d) / (b * c.natAbs)
        let q := if (a < 0) != (c < 0) then -(Int.ofNat qAbs) else Int.ofNat qAbs
        (a * Int.ofNat d - q * c * Int.ofNat b, b * d)
      | _ => (0, 1)
    let negative := if numerator != 0 then numerator < 0 else
      if operation == .add then floatSign left && floatSign right else if operation == .rem then floatSign left else sign
    return float (← roundFloat fuel width negative numerator.natAbs denominator)

end Glorious.Semantics
