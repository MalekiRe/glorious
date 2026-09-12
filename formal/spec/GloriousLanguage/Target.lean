import GloriousLanguage.Syntax

/-! Explicit target contracts (§§4, 15–18). These are mathematical meanings of
machine leaves and shared layouts, not library algorithms or a code generator. -/
namespace Glorious.Language

inductive Endianness where
  | little | big
  deriving DecidableEq, BEq, Repr, Inhabited

inductive Representation where
  | glorious | c | transparent | integer (signed : Bool) (width : Width)
  deriving DecidableEq, BEq, Repr, Inhabited

structure Layout where
  size : Nat
  alignment : Nat
  offsets : List Nat := []
  tagBytes : Nat := 0
  payloadOffset : Nat := 0
  variants : List (List Nat) := []
  deriving DecidableEq, BEq, Repr, Inhabited

structure TargetProfile where
  identity : Identity
  generation : Nat
  triple : String
  pointerBits : Nat
  endian : Endianness
  scalarAlignment : Scalar → Nat
  cScalarAlignment : Scalar → Nat
  cCompatibleScalars : List Scalar
  cBoolBytes : Nat
  cFunctionPointerBytes : Nat
  maximumObjectBytes : Nat
  callableConvention : Identity
  effectConvention : Identity
  manifestIdentity : Identity
  supportsC : Bool
  codeIdentityLayout : Layout
  continuationLayout : Layout
  cRecordLayout : List Layout → Layout

def Width.bits (target : TargetProfile) : Width → Nat
  | .fixed bits => bits
  | .pointer => target.pointerBits

def Scalar.bytes (target : TargetProfile) : Scalar → Nat
  | .integer _ width => width.bits target / 8
  | .floating .single => 4
  | .floating .double => 8
  | .character => 4

def Scalar.Valid (target : TargetProfile) : Scalar → Prop
  | .integer _ (.fixed bits) => bits ∈ [8,16,32,64,128]
  | .integer _ .pointer => target.pointerBits ∈ [16,32,64,128]
  | _ => True

def PowerOfTwo (n : Nat) : Prop := ∃ k, n = 2^k
def Layout.Valid (layout : Layout) : Prop :=
  PowerOfTwo layout.alignment ∧ layout.size % layout.alignment = 0 ∧
  ∀ offset ∈ layout.offsets, offset ≤ layout.size

/-- A target supplies its C record layout; the language does not ask a host
compiler for an ambient answer. These are the representation invariants the
selected answer must satisfy, including zero-sized fields. -/
def CRecordLayout (target : TargetProfile) (fields : List Layout) (layout : Layout) : Prop :=
  target.supportsC = true ∧ layout = target.cRecordLayout fields ∧ layout.Valid ∧
  layout.offsets.length = fields.length ∧ layout.tagBytes = 0 ∧ layout.variants = [] ∧
  (∀ (index : Nat) field offset, fields[index]? = some field → layout.offsets[index]? = some offset →
    offset % field.alignment = 0 ∧ offset+field.size ≤ layout.size ∧ field.alignment ≤ layout.alignment) ∧
  (∀ (i j : Nat) left right a b, i < j → fields[i]? = some left → fields[j]? = some right →
    layout.offsets[i]? = some a → layout.offsets[j]? = some b →
    left.size = 0 ∨ right.size = 0 ∨ a+left.size ≤ b)

def IdentityLayout (layout : Layout) : Prop :=
  layout.Valid ∧ layout.offsets = [] ∧ layout.tagBytes = 0 ∧ layout.payloadOffset = 0 ∧ layout.variants = []

def TargetProfile.Valid (target : TargetProfile) : Prop :=
  target.pointerBits ∈ [16,32,64,128] ∧ 0 < target.maximumObjectBytes ∧
  (∀ scalar, scalar.Valid target → PowerOfTwo (target.scalarAlignment scalar) ∧
    scalar.bytes target % target.scalarAlignment scalar = 0) ∧
  (∀ scalar ∈ target.cCompatibleScalars, scalar.Valid target ∧ PowerOfTwo (target.cScalarAlignment scalar)) ∧
  (target.supportsC = true → 0 < target.cBoolBytes ∧ 0 < target.cFunctionPointerBytes ∧
    ∀ fields, (∀ field ∈ fields, field.Valid) → CRecordLayout target fields (target.cRecordLayout fields)) ∧
  IdentityLayout target.codeIdentityLayout ∧ IdentityLayout target.continuationLayout ∧
  0 < target.continuationLayout.size ∧ target.codeIdentityLayout.size ≤ target.maximumObjectBytes ∧
  target.continuationLayout.size ≤ target.maximumObjectBytes

def alignUp (offset alignment : Nat) : Nat :=
  ((offset + alignment - 1) / alignment) * alignment

inductive FieldsLayout : Nat → List Layout → List Nat → Nat → Prop where
  | nil {offset} : FieldsLayout offset [] [] offset
  | cons {offset field rest offsets stop} : field.Valid →
      FieldsLayout (alignUp offset field.alignment + field.size) rest offsets stop →
      FieldsLayout offset (field :: rest) (alignUp offset field.alignment :: offsets) stop

def AggregateLayout (fields : List Layout) (layout : Layout) : Prop :=
  ∃ stop,
    FieldsLayout 0 fields layout.offsets stop ∧
    layout.alignment = fields.foldl (fun a field => max a field.alignment) 1 ∧
    layout.size = alignUp stop layout.alignment ∧
    layout.tagBytes = 0 ∧ layout.payloadOffset = 0 ∧ layout.variants = []

def ArrayLayout (element : Layout) (length : Nat) (layout : Layout) : Prop :=
  element.Valid ∧ layout =
    ⟨length * alignUp element.size element.alignment, element.alignment,
      (List.range length).map (fun i => i * alignUp element.size element.alignment),0,0,[]⟩

def EnumLayout (variants : List Layout) (layout : Layout) : Prop :=
  variants ≠ [] ∧ (∀ variant ∈ variants, variant.Valid) ∧
  layout.tagBytes ∈ [1,2,4,8,16] ∧ variants.length ≤ 2^(8*layout.tagBytes) ∧
  (∀ smaller ∈ [1,2,4,8,16], smaller < layout.tagBytes → 2^(8*smaller) < variants.length) ∧
  layout.alignment = max layout.tagBytes (variants.foldl (fun a variant => max a variant.alignment) 1) ∧
  layout.payloadOffset = alignUp layout.tagBytes (variants.foldl (fun a variant => max a variant.alignment) 1) ∧
  layout.size = alignUp (layout.payloadOffset + variants.foldl (fun size variant => max size variant.size) 0)
    layout.alignment ∧
  layout.offsets = [] ∧ layout.variants = variants.map (fun variant => variant.offsets.map (· + layout.payloadOffset))

def IntegerRange (target : TargetProfile) (signed : Bool) (width : Width) (n : Int) : Prop :=
  let bits := width.bits target
  if signed then -(2^(bits-1) : Int) ≤ n ∧ n < 2^(bits-1)
  else 0 ≤ n ∧ n < (2^bits : Int)

inductive Overflow where
  | checked | wrapping | saturating
  deriving DecidableEq, BEq, Repr, Inhabited

inductive IntegerOperation where
  | add | subtract | multiply | divide | remainder | negate
  | shiftLeft | shiftRight | bitAnd | bitOr | bitXor
  deriving DecidableEq, BEq, Repr, Inhabited

def integerWrap (target : TargetProfile) (signed : Bool) (width : Width) (n : Int) : Int :=
  let modulus : Int := 2^(width.bits target)
  let residue := n % modulus
  if signed && residue ≥ modulus / 2 then residue - modulus else residue

def integerClamp (target : TargetProfile) (signed : Bool) (width : Width) (n : Int) : Int :=
  let bits := width.bits target
  let lower : Int := if signed then -(2^(bits-1)) else 0
  let upper : Int := if signed then 2^(bits-1)-1 else 2^bits-1
  max lower (min upper n)

inductive IntegerResult (target : TargetProfile) (signed : Bool) (width : Width) :
    Overflow → Int → Except Fatal Int → Prop where
  | checked {n} : IntegerRange target signed width n → IntegerResult target signed width .checked n (.ok n)
  | overflow {n} : ¬ IntegerRange target signed width n →
      IntegerResult target signed width .checked n (.error .arithmetic)
  | wrapping {n} : IntegerResult target signed width .wrapping n (.ok (integerWrap target signed width n))
  | saturating {n} : IntegerResult target signed width .saturating n (.ok (integerClamp target signed width n))

/-- Infinite two's-complement bit operations. The finite-width result rule
then enforces the declared integer range, without relying on host integers. -/
def integerAnd : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a &&& b)
  | .ofNat a, .negSucc b => .ofNat (a ^^^ (a &&& b))
  | .negSucc a, .ofNat b => .ofNat (b ^^^ (b &&& a))
  | .negSucc a, .negSucc b => .negSucc (a ||| b)

def integerOr : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a ||| b)
  | .ofNat a, .negSucc b => .negSucc (b ^^^ (b &&& a))
  | .negSucc a, .ofNat b => .negSucc (a ^^^ (a &&& b))
  | .negSucc a, .negSucc b => .negSucc (a &&& b)

def integerXor : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a ^^^ b)
  | .ofNat a, .negSucc b => .negSucc (a ^^^ b)
  | .negSucc a, .ofNat b => .negSucc (a ^^^ b)
  | .negSucc a, .negSucc b => .ofNat (a ^^^ b)

def integerOperation (operation : IntegerOperation) (a b : Int) : Option Int :=
  match operation with
  | .add => some (a+b)
  | .subtract => some (a-b)
  | .multiply => some (a*b)
  | .divide => if b = 0 then none else some (a.tdiv b)
  | .remainder => if b = 0 then none else some (a.tmod b)
  | .negate => some (-a)
  | .shiftLeft => if b < 0 then none else some (a * 2^b.toNat)
  | .shiftRight => if b < 0 then none else some (a / 2^b.toNat)
  | .bitAnd => some (integerAnd a b)
  | .bitOr => some (integerOr a b)
  | .bitXor => some (integerXor a b)

/-- Exact rational arithmetic is used to state rounding, not host floating
evaluation. Denominators are checked at every mathematical observation. -/
structure Fraction where
  numerator : Int
  denominator : Nat
  deriving DecidableEq, BEq, Repr, Inhabited

def Fraction.Valid (q : Fraction) : Prop := 0 < q.denominator
def Fraction.Equal (a b : Fraction) : Prop := a.Valid ∧ b.Valid ∧
  a.numerator * b.denominator = b.numerator * a.denominator
def Fraction.Le (a b : Fraction) : Prop := a.Valid ∧ b.Valid ∧
  a.numerator * b.denominator ≤ b.numerator * a.denominator
def Fraction.add (a b : Fraction) : Fraction :=
  ⟨a.numerator * b.denominator + b.numerator * a.denominator, a.denominator*b.denominator⟩
def Fraction.negate (a : Fraction) : Fraction := ⟨-a.numerator,a.denominator⟩
def Fraction.subtract (a b : Fraction) : Fraction := a.add b.negate
def Fraction.multiply (a b : Fraction) : Fraction := ⟨a.numerator*b.numerator,a.denominator*b.denominator⟩
def Fraction.divide (a b : Fraction) : Fraction :=
  ⟨a.numerator * b.denominator * (if b.numerator < 0 then -1 else 1),
    a.denominator * b.numerator.natAbs⟩
def Fraction.absolute (a : Fraction) : Fraction := ⟨a.numerator.natAbs,a.denominator⟩

def binaryFraction (negative : Bool) (significand : Nat) (exponent : Int) : Fraction :=
  let sign : Int := if negative then -1 else 1
  if exponent < 0 then ⟨sign * significand, 2^exponent.natAbs⟩
  else ⟨sign * significand * 2^exponent.toNat,1⟩

def decimalFraction (literal : Source.FloatLiteral) : Fraction :=
  let digits := Source.digitsValue 10 (literal.whole ++ literal.fractional)
  let exponent := literal.exponent - Int.ofNat literal.fractional.length
  if exponent < 0 then ⟨digits,10^exponent.natAbs⟩
  else ⟨Int.ofNat digits * 10^exponent.toNat,1⟩

structure FloatFormat where
  fractionBits : Nat
  exponentBits : Nat
  bias : Nat
  deriving DecidableEq, BEq, Repr, Inhabited

def FloatWidth.format : FloatWidth → FloatFormat
  | .single => ⟨23,8,127⟩
  | .double => ⟨52,11,1023⟩

inductive FloatMeaning where
  | finite (negative : Bool) (significand : Nat) (exponent : Int)
  | infinity (negative : Bool)
  | nan
  deriving DecidableEq, BEq, Repr, Inhabited

def FloatMeaning.fraction : FloatMeaning → Option Fraction
  | .finite sign significand exponent => some (binaryFraction sign significand exponent)
  | _ => none

def decodeFloat (width : FloatWidth) (bits : Nat) : Option FloatMeaning :=
  let f := width.format
  if bits ≥ 2^(1+f.exponentBits+f.fractionBits) then none else
  let negative := bits / 2^(f.exponentBits+f.fractionBits) != 0
  let exponent := bits / 2^f.fractionBits % 2^f.exponentBits
  let fraction := bits % 2^f.fractionBits
  if exponent = 2^f.exponentBits-1 then
    some (if fraction = 0 then .infinity negative else .nan)
  else if exponent = 0 then
    some (.finite negative fraction (1 - Int.ofNat f.bias - Int.ofNat f.fractionBits))
  else some (.finite negative (2^f.fractionBits+fraction)
    (Int.ofNat exponent - Int.ofNat f.bias - Int.ofNat f.fractionBits))

def canonicalNaN (width : FloatWidth) : Nat :=
  let f := width.format
  (2^f.exponentBits-1)*2^f.fractionBits + 2^(f.fractionBits-1)

def overflowThreshold (width : FloatWidth) : Fraction :=
  let f := width.format
  binaryFraction false (2^(f.fractionBits+2)-1)
    (Int.ofNat (2^f.exponentBits-2) - Int.ofNat f.bias - Int.ofNat f.fractionBits - 1)

/-- Nearest finite representation, with the even significand selected on a
tie. The sign of an exactly zero result is an explicit input, not forgotten. -/
def RoundsFinite (width : FloatWidth) (exact : Fraction) (negativeZero : Bool) (bits : Nat) : Prop :=
  exact.Valid ∧ ¬ (overflowThreshold width).Le exact.absolute ∧
  ∃ sign significand exponent value,
    decodeFloat width bits = some (.finite sign significand exponent) ∧
    value = binaryFraction sign significand exponent ∧
    (significand = 0 → sign = (if exact.numerator = 0 then negativeZero else decide (exact.numerator < 0))) ∧
    (∀ other sign' significand' exponent',
      decodeFloat width other = some (.finite sign' significand' exponent') →
      (exact.subtract value).absolute.Le
        (exact.subtract (binaryFraction sign' significand' exponent')).absolute) ∧
    (∀ other sign' significand' exponent', other ≠ bits →
      decodeFloat width other = some (.finite sign' significand' exponent') →
      (significand' ≠ 0 ∨ sign' = sign) →
      (exact.subtract value).absolute.Equal
        (exact.subtract (binaryFraction sign' significand' exponent')).absolute → significand % 2 = 0)

inductive Rounded (width : FloatWidth) : Fraction → Bool → Nat → Prop where
  | finite {exact sign bits} : RoundsFinite width exact sign bits → Rounded width exact sign bits
  | overflow {exact sign bits} : exact.Valid → (overflowThreshold width).Le exact.absolute →
      decodeFloat width bits = some (.infinity (decide (exact.numerator < 0))) → Rounded width exact sign bits

inductive FloatOperation where
  | add | subtract | multiply | divide | negate | absolute | squareRoot | fusedMultiplyAdd
  deriving DecidableEq, BEq, Repr, Inhabited

inductive FloatCalculation (width : FloatWidth) : FloatOperation → List Nat → Nat → Prop where
  | nan {op inputs} : (∃ bits ∈ inputs, decodeFloat width bits = some .nan) →
      FloatCalculation width op inputs (canonicalNaN width)
  | addFinite {a b sa sb ma mb ea eb result} :
      decodeFloat width a = some (.finite sa ma ea) → decodeFloat width b = some (.finite sb mb eb) →
      Rounded width ((binaryFraction sa ma ea).add (binaryFraction sb mb eb)) (sa && sb) result →
      FloatCalculation width .add [a,b] result
  | subtract {a b opposite result} : FloatCalculation width .negate [b] opposite →
      FloatCalculation width .add [a,opposite] result → FloatCalculation width .subtract [a,b] result
  | multiplyFinite {a b sa sb ma mb ea eb result} :
      decodeFloat width a = some (.finite sa ma ea) → decodeFloat width b = some (.finite sb mb eb) →
      Rounded width ((binaryFraction sa ma ea).multiply (binaryFraction sb mb eb)) (sa != sb) result →
      FloatCalculation width .multiply [a,b] result
  | divideFinite {a b sa sb ma mb ea eb result} :
      decodeFloat width a = some (.finite sa ma ea) → decodeFloat width b = some (.finite sb mb eb) → mb ≠ 0 →
      Rounded width ((binaryFraction sa ma ea).divide (binaryFraction sb mb eb)) (sa != sb) result →
      FloatCalculation width .divide [a,b] result
  | negateFinite {a sign significand exponent result} :
      decodeFloat width a = some (.finite sign significand exponent) →
      decodeFloat width result = some (.finite (!sign) significand exponent) →
      FloatCalculation width .negate [a] result
  | negateInfinity {a sign result} : decodeFloat width a = some (.infinity sign) →
      decodeFloat width result = some (.infinity (!sign)) → FloatCalculation width .negate [a] result
  | absoluteFinite {a sign significand exponent result} :
      decodeFloat width a = some (.finite sign significand exponent) →
      decodeFloat width result = some (.finite false significand exponent) → FloatCalculation width .absolute [a] result
  | absoluteInfinity {a sign result} : decodeFloat width a = some (.infinity sign) →
      decodeFloat width result = some (.infinity false) → FloatCalculation width .absolute [a] result
  | addInfinityLeft {a b sign other result} : decodeFloat width a = some (.infinity sign) →
      decodeFloat width b = some other → other ≠ .nan → other ≠ .infinity (!sign) →
      decodeFloat width result = some (.infinity sign) → FloatCalculation width .add [a,b] result
  | addInfinityRight {a b sign other result} : decodeFloat width b = some (.infinity sign) →
      decodeFloat width a = some other → other ≠ .nan → other ≠ .infinity (!sign) →
      decodeFloat width result = some (.infinity sign) → FloatCalculation width .add [a,b] result
  | addOppositeInfinity {a b sign} : decodeFloat width a = some (.infinity sign) →
      decodeFloat width b = some (.infinity (!sign)) → FloatCalculation width .add [a,b] (canonicalNaN width)
  | multiplyInfinity {a b sa sb meaningA meaningB result} :
      decodeFloat width a = some meaningA → decodeFloat width b = some meaningB →
      (meaningA = .infinity sa ∧ (meaningB = .infinity sb ∨ ∃ m e, m ≠ 0 ∧ meaningB = .finite sb m e) ∨
       meaningB = .infinity sb ∧ (meaningA = .infinity sa ∨ ∃ m e, m ≠ 0 ∧ meaningA = .finite sa m e)) →
      decodeFloat width result = some (.infinity (sa != sb)) → FloatCalculation width .multiply [a,b] result
  | multiplyZeroInfinity {a b sa sb exponent} :
      (decodeFloat width a = some (.finite sa 0 exponent) ∧ decodeFloat width b = some (.infinity sb) ∨
       decodeFloat width b = some (.finite sb 0 exponent) ∧ decodeFloat width a = some (.infinity sa)) →
      FloatCalculation width .multiply [a,b] (canonicalNaN width)
  | divideInfinity {a b sa sb m e result} : decodeFloat width a = some (.infinity sa) →
      decodeFloat width b = some (.finite sb m e) →
      decodeFloat width result = some (.infinity (sa != sb)) → FloatCalculation width .divide [a,b] result
  | divideByInfinity {a b sa sb m e result resultExponent} : decodeFloat width a = some (.finite sa m e) →
      decodeFloat width b = some (.infinity sb) → decodeFloat width result = some (.finite (sa != sb) 0 resultExponent) →
      FloatCalculation width .divide [a,b] result
  | divideByZero {a b sa sb m e zeroExponent result} : decodeFloat width a = some (.finite sa m e) → m ≠ 0 →
      decodeFloat width b = some (.finite sb 0 zeroExponent) →
      decodeFloat width result = some (.infinity (sa != sb)) → FloatCalculation width .divide [a,b] result
  | divideIndeterminate {a b sa sb ea eb} :
      (decodeFloat width a = some (.infinity sa) ∧ decodeFloat width b = some (.infinity sb) ∨
       decodeFloat width a = some (.finite sa 0 ea) ∧ decodeFloat width b = some (.finite sb 0 eb)) →
      FloatCalculation width .divide [a,b] (canonicalNaN width)
  | fused {a b c sa sb sc ma mb mc ea eb ec result} :
      decodeFloat width a = some (.finite sa ma ea) → decodeFloat width b = some (.finite sb mb eb) →
      decodeFloat width c = some (.finite sc mc ec) →
      Rounded width (((binaryFraction sa ma ea).multiply (binaryFraction sb mb eb)).add (binaryFraction sc mc ec))
        ((sa != sb) && sc) result → FloatCalculation width .fusedMultiplyAdd [a,b,c] result
  /-- Reusing multiplication and addition is exact only when an input to the
  product is already infinite: it cannot round an otherwise finite product
  before adding the third operand. Invalid zero-times-infinity propagates the
  canonical NaN through the ordinary arithmetic rules. -/
  | fusedInfiniteProduct {a b c product result} :
      (∃ sign, decodeFloat width a = some (.infinity sign) ∨
        decodeFloat width b = some (.infinity sign)) →
      FloatCalculation width .multiply [a,b] product →
      FloatCalculation width .add [product,c] result →
      FloatCalculation width .fusedMultiplyAdd [a,b,c] result
  /-- The exact product of two finite inputs is finite even when a separately
  rounded multiplication would overflow. An infinite addend therefore wins
  without first performing that potentially overflowing multiplication. -/
  | fusedInfiniteAddend {a b c sa sb sc ma mb ea eb} :
      decodeFloat width a = some (.finite sa ma ea) →
      decodeFloat width b = some (.finite sb mb eb) →
      decodeFloat width c = some (.infinity sc) →
      FloatCalculation width .fusedMultiplyAdd [a,b,c] c
  | sqrtZero {a sign exponent} : decodeFloat width a = some (.finite sign 0 exponent) →
      FloatCalculation width .squareRoot [a] a
  | sqrtInfinity {a} : decodeFloat width a = some (.infinity false) → FloatCalculation width .squareRoot [a] a
  | sqrtNegative {a m e} : (decodeFloat width a = some (.finite true m e) ∧ m ≠ 0 ∨
      decodeFloat width a = some (.infinity true)) → FloatCalculation width .squareRoot [a] (canonicalNaN width)
  | sqrtFinite {a m e result mr er} {lower upper : Fraction} : decodeFloat width a = some (.finite false m e) → m ≠ 0 →
      decodeFloat width result = some (.finite false mr er) →
      lower.Valid → upper.Valid → lower.Le upper → 0 ≤ lower.numerator →
      (lower.multiply lower).Le (binaryFraction false m e) →
      (binaryFraction false m e).Le (upper.multiply upper) →
      (∀ rational, lower.Le rational → rational.Le upper → RoundsFinite width rational false result) →
      FloatCalculation width .squareRoot [a] result

def ScalarValue.Valid (target : TargetProfile) : ScalarValue → Prop
  | .integer sign width n => (Scalar.integer sign width).Valid target ∧ IntegerRange target sign width n
  | .floating width bits => (decodeFloat width bits).isSome = true
  | .character scalar => Source.UnicodeScalar scalar

inductive Primitive where
  | integer (operation : IntegerOperation) (signed : Bool) (width : Width) (overflow : Overflow)
  | floating (operation : FloatOperation) (width : FloatWidth)
  | scalarEqual | scalarLess | scalarConvert
  | allocate | reallocate | release | rawMove | rawCopy | rawRead | rawWrite | rawBorrow
  | pointerOffset | pointerAddress | pointerWithAddress | layout | literalText | literalBytes
  | availableClose | bindingProject | bindingCombine | abort
  deriving DecidableEq, BEq, Repr, Inhabited

structure RuntimeBinding where
  declaration : DeclId
  signature : Signature
  primitive : Option Primitive
  symbol : Option String
  capability : Option String
  domain : Option Identity
  safeReviewed : Bool
  cABI : Bool
  deriving Repr, Inhabited

inductive IntrinsicRelation where
  | ordinary | use | drop | callable | runsIn | environment | label | available | bindings | bindingContext
  deriving DecidableEq, BEq, Repr, Inhabited

structure TestCarrier where
  declaration : DeclId
  positive : DeclId
  negative : DeclId
  positiveBindings : Nat
  negativeBindings : Nat
  deriving Repr, Inhabited

structure Manifest where
  identity : Identity
  targetIdentity : Identity
  bindings : List RuntimeBinding
  grantedCapabilities : List String
  allocationDomains : List Identity
  sealedRelations : List (DeclId × IntrinsicRelation) := []
  testCarrier : Option TestCarrier := none
  deriving Repr, Inhabited

def Manifest.WellFormed (target : TargetProfile) (manifest : Manifest) : Prop :=
  manifest.identity = target.manifestIdentity ∧ manifest.targetIdentity = target.identity ∧
  (manifest.bindings.map (·.declaration)).Nodup ∧
  (∀ binding ∈ manifest.bindings,
    (binding.primitive.isSome = true ∨ binding.symbol.isSome = true) ∧
    (∀ capability, binding.capability = some capability → capability ∈ manifest.grantedCapabilities) ∧
    (∀ domain, binding.domain = some domain → domain ∈ manifest.allocationDomains) ∧
    (binding.cABI = true → target.supportsC = true) ∧
    (binding.signature.unsafeAllowed = false → binding.safeReviewed = true))

end Glorious.Language
