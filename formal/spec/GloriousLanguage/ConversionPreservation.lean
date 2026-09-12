import GloriousLanguage.ScalarPreservation

/-! Policy-correct scalar conversion. Integer destinations are total on valid
scalar inputs. Floating policy lifting consumes the actual rounding witness;
`FloatRounding` proves its existence and `FloatProgress` derives full conversion
progress. These machine leaf contracts do not turn a fatal event into a source
checked Result. -/
namespace Glorious.Language

theorem binaryFraction.valid (negative : Bool) (significand : Nat) (exponent : Int) :
    (binaryFraction negative significand exponent).Valid := by
  by_cases belowZero : exponent < 0
  · simp only [binaryFraction,belowZero,↓reduceIte,Fraction.Valid]
    exact Nat.pow_pos (by decide : 0 < (2 : Nat))
  · simp only [binaryFraction,belowZero,↓reduceIte,Fraction.Valid]
    decide

theorem IntegerResult.deterministic {target : TargetProfile} {sign : Bool} {width : Width}
    {overflow : Overflow} {value : Int} {first second : Except Fatal Int}
    (left : IntegerResult target sign width overflow value first)
    (right : IntegerResult target sign width overflow value second) : first = second := by
  cases left <;> cases right <;> first | rfl | contradiction

theorem FractionIntegerConversion.total {target : TargetProfile} {sign : Bool} {width : Width}
    (policy : ConversionPolicy) (value : Fraction) (valid : value.Valid) :
    ∃ result, FractionIntegerConversion target sign width policy value result := by
  classical
  cases policy with
  | lossy => exact ⟨_,.lossy valid⟩
  | checked =>
      by_cases interval : value.IntegerInterval target sign width
      · exact ⟨_,.checked interval⟩
      · exact ⟨_,.outOfRange (by decide) valid interval⟩
  | exact =>
      by_cases interval : value.IntegerInterval target sign width
      · by_cases integral : value.numerator = value.numerator.tdiv value.denominator * (value.denominator : Int)
        · exact ⟨_,.exact interval integral⟩
        · exact ⟨_,.fractional interval integral⟩
      · exact ⟨_,.outOfRange (by decide) valid interval⟩

theorem FractionIntegerConversion.deterministic {target : TargetProfile} {sign : Bool} {width : Width}
    {policy : ConversionPolicy} {value : Fraction} {first second : Except Fatal Int}
    (left : FractionIntegerConversion target sign width policy value first)
    (right : FractionIntegerConversion target sign width policy value second) : first = second := by
  cases left <;> cases right <;> first | rfl | contradiction

theorem FractionIntegerConversion.nonlossy_interval {target : TargetProfile} {sign : Bool} {width : Width}
    {policy : ConversionPolicy} {value : Fraction} {result : Int}
    (nonlossy : policy ≠ .lossy)
    (converted : FractionIntegerConversion target sign width policy value (.ok result)) :
    value.IntegerInterval target sign width := by
  cases converted with
  | lossy _ => exact False.elim (nonlossy rfl)
  | checked interval => exact interval
  | exact interval _ => exact interval

/-- Rejection is based on the supplied fraction, even when its truncation
would be zero. This holds for every negative input and every integer width. -/
theorem FractionIntegerConversion.unsigned_negative_fault {target : TargetProfile} {width : Width}
    {policy : ConversionPolicy} {value : Fraction}
    (nonlossy : policy ≠ .lossy) (valid : value.Valid) (negative : value.numerator < 0) :
    FractionIntegerConversion target false width policy value (.error .arithmetic) := by
  apply FractionIntegerConversion.outOfRange nonlossy valid
  intro interval
  have nonnegative := interval.2.1
  simp only [integerMinimum,Bool.false_eq_true,↓reduceIte,Int.zero_mul] at nonnegative
  omega

theorem FractionIntegerConversion.checked_truncates {target : TargetProfile} {sign : Bool} {width : Width}
    {value : Fraction} {result : Int}
    (converted : FractionIntegerConversion target sign width .checked value (.ok result)) :
    result = value.numerator.tdiv value.denominator := by
  cases converted
  rfl

theorem FractionIntegerConversion.exact_preserves {target : TargetProfile} {sign : Bool} {width : Width}
    {value : Fraction} {result : Int}
    (converted : FractionIntegerConversion target sign width .exact value (.ok result)) :
    value.Equal ⟨result,1⟩ := by
  cases converted with
  | exact interval integral =>
      exact ⟨interval.1,by change 0 < (1 : Nat); decide,by simpa using integral⟩

theorem FractionIntegerConversion.lossy_iff {target : TargetProfile} {sign : Bool} {width : Width}
    {value : Fraction} {result : Except Fatal Int} :
    FractionIntegerConversion target sign width .lossy value result ↔
      value.Valid ∧ result = .ok (integerClamp target sign width (value.numerator.tdiv value.denominator)) := by
  constructor
  · intro converted
    cases converted with
    | lossy valid => exact ⟨valid,rfl⟩
    | outOfRange impossible _ _ => exact False.elim (impossible rfl)
  · rintro ⟨valid,rfl⟩
    exact .lossy valid

theorem Rounded.finite_or_infinite {width : FloatWidth} {value : Fraction} {zeroSign : Bool} {bits : Nat}
    (rounded : Rounded width value zeroSign bits) :
    (∃ sign significand exponent, decodeFloat width bits = some (.finite sign significand exponent)) ∨
      ∃ sign, decodeFloat width bits = some (.infinity sign) := by
  cases rounded with
  | finite rounded =>
      rcases rounded.2.2 with ⟨sign,significand,exponent,_,decoded,_⟩
      exact Or.inl ⟨sign,significand,exponent,decoded⟩
  | overflow _ _ decoded => exact Or.inr ⟨_,decoded⟩

/-- Deciding the conversion policy does not require another rounding
algorithm. This theorem consumes the same actual `Rounded` witness. -/
theorem RoundedConversion.of_rounded {width : FloatWidth} {value : Fraction} {zeroSign : Bool} {bits : Nat}
    (policy : ConversionPolicy) (rounded : Rounded width value zeroSign bits) :
    ∃ result, RoundedConversion width policy value zeroSign result := by
  classical
  cases policy with
  | lossy => exact ⟨_,.lossy rounded⟩
  | checked =>
      rcases rounded.finite_or_infinite with ⟨sign,significand,exponent,decoded⟩ | ⟨sign,decoded⟩
      · exact ⟨_,.checked rounded decoded⟩
      · exact ⟨_,.overflow (by decide) rounded decoded⟩
  | exact =>
      rcases rounded.finite_or_infinite with ⟨sign,significand,exponent,decoded⟩ | ⟨sign,decoded⟩
      · by_cases equal : value.Equal (binaryFraction sign significand exponent)
        · exact ⟨_,.exact rounded decoded equal⟩
        · exact ⟨_,.precisionLoss rounded decoded equal⟩
      · exact ⟨_,.overflow (by decide) rounded decoded⟩

theorem RoundedConversion.checked_finite {width : FloatWidth} {value : Fraction} {zeroSign : Bool} {bits : Nat}
    (converted : RoundedConversion width .checked value zeroSign (.ok bits)) :
    ∃ sign significand exponent, decodeFloat width bits = some (.finite sign significand exponent) := by
  cases converted with
  | checked _ decoded => exact ⟨_,_,_,decoded⟩

theorem RoundedConversion.exact_preserves {width : FloatWidth} {value : Fraction} {zeroSign : Bool} {bits : Nat}
    (converted : RoundedConversion width .exact value zeroSign (.ok bits)) :
    ∃ sign significand exponent, decodeFloat width bits = some (.finite sign significand exponent) ∧
      value.Equal (binaryFraction sign significand exponent) := by
  cases converted with
  | exact _ decoded equal => exact ⟨_,_,_,decoded,equal⟩

namespace Execution

theorem ScalarConversion.integer_integer_total {target : TargetProfile} {sourceSign : Bool}
    {sourceWidth : Width} {value : Int} (range : IntegerRange target sourceSign sourceWidth value)
    (policy : ConversionPolicy) (sign : Bool) (width : Width) :
    ∃ result, ScalarConversion target policy (.integer sourceSign sourceWidth value) (.integer sign width) result := by
  rcases IntegerResult.total target sign width policy.integerOverflow value with ⟨result,converted⟩
  cases result with
  | ok integer => exact ⟨_,.integer range converted⟩
  | error reason => exact ⟨_,.integerFault range converted⟩

/-- All numeric policies are total for an integer destination, including
finite fractions, both infinities and NaN, not just the integral-float cases. -/
theorem ScalarConversion.to_integer_total {target : TargetProfile} {source : ScalarValue}
    (sourceValid : source.Valid target) (policy : ConversionPolicy) (sign : Bool) (width : Width) :
    ∃ result, ScalarConversion target policy source (.integer sign width) result := by
  classical
  cases source with
  | integer _ _ _ => exact ScalarConversion.integer_integer_total sourceValid.2 policy sign width
  | character _ => exact ScalarConversion.character_integer_total sourceValid policy sign width
  | floating sourceWidth bits =>
      cases decoded : decodeFloat sourceWidth bits with
      | none => simp [ScalarValue.Valid,decoded] at sourceValid
      | some meaning =>
          cases meaning with
          | finite negative significand exponent =>
              rcases FractionIntegerConversion.total (target := target) (sign := sign) (width := width)
                policy _ (binaryFraction.valid negative significand exponent) with ⟨result,converted⟩
              cases result with
              | ok integer => exact ⟨_,.floatInteger decoded converted⟩
              | error reason => exact ⟨_,.floatIntegerFault decoded converted⟩
          | infinity negative =>
              by_cases lossy : policy = .lossy
              · exact ⟨_,.floatIntegerInfinity lossy decoded⟩
              · exact ⟨_,.floatIntegerNonfinite lossy (Or.inl ⟨negative,decoded⟩)⟩
          | nan =>
              by_cases lossy : policy = .lossy
              · exact ⟨_,.floatIntegerNaN lossy decoded⟩
              · exact ⟨_,.floatIntegerNonfinite lossy (Or.inr decoded)⟩

theorem ScalarConversion.to_character_total {target : TargetProfile} {sign : Bool} {width : Width}
    {value : Int} (range : IntegerRange target sign width value) (policy : ConversionPolicy) :
    ∃ result, ScalarConversion target policy (.integer sign width value) .character result := by
  classical
  by_cases nonnegative : 0 ≤ value
  · by_cases scalar : Source.UnicodeScalar value.toNat
    · exact ⟨_,.character nonnegative scalar range⟩
    · exact ⟨_,.characterInvalid range (Or.inr scalar)⟩
  · exact ⟨_,.characterInvalid range (Or.inl (by omega))⟩

theorem ScalarConversion.integer_float_of_rounded {target : TargetProfile} {sign : Bool} {width : Width}
    {value : Int} {destination : FloatWidth} {bits : Nat}
    (range : IntegerRange target sign width value) (policy : ConversionPolicy)
    (rounded : Rounded destination ⟨value,1⟩ false bits) :
    ∃ result, ScalarConversion target policy (.integer sign width value) (.floating destination) result := by
  rcases RoundedConversion.of_rounded policy rounded with ⟨result,converted⟩
  cases result with
  | ok bits => exact ⟨_,.integerFloat range converted⟩
  | error reason => exact ⟨_,.integerFloatFault range converted⟩

theorem ScalarConversion.float_of_rounded {target : TargetProfile} {sourceWidth destination : FloatWidth}
    {bits resultBits significand : Nat} {sign : Bool} {exponent : Int}
    (decoded : decodeFloat sourceWidth bits = some (.finite sign significand exponent))
    (policy : ConversionPolicy) (rounded : Rounded destination (binaryFraction sign significand exponent) sign resultBits) :
    ∃ result, ScalarConversion target policy (.floating sourceWidth bits) (.floating destination) result := by
  rcases RoundedConversion.of_rounded policy rounded with ⟨result,converted⟩
  cases result with
  | ok bits => exact ⟨_,.float decoded converted⟩
  | error reason => exact ⟨_,.floatFault decoded converted⟩

theorem ScalarConversion.nonfinite_float_total {target : TargetProfile} {sourceWidth destination : FloatWidth}
    {bits : Nat} {meaning : FloatMeaning} (decoded : decodeFloat sourceWidth bits = some meaning)
    (nonfinite : meaning.fraction = none) (policy : ConversionPolicy) :
    ∃ result, ScalarConversion target policy (.floating sourceWidth bits) (.floating destination) result := by
  cases meaning with
  | finite _ _ _ => simp [FloatMeaning.fraction] at nonfinite
  | infinity sign =>
      rcases decodeFloat.infinity_exists destination sign with ⟨result,decodedResult⟩
      exact ⟨_,.floatInfinity decoded decodedResult⟩
  | nan => exact ⟨_,.floatNaN decoded⟩

/-- The actual primitive producer inherits total policy outcomes and validity.
The proof does not use the store's prospective-result validity guard. -/
theorem PrimitiveCalculation.convert_integer_total {target : TargetProfile} {source : ScalarValue}
    (sourceValid : source.Valid target) (policy : ConversionPolicy) (sign : Bool) (width : Width)
    (destinationValid : (Scalar.integer sign width).Valid target) :
    ∃ outcome, PrimitiveCalculation target (.scalarConvert policy) [.scalar (.integer sign width)] [source] outcome ∧
      ∀ result, outcome = .ok result → result.Valid target ∧ result.type = .integer sign width := by
  rcases ScalarConversion.to_integer_total sourceValid policy sign width with ⟨outcome,converted⟩
  refine ⟨outcome,.convert converted,?_⟩
  intro result equal
  subst outcome
  exact ⟨converted.valid destinationValid,converted.type⟩

end Execution
end Glorious.Language
