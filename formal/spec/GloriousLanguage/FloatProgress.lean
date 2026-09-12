import GloriousLanguage.FloatRounding

/-! Floating calculation progress consumes the proved existence of the same
rounding relation used by the machine leaves. The exact product of an FMA is
never rounded independently. Square-root isolation is a separate obligation. -/
namespace Glorious.Language

theorem Fraction.add_valid {left right : Fraction} (leftValid : left.Valid) (rightValid : right.Valid) :
    (left.add right).Valid := Nat.mul_pos leftValid rightValid

theorem Fraction.multiply_valid {left right : Fraction} (leftValid : left.Valid) (rightValid : right.Valid) :
    (left.multiply right).Valid := Nat.mul_pos leftValid rightValid

theorem binaryFraction.numerator_nonzero (sign : Bool) {significand : Nat} (exponent : Int)
    (nonzero : significand ≠ 0) : (binaryFraction sign significand exponent).numerator ≠ 0 := by
  have powerNonzero : (2 : Int)^exponent.toNat ≠ 0 := Int.pow_ne_zero (by decide)
  cases sign <;> by_cases negative : exponent < 0 <;>
    simp [binaryFraction,negative,Int.mul_ne_zero_iff,nonzero,powerNonzero]

theorem RoundedConversion.total (width : FloatWidth) (policy : ConversionPolicy) (value : Fraction)
    (zeroSign : Bool) (valid : value.Valid) :
    ∃ result, RoundedConversion width policy value zeroSign result := by
  rcases Rounded.total width value zeroSign valid with ⟨bits,rounded⟩
  exact RoundedConversion.of_rounded policy rounded

theorem decodeFloat.finite_sign_exists {width : FloatWidth} {bits significand : Nat} {sign : Bool} {exponent : Int}
    (decoded : decodeFloat width bits = some (.finite sign significand exponent)) (newSign : Bool) :
    ∃ result, decodeFloat width result = some (.finite newSign significand exponent) := by
  rcases FloatLattice.finite_code decoded with ⟨code,bounded,_,rfl,rfl⟩
  exact ⟨FloatLattice.encode width newSign code,FloatLattice.decode_encode width newSign code bounded⟩

theorem decodeFloat.zero_exists (width : FloatWidth) (sign : Bool) :
    ∃ bits exponent, decodeFloat width bits = some (.finite sign 0 exponent) := by
  have bounded : 0 < FloatLattice.cutoff width := by cases width <;> decide
  have decoded := FloatLattice.decode_encode width sign 0 bounded
  refine ⟨FloatLattice.encode width sign 0,(FloatLattice.power width 0 : Int) - FloatLattice.scale width,?_⟩
  simpa [FloatLattice.meaning,FloatLattice.significand] using decoded

theorem FloatCalculation.negate_total {width : FloatWidth} {input : Nat} {meaning : FloatMeaning}
    (decoded : decodeFloat width input = some meaning) :
    ∃ result, FloatCalculation width .negate [input] result := by
  cases meaning with
  | nan => exact ⟨_,.nan ⟨input,by simp,decoded⟩⟩
  | infinity sign =>
      rcases decodeFloat.infinity_exists width (!sign) with ⟨result,resultDecoded⟩
      exact ⟨result,.negateInfinity decoded resultDecoded⟩
  | finite sign significand exponent =>
      rcases decodeFloat.finite_sign_exists decoded (!sign) with ⟨result,resultDecoded⟩
      exact ⟨result,.negateFinite decoded resultDecoded⟩

theorem FloatCalculation.absolute_total {width : FloatWidth} {input : Nat} {meaning : FloatMeaning}
    (decoded : decodeFloat width input = some meaning) :
    ∃ result, FloatCalculation width .absolute [input] result := by
  cases meaning with
  | nan => exact ⟨_,.nan ⟨input,by simp,decoded⟩⟩
  | infinity _ =>
      rcases decodeFloat.infinity_exists width false with ⟨result,resultDecoded⟩
      exact ⟨result,.absoluteInfinity decoded resultDecoded⟩
  | finite _ _ _ =>
      rcases decodeFloat.finite_sign_exists decoded false with ⟨result,resultDecoded⟩
      exact ⟨result,.absoluteFinite decoded resultDecoded⟩

theorem FloatCalculation.add_total {width : FloatWidth} {a b : Nat} {meaningA meaningB : FloatMeaning}
    (left : decodeFloat width a = some meaningA) (right : decodeFloat width b = some meaningB) :
    ∃ result, FloatCalculation width .add [a,b] result := by
  cases meaningA with
  | nan => exact ⟨_,.nan ⟨a,by simp,left⟩⟩
  | infinity _ => exact FloatCalculation.add_infinite_left_total left right
  | finite sa ma ea =>
      cases meaningB with
      | nan => exact ⟨_,.nan ⟨b,by simp,right⟩⟩
      | infinity sb =>
          rcases decodeFloat.infinity_exists width sb with ⟨result,decoded⟩
          exact ⟨result,.addInfinityRight right left (by intro h; cases h) (by intro h; cases h) decoded⟩
      | finite sb mb eb =>
          rcases Rounded.total width _ (sa && sb)
            (Fraction.add_valid (binaryFraction.valid sa ma ea) (binaryFraction.valid sb mb eb)) with ⟨result,rounded⟩
          exact ⟨result,.addFinite left right rounded⟩

theorem FloatCalculation.subtract_total {width : FloatWidth} {a b : Nat} {meaningA meaningB : FloatMeaning}
    (left : decodeFloat width a = some meaningA) (right : decodeFloat width b = some meaningB) :
    ∃ result, FloatCalculation width .subtract [a,b] result := by
  rcases FloatCalculation.negate_total right with ⟨opposite,negated⟩
  have valid := negated.valid
  cases decoded : decodeFloat width opposite with
  | none => simp [decoded] at valid
  | some meaning =>
      rcases FloatCalculation.add_total left decoded with ⟨result,added⟩
      exact ⟨result,.subtract negated added⟩

theorem FloatCalculation.multiply_total {width : FloatWidth} {a b : Nat} {meaningA meaningB : FloatMeaning}
    (left : decodeFloat width a = some meaningA) (right : decodeFloat width b = some meaningB) :
    ∃ result, FloatCalculation width .multiply [a,b] result := by
  have infinite : (∃ sign, meaningA = .infinity sign ∨ meaningB = .infinity sign) →
      ∃ result, FloatCalculation width .multiply [a,b] result := by
    intro exceptional
    rcases FloatCalculation.multiply_infinite_total left right exceptional with ⟨result,calculated,_⟩
    exact ⟨result,calculated⟩
  cases meaningA with
  | nan => exact ⟨_,.nan ⟨a,by simp,left⟩⟩
  | infinity sign => exact infinite ⟨sign,Or.inl rfl⟩
  | finite sa ma ea =>
      cases meaningB with
      | nan => exact ⟨_,.nan ⟨b,by simp,right⟩⟩
      | infinity sign => exact infinite ⟨sign,Or.inr rfl⟩
      | finite sb mb eb =>
          rcases Rounded.total width _ (sa != sb)
            (Fraction.multiply_valid (binaryFraction.valid sa ma ea) (binaryFraction.valid sb mb eb)) with ⟨result,rounded⟩
          exact ⟨result,.multiplyFinite left right rounded⟩

theorem FloatCalculation.divide_total {width : FloatWidth} {a b : Nat} {meaningA meaningB : FloatMeaning}
    (left : decodeFloat width a = some meaningA) (right : decodeFloat width b = some meaningB) :
    ∃ result, FloatCalculation width .divide [a,b] result := by
  cases meaningA with
  | nan => exact ⟨_,.nan ⟨a,by simp,left⟩⟩
  | infinity sa =>
      cases meaningB with
      | nan => exact ⟨_,.nan ⟨b,by simp,right⟩⟩
      | infinity sb => exact ⟨_,.divideIndeterminate (ea := 0) (eb := 0) (Or.inl ⟨left,right⟩)⟩
      | finite sb _ _ =>
          rcases decodeFloat.infinity_exists width (sa != sb) with ⟨result,decoded⟩
          exact ⟨result,.divideInfinity left right decoded⟩
  | finite sa ma ea =>
      cases meaningB with
      | nan => exact ⟨_,.nan ⟨b,by simp,right⟩⟩
      | infinity sb =>
          rcases decodeFloat.zero_exists width (sa != sb) with ⟨result,exponent,decoded⟩
          exact ⟨result,.divideByInfinity left right decoded⟩
      | finite sb mb eb =>
          by_cases zero : mb = 0
          · subst mb
            by_cases zeroLeft : ma = 0
            · subst ma
              exact ⟨_,.divideIndeterminate (Or.inr ⟨left,right⟩)⟩
            · rcases decodeFloat.infinity_exists width (sa != sb) with ⟨result,decoded⟩
              exact ⟨result,.divideByZero left zeroLeft right decoded⟩
          · have valid : ((binaryFraction sa ma ea).divide (binaryFraction sb mb eb)).Valid :=
              Nat.mul_pos (binaryFraction.valid sa ma ea) (Int.natAbs_pos.mpr (binaryFraction.numerator_nonzero sb eb zero))
            rcases Rounded.total width _ (sa != sb) valid with ⟨result,rounded⟩
            exact ⟨result,.divideFinite left right zero rounded⟩

theorem FloatCalculation.fused_total {width : FloatWidth} {a b c : Nat} {meaningA meaningB meaningC : FloatMeaning}
    (left : decodeFloat width a = some meaningA) (right : decodeFloat width b = some meaningB)
    (addend : decodeFloat width c = some meaningC) :
    ∃ result, FloatCalculation width .fusedMultiplyAdd [a,b,c] result := by
  have nonfinite : meaningA.fraction = none ∨ meaningB.fraction = none ∨ meaningC.fraction = none →
      ∃ result, FloatCalculation width .fusedMultiplyAdd [a,b,c] result := by
    intro exceptional
    rcases FloatCalculation.fused_nonfinite_total left right addend exceptional with ⟨result,calculated,_⟩
    exact ⟨result,calculated⟩
  cases meaningA with
  | nan => exact nonfinite (Or.inl rfl)
  | infinity _ => exact nonfinite (Or.inl rfl)
  | finite sa ma ea =>
      cases meaningB with
      | nan => exact nonfinite (Or.inr (Or.inl rfl))
      | infinity _ => exact nonfinite (Or.inr (Or.inl rfl))
      | finite sb mb eb =>
          cases meaningC with
          | nan => exact nonfinite (Or.inr (Or.inr rfl))
          | infinity _ => exact nonfinite (Or.inr (Or.inr rfl))
          | finite sc mc ec =>
              have valid := Fraction.add_valid
                (Fraction.multiply_valid (binaryFraction.valid sa ma ea) (binaryFraction.valid sb mb eb))
                (binaryFraction.valid sc mc ec)
              rcases Rounded.total width _ ((sa != sb) && sc) valid with ⟨result,rounded⟩
              exact ⟨result,.fused left right addend rounded⟩

/-- All correctly shaped nonsquare-root operations progress on every valid
bit pattern. No arithmetic or conversion caller supplies a rounding witness. -/
theorem FloatCalculation.nonsqrt_total (width : FloatWidth) (operation : FloatOperation) (inputs : List Nat)
    (arity : inputs.length = Execution.FloatArity operation)
    (valid : ∀ bits ∈ inputs, (decodeFloat width bits).isSome = true)
    (nonsqrt : operation ≠ .squareRoot) : ∃ result, FloatCalculation width operation inputs result := by
  have decoded : ∀ bits ∈ inputs, ∃ meaning, decodeFloat width bits = some meaning := by
    intro bits member
    have inputValid := valid bits member
    cases observed : decodeFloat width bits with
    | none => simp [observed] at inputValid
    | some meaning => exact ⟨meaning,rfl⟩
  cases operation with
  | squareRoot => exact False.elim (nonsqrt rfl)
  | negate | absolute =>
      rcases List.length_eq_one_iff.mp arity with ⟨input,rfl⟩
      rcases decoded input (by simp) with ⟨meaning,observed⟩
      first | exact FloatCalculation.negate_total observed | exact FloatCalculation.absolute_total observed
  | add | subtract | multiply | divide =>
      have pair : ∃ a b, inputs = [a,b] := ⟨_,_,List.eq_getElem_of_length_eq_two inputs arity⟩
      rcases pair with ⟨a,b,rfl⟩
      rcases decoded a (by simp) with ⟨meaningA,left⟩
      rcases decoded b (by simp) with ⟨meaningB,right⟩
      first
      | exact FloatCalculation.add_total left right
      | exact FloatCalculation.subtract_total left right
      | exact FloatCalculation.multiply_total left right
      | exact FloatCalculation.divide_total left right
  | fusedMultiplyAdd =>
      have triple : ∃ a b c, inputs = [a,b,c] := ⟨_,_,_,List.eq_getElem_of_length_eq_three inputs arity⟩
      rcases triple with ⟨a,b,c,rfl⟩
      rcases decoded a (by simp) with ⟨meaningA,left⟩
      rcases decoded b (by simp) with ⟨meaningB,right⟩
      rcases decoded c (by simp) with ⟨meaningC,addend⟩
      exact FloatCalculation.fused_total left right addend

namespace Execution

theorem PrimitiveCalculation.floating_nonsqrt_total (target : TargetProfile) (width : FloatWidth)
    (operation : FloatOperation) (inputs : List Nat) (arity : inputs.length = FloatArity operation)
    (valid : ∀ bits ∈ inputs, (decodeFloat width bits).isSome = true) (nonsqrt : operation ≠ .squareRoot) :
    ∃ result, PrimitiveCalculation target (.floating operation width) [] (inputs.map (.floating width))
      (.ok (.floating width result)) ∧ (ScalarValue.floating width result).Valid target := by
  rcases FloatCalculation.nonsqrt_total width operation inputs arity valid nonsqrt with ⟨result,calculated⟩
  exact ⟨result,.floating arity calculated,calculated.valid⟩

theorem ScalarConversion.integer_float_total {target : TargetProfile} {sign : Bool} {width : Width} {value : Int}
    (range : IntegerRange target sign width value) (policy : ConversionPolicy) (destination : FloatWidth) :
    ∃ result, ScalarConversion target policy (.integer sign width value) (.floating destination) result := by
  rcases Rounded.total destination ⟨value,1⟩ false (by change 0 < (1 : Nat); decide) with ⟨bits,rounded⟩
  exact ScalarConversion.integer_float_of_rounded range policy rounded

theorem ScalarConversion.float_total {target : TargetProfile} {sourceWidth : FloatWidth} {bits : Nat}
    (valid : (ScalarValue.floating sourceWidth bits).Valid target) (policy : ConversionPolicy) (destination : FloatWidth) :
    ∃ result, ScalarConversion target policy (.floating sourceWidth bits) (.floating destination) result := by
  cases decoded : decodeFloat sourceWidth bits with
  | none => simp [ScalarValue.Valid,decoded] at valid
  | some meaning =>
      cases meaning with
      | infinity _ => exact ScalarConversion.nonfinite_float_total decoded rfl policy
      | nan => exact ScalarConversion.nonfinite_float_total decoded rfl policy
      | finite sign significand exponent =>
          rcases Rounded.total destination _ sign (binaryFraction.valid sign significand exponent) with ⟨resultBits,rounded⟩
          exact ScalarConversion.float_of_rounded decoded policy rounded

/-- Every source/destination pair admitted by the authoritative scalar
conversion signature has a policy-correct normal or fatal outcome. -/
theorem ScalarConversion.total {target : TargetProfile} {source : ScalarValue} {destination : Scalar}
    (valid : source.Valid target) (supported : ScalarConversionSupported source.type destination) (policy : ConversionPolicy) :
    ∃ result, ScalarConversion target policy source destination result := by
  cases destination with
  | integer sign width => exact ScalarConversion.to_integer_total valid policy sign width
  | character =>
      cases source with
      | integer _ _ _ => exact ScalarConversion.to_character_total valid.2 policy
      | floating _ _ => cases supported
      | character _ => cases supported
  | floating width =>
      cases source with
      | integer _ _ _ => exact ScalarConversion.integer_float_total valid.2 policy width
      | floating _ _ => exact ScalarConversion.float_total valid policy width
      | character _ => cases supported

theorem PrimitiveCalculation.convert_total {target : TargetProfile} {source : ScalarValue} {destination : Scalar}
    (valid : source.Valid target) (supported : ScalarConversionSupported source.type destination)
    (destinationValid : destination.Valid target) (policy : ConversionPolicy) :
    ∃ outcome, PrimitiveCalculation target (.scalarConvert policy) [.scalar destination] [source] outcome ∧
      ∀ result, outcome = .ok result → result.Valid target ∧ result.type = destination := by
  rcases ScalarConversion.total valid supported policy with ⟨outcome,converted⟩
  refine ⟨outcome,.convert converted,?_⟩
  intro result same
  subst outcome
  exact ⟨converted.valid destinationValid,converted.type⟩

end Execution
end Glorious.Language
