import GloriousLanguage.Primitives

/-! General outcome and validity theorems for the authoritative machine-scalar
relations. These do not identify a trapping machine leaf with a source-library
checked conversion or assume that a prospective result is well typed. -/
namespace Glorious.Language

theorem Scalar.integer_bits_positive {target : TargetProfile} {sign : Bool} {width : Width}
    (valid : (Scalar.integer sign width).Valid target) : 0 < width.bits target := by
  cases width with
  | fixed bits =>
      change bits ∈ [8,16,32,64,128] at valid
      change 0 < bits
      simp only [List.mem_cons,List.not_mem_nil,or_false] at valid
      omega
  | pointer =>
      change target.pointerBits ∈ [16,32,64,128] at valid
      change 0 < target.pointerBits
      simp only [List.mem_cons,List.not_mem_nil,or_false] at valid
      omega

theorem integerWrap.range {target : TargetProfile} {sign : Bool} {width : Width}
    (valid : (Scalar.integer sign width).Valid target) (value : Int) :
    IntegerRange target sign width (integerWrap target sign width value) := by
  have bitsPositive := Scalar.integer_bits_positive valid
  have modulusPositive : (0 : Int) < 2 ^ width.bits target := Int.pow_pos (by decide)
  have halfPositive : (0 : Int) < 2 ^ (width.bits target - 1) := Int.pow_pos (by decide)
  have modulus : (2 : Int) ^ width.bits target = 2 ^ (width.bits target - 1) * 2 := by
    calc
      (2 : Int) ^ width.bits target = 2 ^ ((width.bits target - 1) + 1) := by congr 1; omega
      _ = 2 ^ (width.bits target - 1) * 2 := Int.pow_succ _ _
  have lower := Int.emod_nonneg value (Int.ne_of_gt modulusPositive)
  have upper := Int.emod_lt_of_pos value modulusPositive
  cases sign with
  | false => simpa [IntegerRange,integerWrap] using And.intro lower upper
  | true =>
      simp only [IntegerRange,integerWrap,Bool.true_and,↓reduceIte,decide_eq_true_eq]
      split <;> omega

theorem integerClamp.range {target : TargetProfile} {sign : Bool} {width : Width} (value : Int) :
    IntegerRange target sign width (integerClamp target sign width value) := by
  have modulusPositive : (0 : Int) < 2 ^ width.bits target := Int.pow_pos (by decide)
  have halfPositive : (0 : Int) < 2 ^ (width.bits target - 1) := Int.pow_pos (by decide)
  cases sign <;> simp only [IntegerRange,integerClamp,Bool.false_eq_true,↓reduceIte] <;> omega

theorem IntegerResult.total (target : TargetProfile) (sign : Bool) (width : Width)
    (overflow : Overflow) (value : Int) :
    ∃ result, IntegerResult target sign width overflow value result := by
  classical
  cases overflow with
  | checked =>
      by_cases range : IntegerRange target sign width value
      · exact ⟨_,.checked range⟩
      · exact ⟨_,.overflow range⟩
  | wrapping => exact ⟨_,.wrapping⟩
  | saturating => exact ⟨_,.saturating⟩

theorem IntegerResult.range {target : TargetProfile} {sign : Bool} {width : Width}
    {overflow : Overflow} {value result : Int} (valid : (Scalar.integer sign width).Valid target)
    (calculated : IntegerResult target sign width overflow value (.ok result)) :
    IntegerRange target sign width result := by
  cases calculated with
  | checked range => exact range
  | wrapping => exact integerWrap.range valid value
  | saturating => exact integerClamp.range value

theorem decodeFloat.canonicalNaN (width : FloatWidth) :
    decodeFloat width (canonicalNaN width) = some .nan := by
  cases width <;> decide

theorem Rounded.valid {width : FloatWidth} {exact : Fraction} {zeroSign : Bool} {bits : Nat}
    (rounded : Rounded width exact zeroSign bits) : (decodeFloat width bits).isSome = true := by
  cases rounded with
  | finite rounded =>
      rcases rounded.2.2 with ⟨_,_,_,_,decoded,_⟩
      simp [decoded]
  | overflow _ _ decoded => simp [decoded]

theorem FloatCalculation.valid {width : FloatWidth} {operation : FloatOperation}
    {inputs : List Nat} {result : Nat} (calculated : FloatCalculation width operation inputs result) :
    (decodeFloat width result).isSome = true := by
  induction calculated <;> first
  | assumption
  | apply Rounded.valid; assumption
  | simp_all only [decodeFloat.canonicalNaN,Option.isSome_some]

theorem decodeFloat.infinity_exists (width : FloatWidth) (sign : Bool) :
    ∃ bits, decodeFloat width bits = some (.infinity sign) := by
  refine ⟨(if sign then 2 ^ (width.format.exponentBits + width.format.fractionBits) else 0) +
    (2 ^ width.format.exponentBits - 1) * 2 ^ width.format.fractionBits,?_⟩
  cases width <;> cases sign <;> decide

theorem FloatCalculation.add_infinite_left_total {width : FloatWidth} {a b : Nat}
    {sign : Bool} {other : FloatMeaning}
    (left : decodeFloat width a = some (.infinity sign))
    (right : decodeFloat width b = some other) :
    ∃ result, FloatCalculation width .add [a,b] result := by
  classical
  by_cases nan : other = .nan
  · subst other
    exact ⟨_,.nan ⟨b,by simp,right⟩⟩
  by_cases opposite : other = .infinity (!sign)
  · subst other
    exact ⟨_,.addOppositeInfinity left right⟩
  rcases decodeFloat.infinity_exists width sign with ⟨result,decoded⟩
  exact ⟨result,.addInfinityLeft left right nan opposite decoded⟩

/-- An infinite input forces a multiplication's exceptional result without
any finite-rounding existence hypothesis. -/
theorem FloatCalculation.multiply_infinite_total {width : FloatWidth} {a b : Nat}
    {meaningA meaningB : FloatMeaning}
    (left : decodeFloat width a = some meaningA) (right : decodeFloat width b = some meaningB)
    (infinite : ∃ sign, meaningA = .infinity sign ∨ meaningB = .infinity sign) :
    ∃ result, FloatCalculation width .multiply [a,b] result ∧
      (decodeFloat width result = some .nan ∨
        ∃ sign, decodeFloat width result = some (.infinity sign)) := by
  classical
  cases meaningA with
  | nan => exact ⟨_,.nan ⟨a,by simp,left⟩,Or.inl (decodeFloat.canonicalNaN width)⟩
  | finite sa ma ea =>
      rcases infinite with ⟨sb,impossible | rfl⟩
      · cases impossible
      by_cases zero : ma = 0
      · subst ma
        exact ⟨_,.multiplyZeroInfinity (Or.inl ⟨left,right⟩),Or.inl (decodeFloat.canonicalNaN width)⟩
      rcases decodeFloat.infinity_exists width (sa != sb) with ⟨result,decoded⟩
      exact ⟨result,.multiplyInfinity left right (Or.inr ⟨rfl,Or.inr ⟨ma,ea,zero,rfl⟩⟩) decoded,
        Or.inr ⟨_,decoded⟩⟩
  | infinity sa =>
      cases meaningB with
      | nan => exact ⟨_,.nan ⟨b,by simp,right⟩,Or.inl (decodeFloat.canonicalNaN width)⟩
      | infinity sb =>
          rcases decodeFloat.infinity_exists width (sa != sb) with ⟨result,decoded⟩
          exact ⟨result,.multiplyInfinity left right (Or.inl ⟨rfl,Or.inl rfl⟩) decoded,
            Or.inr ⟨_,decoded⟩⟩
      | finite sb mb eb =>
          by_cases zero : mb = 0
          · subst mb
            exact ⟨_,.multiplyZeroInfinity (Or.inr ⟨right,left⟩),Or.inl (decodeFloat.canonicalNaN width)⟩
          rcases decodeFloat.infinity_exists width (sa != sb) with ⟨result,decoded⟩
          exact ⟨result,.multiplyInfinity left right (Or.inl ⟨rfl,Or.inr ⟨mb,eb,zero,rfl⟩⟩) decoded,
            Or.inr ⟨_,decoded⟩⟩

/-- Every nonfinite FMA input triple has a specified valid result. The only
remaining FMA totality obligation is existence of the single finite rounding. -/
theorem FloatCalculation.fused_nonfinite_total {width : FloatWidth} {a b c : Nat}
    {meaningA meaningB meaningC : FloatMeaning}
    (left : decodeFloat width a = some meaningA) (right : decodeFloat width b = some meaningB)
    (addend : decodeFloat width c = some meaningC)
    (nonfinite : meaningA.fraction = none ∨ meaningB.fraction = none ∨ meaningC.fraction = none) :
    ∃ result, FloatCalculation width .fusedMultiplyAdd [a,b,c] result ∧
      (decodeFloat width result).isSome = true := by
  classical
  suffices outcome : ∃ result, FloatCalculation width .fusedMultiplyAdd [a,b,c] result by
    rcases outcome with ⟨result,calculated⟩
    exact ⟨result,calculated,calculated.valid⟩
  by_cases aNan : meaningA = .nan
  · subst meaningA
    exact ⟨_,.nan ⟨a,by simp,left⟩⟩
  by_cases bNan : meaningB = .nan
  · subst meaningB
    exact ⟨_,.nan ⟨b,by simp,right⟩⟩
  by_cases cNan : meaningC = .nan
  · subst meaningC
    exact ⟨_,.nan ⟨c,by simp,addend⟩⟩
  by_cases productInfinite : ∃ sign, meaningA = .infinity sign ∨ meaningB = .infinity sign
  · rcases FloatCalculation.multiply_infinite_total left right productInfinite with
      ⟨product,multiplied,productNan | ⟨sign,productDecoded⟩⟩
    · have added : FloatCalculation width .add [product,c] (canonicalNaN width) :=
        .nan ⟨product,by simp,productNan⟩
      refine ⟨_,.fusedInfiniteProduct ?_ multiplied added⟩
      rcases productInfinite with ⟨sign,rfl | rfl⟩
      · exact ⟨sign,Or.inl left⟩
      · exact ⟨sign,Or.inr right⟩
    · rcases FloatCalculation.add_infinite_left_total productDecoded addend with ⟨result,added⟩
      refine ⟨result,.fusedInfiniteProduct ?_ multiplied added⟩
      rcases productInfinite with ⟨sign,rfl | rfl⟩
      · exact ⟨sign,Or.inl left⟩
      · exact ⟨sign,Or.inr right⟩
  cases meaningA with
  | nan => exact False.elim (aNan rfl)
  | infinity sign => exact False.elim (productInfinite ⟨sign,Or.inl rfl⟩)
  | finite sa ma ea =>
      cases meaningB with
      | nan => exact False.elim (bNan rfl)
      | infinity sign => exact False.elim (productInfinite ⟨sign,Or.inr rfl⟩)
      | finite sb mb eb =>
          cases meaningC with
          | nan => exact False.elim (cNan rfl)
          | finite _ _ _ => simp [FloatMeaning.fraction] at nonfinite
          | infinity _ => exact ⟨c,.fusedInfiniteAddend left right addend⟩

namespace Execution

theorem IntegerCalculation.binary_total {target : TargetProfile} {sign : Bool} {width : Width}
    (operation : IntegerOperation) (overflow : Overflow) (left right : Int)
    (binary : IntegerArity operation = 2)
    (leftRange : IntegerRange target sign width left) (rightRange : IntegerRange target sign width right) :
    ∃ result, IntegerCalculation target sign width operation overflow [left,right] result := by
  classical
  by_cases divisor : (operation = .divide ∨ operation = .remainder) ∧ right = 0
  · rcases divisor with ⟨operationZero,rfl⟩
    exact ⟨_,.zeroDivisor operationZero leftRange⟩
  by_cases shift : (operation = .shiftLeft ∨ operation = .shiftRight) ∧
      (right < 0 ∨ Int.ofNat (width.bits target) ≤ right)
  · exact ⟨_,.invalidShift shift.1 leftRange rightRange shift.2⟩
  have shiftRange : operation = .shiftLeft ∨ operation = .shiftRight →
      0 ≤ right ∧ right < width.bits target := by
    intro operationShift
    have notBad : ¬ (right < 0 ∨ Int.ofNat (width.bits target) ≤ right) :=
      fun bad => shift ⟨operationShift,bad⟩
    change ¬ (right < 0 ∨ (width.bits target : Int) ≤ right) at notBad
    omega
  have calculated : ∃ raw, integerOperation operation left right = some raw := by
    cases operation <;> simp_all [integerOperation,IntegerArity]
  rcases calculated with ⟨raw,calculated⟩
  rcases IntegerResult.total target sign width overflow raw with ⟨result,resultCalculation⟩
  exact ⟨result,.binary binary leftRange rightRange shiftRange calculated resultCalculation⟩

/-- Every declared integer arity has a normal or explicitly fatal outcome.
Division by zero and invalid shifts are part of that outcome, not stuck states. -/
theorem IntegerCalculation.total {target : TargetProfile} {sign : Bool} {width : Width}
    (operation : IntegerOperation) (overflow : Overflow) (inputs : List Int)
    (arity : inputs.length = IntegerArity operation)
    (ranges : ∀ input ∈ inputs, IntegerRange target sign width input) :
    ∃ result, IntegerCalculation target sign width operation overflow inputs result := by
  classical
  by_cases unary : operation = .negate
  · subst operation
    have length : inputs.length = 1 := by simpa [IntegerArity] using arity
    rcases List.length_eq_one_iff.mp length with ⟨input,rfl⟩
    rcases IntegerResult.total target sign width overflow (-input) with ⟨result,calculated⟩
    exact ⟨result,.unary (ranges input (by simp)) calculated⟩
  · have binary : IntegerArity operation = 2 := by simp [IntegerArity,unary]
    have length : inputs.length = 2 := arity.trans binary
    cases inputs with
    | nil => simp at length
    | cons left rest =>
        have restLength : rest.length = 1 := by simpa using length
        rcases List.length_eq_one_iff.mp restLength with ⟨right,rfl⟩
        exact IntegerCalculation.binary_total operation overflow left right binary
          (ranges left (by simp)) (ranges right (by simp))

theorem IntegerCalculation.range {target : TargetProfile} {sign : Bool} {width : Width}
    {operation : IntegerOperation} {overflow : Overflow} {inputs : List Int} {result : Int}
    (valid : (Scalar.integer sign width).Valid target)
    (calculated : IntegerCalculation target sign width operation overflow inputs (.ok result)) :
    IntegerRange target sign width result := by
  cases calculated with
  | binary _ _ _ _ _ result => exact result.range valid
  | unary _ result => exact result.range valid

theorem IntegerCalculation.nonempty {target : TargetProfile} {sign : Bool} {width : Width}
    {operation : IntegerOperation} {overflow : Overflow} {inputs : List Int} {result : Except Fatal Int}
    (calculated : IntegerCalculation target sign width operation overflow inputs result) : inputs ≠ [] := by
  cases calculated <;> simp

theorem ScalarConversion.type {target : TargetProfile} {source result : ScalarValue} {destination : Scalar}
    (calculated : ScalarConversion target source destination (.ok result)) : result.type = destination := by
  cases calculated <;> rfl

theorem ScalarConversion.valid {target : TargetProfile} {source result : ScalarValue} {destination : Scalar}
    (destinationValid : destination.Valid target)
    (calculated : ScalarConversion target source destination (.ok result)) : result.Valid target := by
  cases calculated with
  | integer _ range => exact ⟨destinationValid,range⟩
  | integerFloat _ rounded => exact rounded.valid
  | floatInteger _ _ _ range => exact ⟨destinationValid,range⟩
  | float _ rounded => exact rounded.valid
  | floatInfinity _ decoded => simp [ScalarValue.Valid,decoded]
  | floatNaN _ => simp [ScalarValue.Valid,decodeFloat.canonicalNaN]
  | character _ scalar _ => exact scalar
  | characterInteger _ range => exact ⟨destinationValid,range⟩

/-- Character narrowing is total at the machine leaf: range failure is an
arithmetic fault, not absence of a transition. This does not add an unchecked
source `As<char>` instance or identify that fault with a library Result. -/
theorem ScalarConversion.character_integer_total {target : TargetProfile} {value : Nat}
    (valid : Source.UnicodeScalar value) (sign : Bool) (width : Width) :
    ∃ result, ScalarConversion target (.character value) (.integer sign width) result := by
  classical
  by_cases range : IntegerRange target sign width value
  · exact ⟨_,.characterInteger valid range⟩
  · exact ⟨_,.characterIntegerOverflow valid range⟩

theorem PrimitiveCalculation.integer_total {target : TargetProfile} {sign : Bool} {width : Width}
    (valid : (Scalar.integer sign width).Valid target)
    (operation : IntegerOperation) (overflow : Overflow) (inputs : List Int)
    (arity : inputs.length = IntegerArity operation)
    (ranges : ∀ input ∈ inputs, IntegerRange target sign width input) :
    ∃ outcome, PrimitiveCalculation target (.integer operation sign width overflow) []
        (inputs.map (.integer sign width)) outcome ∧
      ∀ result, outcome = .ok result → result.Valid target ∧ result.type = .integer sign width := by
  rcases IntegerCalculation.total operation overflow inputs arity ranges with ⟨outcome,calculated⟩
  cases outcome with
  | error reason => exact ⟨_,.integerFault calculated,by intro result impossible; cases impossible⟩
  | ok integer =>
      refine ⟨_,.integer calculated,?_⟩
      intro result equal
      cases equal
      exact ⟨⟨valid,calculated.range valid⟩,rfl⟩

/-- Validity follows from the operand and destination type inputs, including
rounding and exceptional float operations. No post-result typing is assumed. -/
theorem PrimitiveCalculation.valid {target : TargetProfile} {primitive : Primitive}
    {arguments : List Term} {inputs : List ScalarValue} {result : ScalarValue}
    (inputsValid : ∀ input ∈ inputs, input.Valid target)
    (destinationsValid : ∀ destination, .scalar destination ∈ arguments → destination.Valid target)
    (calculated : PrimitiveCalculation target primitive arguments inputs (.ok result)) : result.Valid target := by
  cases calculated with
  | integer calculated =>
      have nonempty := calculated.nonempty
      rename_i _ sign width _ integers integer
      cases integers with
      | nil => exact False.elim (nonempty rfl)
      | cons first rest =>
          have valid := inputsValid (.integer sign width first) (by simp)
          exact ⟨valid.1,calculated.range valid.1⟩
  | floating _ calculated => exact calculated.valid
  | equal _ _ _ flag | less _ _ _ flag =>
      rcases flag with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;>
        simp [ScalarValue.Valid,Scalar.Valid,IntegerRange,Width.bits]
  | convert calculated => exact calculated.valid (destinationsValid _ (by simp))

end Execution
end Glorious.Language
