import GloriousLanguage.FloatSqrt

/-! Uniqueness of floating outcomes follows from the authoritative rounding
and square-root relations, including tie parity and signed zero. -/
namespace Glorious.Language

theorem FiniteGrid.unique (points : Nat → Nat) (last denominator : Nat) (numerator : Int)
    (positive : 0 < denominator)
    (increasing : ∀ left right, left < right → right ≤ last → points left < points right)
    {left right : Nat} (leftBound : left ≤ last) (rightBound : right ≤ last)
    (leftNearest : ∀ other, other ≤ last → FiniteGrid.distance points denominator numerator left ≤ FiniteGrid.distance points denominator numerator other)
    (rightNearest : ∀ other, other ≤ last → FiniteGrid.distance points denominator numerator right ≤ FiniteGrid.distance points denominator numerator other)
    (leftEven : ∀ other, other ≤ last → other ≠ left →
      FiniteGrid.distance points denominator numerator left = FiniteGrid.distance points denominator numerator other → left % 2 = 0)
    (rightEven : ∀ other, other ≤ last → other ≠ right →
      FiniteGrid.distance points denominator numerator right = FiniteGrid.distance points denominator numerator other → right % 2 = 0) :
    left = right := by
  by_cases same : left = right
  · exact same
  have equalDistance := Nat.le_antisymm (leftNearest right rightBound) (rightNearest left leftBound)
  have evenLeft := leftEven right rightBound (Ne.symm same) equalDistance
  have evenRight := rightEven left leftBound same equalDistance.symm
  by_cases ordered : left < right
  · have middleBound : left + 1 ≤ last := by omega
    have first := Nat.mul_lt_mul_of_pos_right (increasing left (left + 1) (by omega) middleBound) positive
    have second := Nat.mul_lt_mul_of_pos_right (increasing (left + 1) right (by omega) rightBound) positive
    have closer := FiniteGrid.distance_between (Int.ofNat_lt.mpr first) (Int.ofNat_lt.mpr second) equalDistance
    have nearest := leftNearest (left + 1) middleBound
    exact False.elim (Nat.not_lt_of_ge nearest closer)
  · have middleBound : right + 1 ≤ last := by omega
    have first := Nat.mul_lt_mul_of_pos_right (increasing right (right + 1) (by omega) middleBound) positive
    have second := Nat.mul_lt_mul_of_pos_right (increasing (right + 1) left (by omega) leftBound) positive
    have closer := FiniteGrid.distance_between (Int.ofNat_lt.mpr first) (Int.ofNat_lt.mpr second) equalDistance.symm
    have nearest := rightNearest (right + 1) middleBound
    exact False.elim (Nat.not_lt_of_ge nearest closer)

theorem Fraction.Le.antisymm {left right : Fraction} (first : left.Le right) (second : right.Le left) :
    left.Equal right := ⟨first.1,first.2.1,Int.le_antisymm first.2.2 second.2.2⟩

theorem Fraction.distance_le_common_rev {exact left right : Fraction} {x y : Int} {denominator : Nat}
    (valid : exact.Valid) (leftRep : left.Equal ⟨x,denominator⟩) (rightRep : right.Equal ⟨y,denominator⟩)
    (ordered : (exact.subtract left).absolute.Le (exact.subtract right).absolute) :
    (exact.numerator * denominator - x * exact.denominator).natAbs ≤
      (exact.numerator * denominator - y * exact.denominator).natAbs := by
  have leftCross := Fraction.distance_cross (exact := exact) leftRep
  have rightCross := Fraction.distance_cross (exact := exact) rightRep
  have cross := ordered.2.2
  change ((exact.subtract left).numerator.natAbs : Int) * (exact.denominator * right.denominator : Nat) ≤
    ((exact.subtract right).numerator.natAbs : Int) * (exact.denominator * left.denominator : Nat) at cross
  simp only [← Int.natCast_mul,Int.ofNat_le] at cross
  apply Nat.le_of_mul_le_mul_right (c := left.denominator * (exact.denominator * right.denominator)) _
    (Nat.mul_pos leftRep.1 (Nat.mul_pos valid rightRep.1))
  calc
    (exact.numerator * denominator - x * exact.denominator).natAbs *
        (left.denominator * (exact.denominator * right.denominator)) =
        ((exact.subtract left).numerator.natAbs * denominator) * (exact.denominator * right.denominator) := by
          rw [leftCross]; ac_rfl
    _ = ((exact.subtract left).numerator.natAbs * (exact.denominator * right.denominator)) * denominator := by ac_rfl
    _ ≤ ((exact.subtract right).numerator.natAbs * (exact.denominator * left.denominator)) * denominator :=
      Nat.mul_le_mul_right denominator cross
    _ = ((exact.subtract right).numerator.natAbs * denominator) * (exact.denominator * left.denominator) := by ac_rfl
    _ = (exact.numerator * denominator - y * exact.denominator).natAbs *
        (left.denominator * (exact.denominator * right.denominator)) := by rw [rightCross]; ac_rfl

theorem FloatLattice.encode_injective (width : FloatWidth) (negative : Bool) {left right : Nat}
    (equal : FloatLattice.encode width negative left = FloatLattice.encode width negative right) : left = right := by
  exact Nat.add_left_cancel equal

theorem decodeFloat.finite_injective {width : FloatWidth} {left right significand : Nat} {sign : Bool} {exponent : Int}
    (first : decodeFloat width left = some (.finite sign significand exponent))
    (second : decodeFloat width right = some (.finite sign significand exponent)) : left = right := by
  rcases FloatLattice.finite_code first with ⟨firstCode,_,firstEncoding,firstSignificand,firstExponent⟩
  rcases FloatLattice.finite_code second with ⟨secondCode,_,secondEncoding,secondSignificand,secondExponent⟩
  have sameSignificand := firstSignificand.symm.trans secondSignificand
  have samePower : FloatLattice.power width firstCode = FloatLattice.power width secondCode := by omega
  have sameUnits : FloatLattice.units width.format.fractionBits firstCode = FloatLattice.units width.format.fractionBits secondCode := by
    rw [FloatLattice.units_significand,FloatLattice.units_significand,sameSignificand,samePower]
  have sameCode := FloatLattice.units_injective width.format.fractionBits sameUnits
  rw [firstEncoding,secondEncoding,sameCode]

theorem decodeFloat.zero_encoding {width : FloatWidth} {bits : Nat} {sign : Bool} {exponent : Int}
    (decoded : decodeFloat width bits = some (.finite sign 0 exponent)) : bits = FloatLattice.encode width sign 0 := by
  rcases FloatLattice.finite_code decoded with ⟨code,_,encoding,significand,_⟩
  have zero := (FloatLattice.significand_zero width code).mp significand.symm
  rw [encoding,zero]

theorem decodeFloat.zero_injective {width : FloatWidth} {left right : Nat} {sign : Bool} {leftExponent rightExponent : Int}
    (first : decodeFloat width left = some (.finite sign 0 leftExponent))
    (second : decodeFloat width right = some (.finite sign 0 rightExponent)) : left = right := by
  rw [decodeFloat.zero_encoding first,decodeFloat.zero_encoding second]

theorem decodeFloat.infinity_encoding {width : FloatWidth} {bits : Nat} {sign : Bool}
    (decoded : decodeFloat width bits = some (.infinity sign)) :
    bits = FloatLattice.encode width sign (FloatLattice.cutoff width) := by
  unfold decodeFloat at decoded
  dsimp only at decoded
  split at decoded
  · contradiction
  · split at decoded
    · split at decoded
      · simp only [Option.some.injEq,FloatMeaning.infinity.injEq] at decoded
        cases width <;> cases sign <;>
          simp [FloatLattice.encode,FloatLattice.cutoff,FloatLattice.signMask,FloatLattice.base,FloatWidth.format] at * <;>
          omega
      · simp at decoded
    · split at decoded <;> simp at decoded

theorem decodeFloat.infinity_injective {width : FloatWidth} {left right : Nat} {sign : Bool}
    (first : decodeFloat width left = some (.infinity sign))
    (second : decodeFloat width right = some (.infinity sign)) : left = right := by
  rw [decodeFloat.infinity_encoding first,decodeFloat.infinity_encoding second]

/-- Nearestness against zero forces the prescribed sign on every result,
not only the explicit zero-result branch of the rounding definition. -/
theorem RoundsFinite.sign {width : FloatWidth} {exact : Fraction} {negativeZero sign : Bool} {bits significand : Nat}
    {exponent : Int} (rounded : RoundsFinite width exact negativeZero bits)
    (decoded : decodeFloat width bits = some (.finite sign significand exponent)) :
    sign = FloatLattice.roundingSign exact.numerator negativeZero := by
  rcases rounded with ⟨valid,_,actualSign,actualSignificand,actualExponent,value,actualDecoded,rfl,zeroSign,nearest,_⟩
  have same := decoded.symm.trans actualDecoded
  simp only [Option.some.injEq,FloatMeaning.finite.injEq] at same
  rcases same with ⟨rfl,rfl,rfl⟩
  by_cases zero : significand = 0
  · exact zeroSign zero
  · rcases FloatLattice.finite_code actualDecoded with ⟨code,_,rfl,rfl,rfl⟩
    by_cases sameSign : sign = FloatLattice.roundingSign exact.numerator negativeZero
    · exact sameSign
    · let selectedSign := FloatLattice.roundingSign exact.numerator negativeZero
      let scale := 2^FloatLattice.scale width
      have opposite : sign = !selectedSign := Bool.eq_not_of_ne sameSign
      have aligned := FloatLattice.roundingSign_aligned exact.numerator negativeZero scale
      have cutoffPositive : 0 < FloatLattice.cutoff width := by cases width <;> decide
      have zeroDecoded := FloatLattice.decode_encode width selectedSign 0 cutoffPositive
      have zeroNearest := nearest (FloatLattice.encode width selectedSign 0) selectedSign
        (FloatLattice.significand width 0) ((FloatLattice.power width 0 : Int) - FloatLattice.scale width) zeroDecoded
      have order := Fraction.distance_le_common_rev valid
        (FloatLattice.common width sign code) (FloatLattice.common width selectedSign 0) zeroNearest
      change (exact.numerator * scale - FloatLattice.signed sign
          (FloatLattice.units width.format.fractionBits code) * exact.denominator).natAbs ≤
        (exact.numerator * scale - FloatLattice.signed selectedSign
          (FloatLattice.units width.format.fractionBits 0) * exact.denominator).natAbs at order
      rw [opposite,FloatLattice.opposite_scaled _ _ _ aligned] at order
      have unitsZero : FloatLattice.units width.format.fractionBits 0 = 0 := by simp [FloatLattice.units]
      rw [unitsZero] at order
      simp [FloatLattice.signed,Int.natAbs_mul] at order
      have codeNonzero : code ≠ 0 := by
        intro zeroCode
        exact zero ((FloatLattice.significand_zero width code).mpr zeroCode)
      have unitsPositive : 0 < FloatLattice.units width.format.fractionBits code := by
        have strict := FloatLattice.units_increasing width.format.fractionBits 0 code (by omega)
        rwa [unitsZero] at strict
      have multiplied := Nat.mul_pos unitsPositive valid
      omega

/-- Every actual finite rounding derivation projects to the same signed
IEEE lattice and the same nearest/even obligations used for existence. -/
theorem RoundsFinite.lattice {width : FloatWidth} {exact : Fraction} {negativeZero : Bool} {bits : Nat}
    (rounded : RoundsFinite width exact negativeZero bits) :
    ∃ selected, selected < FloatLattice.cutoff width ∧
      bits = FloatLattice.encode width (FloatLattice.roundingSign exact.numerator negativeZero) selected ∧
      (∀ code, code < FloatLattice.cutoff width →
        FiniteGrid.distance (FloatLattice.units width.format.fractionBits) exact.denominator
          ((exact.numerator.natAbs * 2^FloatLattice.scale width : Nat) : Int) selected ≤
        FiniteGrid.distance (FloatLattice.units width.format.fractionBits) exact.denominator
          ((exact.numerator.natAbs * 2^FloatLattice.scale width : Nat) : Int) code) ∧
      (∀ code, code < FloatLattice.cutoff width → code ≠ selected →
        FiniteGrid.distance (FloatLattice.units width.format.fractionBits) exact.denominator
          ((exact.numerator.natAbs * 2^FloatLattice.scale width : Nat) : Int) selected =
        FiniteGrid.distance (FloatLattice.units width.format.fractionBits) exact.denominator
          ((exact.numerator.natAbs * 2^FloatLattice.scale width : Nat) : Int) code → selected % 2 = 0) := by
  rcases rounded.2.2 with ⟨sign,significand,exponent,value,decoded,rfl,_,nearest,even⟩
  have correctSign := rounded.sign decoded
  subst sign
  rcases FloatLattice.finite_code decoded with ⟨selected,selectedBound,rfl,rfl,rfl⟩
  let negative := FloatLattice.roundingSign exact.numerator negativeZero
  let scale := 2^FloatLattice.scale width
  let points := FloatLattice.units width.format.fractionBits
  let distance := FiniteGrid.distance points exact.denominator ((exact.numerator.natAbs * scale : Nat) : Int)
  have normalized : ∀ code,
      (exact.numerator * scale - FloatLattice.signed negative (points code) * exact.denominator).natAbs = distance code := by
    intro code
    exact FloatLattice.distance_scaled _ _ _ (FloatLattice.roundingSign_aligned _ _ _)
  refine ⟨selected,selectedBound,rfl,?_,?_⟩
  · intro code codeBound
    have otherDecoded := FloatLattice.decode_encode width negative code codeBound
    have actual := nearest _ negative (FloatLattice.significand width code)
      ((FloatLattice.power width code : Int) - FloatLattice.scale width) otherDecoded
    have projected := Fraction.distance_le_common_rev rounded.1
      (FloatLattice.common width negative selected) (FloatLattice.common width negative code) actual
    change (exact.numerator * scale - FloatLattice.signed negative (points selected) * exact.denominator).natAbs ≤
      (exact.numerator * scale - FloatLattice.signed negative (points code) * exact.denominator).natAbs at projected
    simpa only [normalized] using projected
  · intro code codeBound different equalDistance
    rw [← FloatLattice.significand_parity width selected]
    have otherDecoded := FloatLattice.decode_encode width negative code codeBound
    apply even _ negative (FloatLattice.significand width code)
      ((FloatLattice.power width code : Int) - FloatLattice.scale width)
    · intro sameBits
      exact different (FloatLattice.encode_injective width negative sameBits)
    · exact otherDecoded
    · exact Or.inr rfl
    · apply Fraction.Le.antisymm
      · apply Fraction.distance_le_common rounded.1 (FloatLattice.common width negative selected) (FloatLattice.common width negative code)
        change (exact.numerator * scale - FloatLattice.signed negative (points selected) * exact.denominator).natAbs ≤
          (exact.numerator * scale - FloatLattice.signed negative (points code) * exact.denominator).natAbs
        rw [normalized,normalized]
        exact Nat.le_of_eq equalDistance
      · apply Fraction.distance_le_common rounded.1 (FloatLattice.common width negative code) (FloatLattice.common width negative selected)
        change (exact.numerator * scale - FloatLattice.signed negative (points code) * exact.denominator).natAbs ≤
          (exact.numerator * scale - FloatLattice.signed negative (points selected) * exact.denominator).natAbs
        rw [normalized,normalized]
        exact Nat.le_of_eq equalDistance.symm

theorem RoundsFinite.deterministic {width : FloatWidth} {exact : Fraction} {negativeZero : Bool} {left right : Nat}
    (first : RoundsFinite width exact negativeZero left) (second : RoundsFinite width exact negativeZero right) : left = right := by
  rcases first.lattice with ⟨leftCode,leftBound,leftEncoding,leftNearest,leftEven⟩
  rcases second.lattice with ⟨rightCode,rightBound,rightEncoding,rightNearest,rightEven⟩
  have cutoffPositive : 0 < FloatLattice.cutoff width := by cases width <;> decide
  have sameCode := FiniteGrid.unique (FloatLattice.units width.format.fractionBits) (FloatLattice.cutoff width - 1)
    exact.denominator ((exact.numerator.natAbs * 2^FloatLattice.scale width : Nat) : Int) first.1
    (fun left right ordered _ => FloatLattice.units_increasing _ left right ordered)
    (left := leftCode) (right := rightCode) (by omega) (by omega)
    (fun code bounded => leftNearest code (by omega)) (fun code bounded => rightNearest code (by omega))
    (fun code bounded => leftEven code (by omega)) (fun code bounded => rightEven code (by omega))
  rw [leftEncoding,rightEncoding,sameCode]

theorem Rounded.deterministic {width : FloatWidth} {exact : Fraction} {negativeZero : Bool} {left right : Nat}
    (first : Rounded width exact negativeZero left) (second : Rounded width exact negativeZero right) : left = right := by
  cases first with
  | finite first =>
      cases second with
      | finite second => exact first.deterministic second
      | overflow _ overflow _ => exact False.elim (first.2.1 overflow)
  | overflow _ overflow first =>
      cases second with
      | finite second => exact False.elim (second.2.1 overflow)
      | overflow _ _ second => exact decodeFloat.infinity_injective first second

theorem RoundedConversion.ok_rounded {width : FloatWidth} {policy : ConversionPolicy} {exact : Fraction}
    {negativeZero : Bool} {bits : Nat} (converted : RoundedConversion width policy exact negativeZero (.ok bits)) :
    Rounded width exact negativeZero bits := by
  cases converted <;> assumption

theorem RoundedConversion.no_fault_after_success {width : FloatWidth} {policy : ConversionPolicy} {exact : Fraction}
    {negativeZero : Bool} {bits : Nat} {reason : Fatal}
    (success : RoundedConversion width policy exact negativeZero (.ok bits))
    (failure : RoundedConversion width policy exact negativeZero (.error reason)) : False := by
  cases success with
  | lossy rounded =>
      cases failure with
      | overflow impossible _ _ => exact impossible rfl
  | checked rounded decoded =>
      cases failure with
      | overflow _ failed otherDecoded =>
          have same := rounded.deterministic failed
          subst_vars
          simp_all
  | exact rounded decoded equal =>
      cases failure with
      | overflow _ failed otherDecoded =>
          have same := rounded.deterministic failed
          subst_vars
          simp_all
      | precisionLoss failed otherDecoded different =>
          have same := rounded.deterministic failed
          subst_vars
          have meanings := decoded.symm.trans otherDecoded
          simp only [Option.some.injEq,FloatMeaning.finite.injEq] at meanings
          rcases meanings with ⟨rfl,rfl,rfl⟩
          exact different equal

theorem RoundedConversion.deterministic {width : FloatWidth} {policy : ConversionPolicy} {exact : Fraction}
    {negativeZero : Bool} {firstResult secondResult : Except Fatal Nat}
    (first : RoundedConversion width policy exact negativeZero firstResult)
    (second : RoundedConversion width policy exact negativeZero secondResult) : firstResult = secondResult := by
  cases firstResult with
  | ok firstBits =>
      cases secondResult with
      | ok secondBits => exact congrArg Except.ok (first.ok_rounded.deterministic second.ok_rounded)
      | error _ => exact False.elim (first.no_fault_after_success second)
  | error _ =>
      cases secondResult with
      | ok _ => exact False.elim (second.no_fault_after_success first)
      | error _ => cases first <;> cases second <;> rfl

theorem FloatCalculation.nan_result {width : FloatWidth} {operation : FloatOperation} {inputs : List Nat} {result : Nat}
    (calculated : FloatCalculation width operation inputs result)
    (nan : ∃ bits ∈ inputs, decodeFloat width bits = some .nan) : result = canonicalNaN width := by
  induction calculated <;> simp_all [List.mem_cons]
  all_goals grind only [decodeFloat.canonicalNaN]

theorem Fraction.Le.refl {value : Fraction} (valid : value.Valid) : value.Le value := ⟨valid,valid,Int.le_refl _⟩

theorem Fraction.Le.square_reflect {left right : Fraction} (leftValid : left.Valid) (rightValid : right.Valid)
    (leftNonnegative : 0 ≤ left.numerator) (rightNonnegative : 0 ≤ right.numerator)
    (square : (left.multiply left).Le (right.multiply right)) : left.Le right := by
  refine ⟨leftValid,rightValid,?_⟩
  have leftProductNonnegative := Int.mul_nonneg leftNonnegative (Int.natCast_nonneg right.denominator)
  have rightProductNonnegative := Int.mul_nonneg rightNonnegative (Int.natCast_nonneg left.denominator)
  have squared : (left.numerator * (right.denominator : Int)) * (left.numerator * right.denominator) ≤
      (right.numerator * (left.denominator : Int)) * (right.numerator * left.denominator) := by
    have cross := square.2.2
    simp only [Fraction.multiply,Int.natCast_mul] at cross
    grind only
  by_cases ordered : left.numerator * right.denominator ≤ right.numerator * left.denominator
  · exact ordered
  · have strict := Int.mul_self_lt_mul_self rightProductNonnegative
      (show right.numerator * (left.denominator : Int) < left.numerator * right.denominator by omega)
    omega

/-- Any two nonnegative rational intervals bracketing the same square root
overlap. Their uniform rounding obligations therefore force the same result. -/
theorem RoundsFinite.sqrt_intervals_unique {width : FloatWidth} {input lower₁ upper₁ lower₂ upper₂ : Fraction} {firstBits secondBits : Nat}
    (nonnegative₁ : 0 ≤ lower₁.numerator) (nonnegative₂ : 0 ≤ lower₂.numerator)
    (ordered₁ : lower₁.Le upper₁) (ordered₂ : lower₂.Le upper₂)
    (lowerSquare₁ : (lower₁.multiply lower₁).Le input) (lowerSquare₂ : (lower₂.multiply lower₂).Le input)
    (upperSquare₁ : input.Le (upper₁.multiply upper₁)) (upperSquare₂ : input.Le (upper₂.multiply upper₂))
    (first : ∀ exact, lower₁.Le exact → exact.Le upper₁ → RoundsFinite width exact false firstBits)
    (second : ∀ exact, lower₂.Le exact → exact.Le upper₂ → RoundsFinite width exact false secondBits) : firstBits = secondBits := by
  classical
  have cross₁ := Fraction.Le.square_reflect ordered₁.1 ordered₂.2.1 nonnegative₁ (ordered₂.nonnegative nonnegative₂)
    (lowerSquare₁.trans upperSquare₂)
  have cross₂ := Fraction.Le.square_reflect ordered₂.1 ordered₁.2.1 nonnegative₂ (ordered₁.nonnegative nonnegative₁)
    (lowerSquare₂.trans upperSquare₁)
  by_cases ordered : lower₁.Le lower₂
  · exact (first lower₂ ordered cross₂).deterministic (second lower₂ (.refl ordered₂.1) ordered₂)
  · have reversed : lower₂.Le lower₁ := by
      refine ⟨ordered₂.1,ordered₁.1,?_⟩
      unfold Fraction.Le at ordered
      simp only [ordered₁.1,ordered₂.1,true_and] at ordered
      omega
    exact (first lower₁ (.refl ordered₁.1) ordered₁).deterministic (second lower₁ reversed cross₁)

theorem FloatCalculation.add_deterministic {width : FloatWidth} {inputs : List Nat} {left right : Nat}
    (first : FloatCalculation width .add inputs left) (second : FloatCalculation width .add inputs right) : left = right := by
  classical
  by_cases nan : ∃ bits ∈ inputs, decodeFloat width bits = some .nan
  · exact (first.nan_result nan).trans (second.nan_result nan).symm
  · cases first <;> cases second <;> simp_all [List.mem_cons]
    all_goals grind only [Rounded.deterministic,decodeFloat.infinity_injective]

theorem FloatCalculation.negate_deterministic {width : FloatWidth} {inputs : List Nat} {left right : Nat}
    (first : FloatCalculation width .negate inputs left) (second : FloatCalculation width .negate inputs right) : left = right := by
  classical
  by_cases nan : ∃ bits ∈ inputs, decodeFloat width bits = some .nan
  · exact (first.nan_result nan).trans (second.nan_result nan).symm
  · cases first <;> cases second <;> simp_all [List.mem_cons]
    all_goals grind only [decodeFloat.finite_injective,decodeFloat.infinity_injective]

theorem FloatCalculation.absolute_deterministic {width : FloatWidth} {inputs : List Nat} {left right : Nat}
    (first : FloatCalculation width .absolute inputs left) (second : FloatCalculation width .absolute inputs right) : left = right := by
  classical
  by_cases nan : ∃ bits ∈ inputs, decodeFloat width bits = some .nan
  · exact (first.nan_result nan).trans (second.nan_result nan).symm
  · cases first <;> cases second <;> simp_all [List.mem_cons]
    all_goals grind only [decodeFloat.finite_injective,decodeFloat.infinity_injective]

theorem FloatCalculation.subtract_deterministic {width : FloatWidth} {inputs : List Nat} {left right : Nat}
    (first : FloatCalculation width .subtract inputs left) (second : FloatCalculation width .subtract inputs right) : left = right := by
  classical
  by_cases nan : ∃ bits ∈ inputs, decodeFloat width bits = some .nan
  · exact (first.nan_result nan).trans (second.nan_result nan).symm
  · cases first <;> cases second <;> simp_all [List.mem_cons]
    all_goals grind only [FloatCalculation.negate_deterministic,FloatCalculation.add_deterministic]

theorem FloatCalculation.multiply_deterministic {width : FloatWidth} {inputs : List Nat} {left right : Nat}
    (first : FloatCalculation width .multiply inputs left) (second : FloatCalculation width .multiply inputs right) : left = right := by
  classical
  by_cases nan : ∃ bits ∈ inputs, decodeFloat width bits = some .nan
  · exact (first.nan_result nan).trans (second.nan_result nan).symm
  · cases first <;> cases second <;> simp_all [List.mem_cons]
    all_goals grind only [Rounded.deterministic,decodeFloat.infinity_injective]

theorem FloatCalculation.divide_deterministic {width : FloatWidth} {inputs : List Nat} {left right : Nat}
    (first : FloatCalculation width .divide inputs left) (second : FloatCalculation width .divide inputs right) : left = right := by
  classical
  by_cases nan : ∃ bits ∈ inputs, decodeFloat width bits = some .nan
  · exact (first.nan_result nan).trans (second.nan_result nan).symm
  · cases first <;> cases second <;> simp_all [List.mem_cons]
    all_goals grind only [Rounded.deterministic,decodeFloat.infinity_injective,decodeFloat.finite_injective,decodeFloat.zero_injective]

theorem FloatCalculation.sqrt_deterministic {width : FloatWidth} {inputs : List Nat} {left right : Nat}
    (first : FloatCalculation width .squareRoot inputs left) (second : FloatCalculation width .squareRoot inputs right) : left = right := by
  classical
  by_cases nan : ∃ bits ∈ inputs, decodeFloat width bits = some .nan
  · exact (first.nan_result nan).trans (second.nan_result nan).symm
  · cases first <;> cases second <;> simp_all [List.mem_cons]
    all_goals try solve | grind only
    apply RoundsFinite.sqrt_intervals_unique (firstBits := left) (secondBits := right)
      (first := by assumption) (second := by assumption) <;> assumption

theorem FloatCalculation.fused_deterministic {width : FloatWidth} {inputs : List Nat} {left right : Nat}
    (first : FloatCalculation width .fusedMultiplyAdd inputs left) (second : FloatCalculation width .fusedMultiplyAdd inputs right) : left = right := by
  classical
  by_cases nan : ∃ bits ∈ inputs, decodeFloat width bits = some .nan
  · exact (first.nan_result nan).trans (second.nan_result nan).symm
  · cases first <;> cases second <;> simp_all [List.mem_cons]
    all_goals grind only [Rounded.deterministic,FloatCalculation.multiply_deterministic,FloatCalculation.add_deterministic]

theorem FloatCalculation.deterministic {width : FloatWidth} {operation : FloatOperation} {inputs : List Nat} {left right : Nat}
    (first : FloatCalculation width operation inputs left) (second : FloatCalculation width operation inputs right) : left = right := by
  cases operation with
  | add => exact first.add_deterministic second
  | subtract => exact first.subtract_deterministic second
  | multiply => exact first.multiply_deterministic second
  | divide => exact first.divide_deterministic second
  | negate => exact first.negate_deterministic second
  | absolute => exact first.absolute_deterministic second
  | squareRoot => exact first.sqrt_deterministic second
  | fusedMultiplyAdd => exact first.fused_deterministic second

end Glorious.Language
