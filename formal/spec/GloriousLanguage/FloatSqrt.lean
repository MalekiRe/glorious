import GloriousLanguage.FloatProgress
import Init.Data.Nat.Sqrt

/-! Rational square-root isolation for the existing floating square-root
relation. A nonsquare integer root has rational bounds strictly inside one
integer cell; rescaling that cell avoids every possible floating midpoint. -/
namespace Glorious.Language

theorem Fraction.Equal.symm {left right : Fraction} (equal : left.Equal right) : right.Equal left :=
  ⟨equal.2.1,equal.1,equal.2.2.symm⟩

theorem Fraction.Equal.le {left right : Fraction} (equal : left.Equal right) : left.Le right :=
  ⟨equal.1,equal.2.1,Int.le_of_eq equal.2.2⟩

theorem Fraction.Le.trans {left middle right : Fraction} (first : left.Le middle) (second : middle.Le right) :
    left.Le right := by
  refine ⟨first.1,second.2.1,?_⟩
  by_cases ordered : left.numerator * right.denominator ≤ right.numerator * left.denominator
  · exact ordered
  · have reversed : right.numerator * left.denominator < left.numerator * right.denominator := by omega
    have strict := Int.mul_lt_mul_of_pos_right reversed (Int.ofNat_lt.mpr first.2.1)
    have firstScaled := Int.mul_le_mul_of_nonneg_right first.2.2 (Int.natCast_nonneg right.denominator)
    have secondScaled := Int.mul_le_mul_of_nonneg_right second.2.2 (Int.natCast_nonneg left.denominator)
    grind only

theorem Fraction.absolute_self {value : Fraction} (nonnegative : 0 ≤ value.numerator) : value.absolute = value := by
  cases value with
  | mk numerator denominator =>
      simp only [Fraction.absolute,Int.natAbs_of_nonneg nonnegative]

theorem Fraction.Le.nonnegative {left right : Fraction} (ordered : left.Le right) (nonnegative : 0 ≤ left.numerator) :
    0 ≤ right.numerator := by
  have leftNonnegative := Int.mul_nonneg nonnegative (Int.natCast_nonneg right.denominator)
  have rightNonnegative : 0 ≤ right.numerator * (left.denominator : Int) := Int.le_trans leftNonnegative ordered.2.2
  exact Int.nonneg_of_mul_nonneg_left rightNonnegative (Int.ofNat_lt.mpr ordered.1)

namespace FloatLattice

/-- A conservative representable magnitude bound for square-root witnesses,
strictly below overflow. Its exponent is not another target-format contract. -/
def rootCap (width : FloatWidth) : Nat :=
  2^(scale width + match width with | .single => 64 | .double => 512)

set_option exponentiation.threshold 4096 in
set_option maxRecDepth 4096 in
theorem rootCap_square (width : FloatWidth) :
    units width.format.fractionBits (cutoff width - 1) * 2^scale width < rootCap width * rootCap width := by
  cases width <;> decide

set_option exponentiation.threshold 4096 in
set_option maxRecDepth 4096 in
theorem rootCap_below (width : FloatWidth) :
    ¬ (overflowThreshold width).Le ⟨rootCap width,2^scale width⟩ := by
  unfold Fraction.Le Fraction.Valid
  cases width <;> decide

theorem units_monotone (fractionBits : Nat) {left right : Nat} (ordered : left ≤ right) :
    units fractionBits left ≤ units fractionBits right := by
  by_cases same : left = right
  · subst right
    exact Nat.le_refl _
  · exact Nat.le_of_lt (units_increasing fractionBits left right (by omega))

theorem rootCap_input {width : FloatWidth} {code : Nat} (bounded : code < cutoff width) :
    4 * units width.format.fractionBits code * 2^scale width < (2 * rootCap width) * (2 * rootCap width) := by
  have magnitudeBound := Nat.mul_le_mul_right (2^scale width)
    (units_monotone width.format.fractionBits (show code ≤ cutoff width - 1 by omega))
  have squareBound := Nat.lt_of_le_of_lt magnitudeBound (rootCap_square width)
  have scaled := Nat.mul_lt_mul_of_pos_left squareBound (by decide : 0 < 4)
  have product : (2 * rootCap width) * (2 * rootCap width) = 4 * (rootCap width * rootCap width) := by grind only
  rw [product]
  simpa only [Nat.mul_assoc] using scaled

theorem below_of_rootCap {width : FloatWidth} {exact : Fraction}
    (nonnegative : 0 ≤ exact.numerator) (bounded : exact.Le ⟨rootCap width,2^scale width⟩) :
    ¬ (overflowThreshold width).Le exact.absolute := by
  rw [Fraction.absolute_self nonnegative]
  intro overflow
  exact rootCap_below width (overflow.trans bounded)

end FloatLattice

namespace RootIsolation

def scaled (numerator scale denominator : Nat) : Fraction := ⟨numerator,2 * scale * denominator⟩

theorem scaled_valid (numerator : Nat) {scale denominator : Nat} (scalePositive : 0 < scale) (positive : 0 < denominator) :
    (scaled numerator scale denominator).Valid := Nat.mul_pos (Nat.mul_pos (by decide) scalePositive) positive

theorem scaled_order {lower upper scale denominator : Nat} (scalePositive : 0 < scale) (positive : 0 < denominator)
    (ordered : lower ≤ upper) : (scaled lower scale denominator).Le (scaled upper scale denominator) :=
  ⟨scaled_valid _ scalePositive positive,scaled_valid _ scalePositive positive,
    Int.mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr ordered) (Int.natCast_nonneg _)⟩

theorem scaled_lower {input lower scale denominator : Nat} (scalePositive : 0 < scale) (positive : 0 < denominator)
    (square : lower * lower ≤ (4 * input * scale) * denominator * denominator) :
    ((scaled lower scale denominator).multiply (scaled lower scale denominator)).Le ⟨input,scale⟩ := by
  refine ⟨Fraction.multiply_valid (scaled_valid _ scalePositive positive) (scaled_valid _ scalePositive positive),scalePositive,?_⟩
  change (lower : Int) * lower * scale ≤ (input : Int) * ((2 * scale * denominator) * (2 * scale * denominator) : Nat)
  simp only [← Int.natCast_mul,Int.ofNat_le]
  have multiplied := Nat.mul_le_mul_right scale square
  grind only

theorem scaled_upper {input upper scale denominator : Nat} (scalePositive : 0 < scale) (positive : 0 < denominator)
    (square : (4 * input * scale) * denominator * denominator ≤ upper * upper) :
    (Fraction.mk input scale).Le ((scaled upper scale denominator).multiply (scaled upper scale denominator)) := by
  refine ⟨scalePositive,Fraction.multiply_valid (scaled_valid _ scalePositive positive) (scaled_valid _ scalePositive positive),?_⟩
  change (input : Int) * ((2 * scale * denominator) * (2 * scale * denominator) : Nat) ≤ (upper : Int) * upper * scale
  simp only [← Int.natCast_mul,Int.ofNat_le]
  have multiplied := Nat.mul_le_mul_right scale square
  grind only

theorem scaled_bounded {upper cap scale denominator : Nat} (scalePositive : 0 < scale) (positive : 0 < denominator)
    (bound : upper ≤ (2 * cap) * denominator) : (scaled upper scale denominator).Le ⟨cap,scale⟩ := by
  refine ⟨scaled_valid _ scalePositive positive,scalePositive,?_⟩
  change (upper : Int) * scale ≤ (cap : Int) * (2 * scale * denominator : Nat)
  simp only [← Int.natCast_mul,Int.ofNat_le]
  have multiplied := Nat.mul_le_mul_right scale bound
  grind only

/-- Integer gaps supply strict rational root bounds without real-number
oracles, approximation assumptions, or an unbounded search. -/
theorem bracket (input : Nat) :
    ∃ lower upper denominator : Nat,
      0 < denominator ∧ lower ≤ upper ∧
      lower * lower ≤ input * denominator * denominator ∧
      input * denominator * denominator ≤ upper * upper ∧
      ((lower = upper ∧ denominator = 1) ∨ ∃ cell,
        cell * cell ≤ input ∧ cell * denominator < lower ∧ upper < (cell + 1) * denominator) := by
  let cell := input.sqrt
  have floor : cell * cell ≤ input := Nat.sqrt_le input
  have ceiling : input < (cell + 1) * (cell + 1) := Nat.lt_succ_sqrt input
  by_cases exact : cell * cell = input
  · exact ⟨cell,cell,1,by decide,Nat.le_refl _,by simp [exact],by simp [exact],Or.inl ⟨rfl,rfl⟩⟩
  · let denominator := 2 * cell + 2
    let lower := cell * denominator + 1
    let upper := cell * denominator + (2 * cell + 1)
    have lowerInput : cell * cell + 1 ≤ input := by omega
    have upperInput : input ≤ cell * cell + 2 * cell := by
      simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one] at ceiling
      omega
    have lowerSquare : lower * lower ≤ (cell * cell + 1) * denominator * denominator := by
      dsimp [lower,denominator]
      grind only
    have upperSquare : (cell * cell + 2 * cell) * denominator * denominator ≤ upper * upper := by
      dsimp [upper,denominator]
      grind only
    refine ⟨lower,upper,denominator,by dsimp [denominator]; omega,by dsimp [lower,upper]; omega,
      Nat.le_trans lowerSquare (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ lowerInput)),
      Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ upperInput)) upperSquare,
      Or.inr ⟨cell,floor,by dsimp [lower]; omega,?_⟩⟩
    dsimp [upper,denominator]
    rw [Nat.add_mul,Nat.one_mul]
    omega

end RootIsolation

namespace RoundingCell

def Contains (cell denominator : Nat) (numerator : Int) : Prop :=
  (cell : Int) * denominator < 2 * numerator ∧ 2 * numerator < (cell + 1 : Nat) * denominator

theorem interval {cell scale : Nat} {lower upper exact : Fraction}
    (lowerInside : Contains cell lower.denominator (lower.numerator * scale))
    (upperInside : Contains cell upper.denominator (upper.numerator * scale))
    (lowerBound : lower.Le exact) (upperBound : exact.Le upper) :
    Contains cell exact.denominator (exact.numerator * scale) := by
  constructor
  · have lowerScaled := Int.mul_lt_mul_of_pos_right lowerInside.1 (Int.ofNat_lt.mpr lowerBound.2.1)
    have boundScaled := Int.mul_le_mul_of_nonneg_right lowerBound.2.2
      (show (0 : Int) ≤ 2 * scale from Int.mul_nonneg (by decide) (Int.natCast_nonneg _))
    apply Int.lt_of_mul_lt_mul_right (a := (lower.denominator : Int)) _ (Int.natCast_nonneg _)
    grind only
  · have upperScaled := Int.mul_lt_mul_of_pos_right upperInside.2 (Int.ofNat_lt.mpr upperBound.1)
    have boundScaled := Int.mul_le_mul_of_nonneg_right upperBound.2.2
      (show (0 : Int) ≤ 2 * scale from Int.mul_nonneg (by decide) (Int.natCast_nonneg _))
    apply Int.lt_of_mul_lt_mul_right (a := (upper.denominator : Int)) _ (Int.natCast_nonneg _)
    grind only

theorem scaled_inside {cell numerator scale denominator : Nat} (scalePositive : 0 < scale)
    (lower : cell * denominator < numerator) (upper : numerator < (cell + 1) * denominator) :
    Contains cell (RootIsolation.scaled numerator scale denominator).denominator
      ((RootIsolation.scaled numerator scale denominator).numerator * scale) := by
  have multiplierPositive : 0 < 2 * scale := Nat.mul_pos (by decide) scalePositive
  have lowerScaled := Int.ofNat_lt.mpr (Nat.mul_lt_mul_of_pos_left lower multiplierPositive)
  have upperScaled := Int.ofNat_lt.mpr (Nat.mul_lt_mul_of_pos_left upper multiplierPositive)
  simp only [Int.natCast_mul,Int.natCast_add,RootIsolation.scaled,Contains] at lowerScaled upperScaled ⊢
  constructor <;> grind only

theorem distance_left {point left right : Int} (ordered : left < right) :
    (point - left).natAbs ≤ (point - right).natAbs ↔ 2 * point ≤ left + right := by
  have leftSign := Int.natAbs_eq_iff.mp (rfl : (point - left).natAbs = (point - left).natAbs)
  have rightSign := Int.natAbs_eq_iff.mp (rfl : (point - right).natAbs = (point - right).natAbs)
  rcases leftSign with leftSign | leftSign <;> rcases rightSign with rightSign | rightSign <;> omega

theorem distance_right {point left right : Int} (ordered : left < right) :
    (point - right).natAbs ≤ (point - left).natAbs ↔ left + right ≤ 2 * point := by
  have leftSign := Int.natAbs_eq_iff.mp (rfl : (point - left).natAbs = (point - left).natAbs)
  have rightSign := Int.natAbs_eq_iff.mp (rfl : (point - right).natAbs = (point - right).natAbs)
  rcases leftSign with leftSign | leftSign <;> rcases rightSign with rightSign | rightSign <;> omega

theorem no_midpoint {cell denominator : Nat} {numerator : Int}
    (inside : Contains cell denominator numerator) (midpoint : Nat) :
    2 * numerator ≠ (midpoint : Int) * denominator := by
  rcases inside with ⟨lower,upper⟩
  by_cases below : midpoint ≤ cell
  · have multiplied := Int.ofNat_le.mpr (Nat.mul_le_mul_right denominator below)
    simp only [Int.natCast_mul] at multiplied
    omega
  · have multiplied := Int.ofNat_le.mpr (Nat.mul_le_mul_right denominator (show cell + 1 ≤ midpoint by omega))
    simp only [Int.natCast_mul,Int.natCast_add,Int.natCast_one] at multiplied upper
    omega

/-- Within one open half-unit cell, the ordering of distances to every pair
of integer lattice points agrees with the exact cell center. -/
theorem nearest {cell denominator left right : Nat} {numerator : Int}
    (positive : 0 < denominator) (inside : Contains cell denominator numerator)
    (center : ((2 * cell + 1 : Nat) - (4 * left : Nat) : Int).natAbs ≤
      ((2 * cell + 1 : Nat) - (4 * right : Nat) : Int).natAbs) :
    (numerator - (left * denominator : Nat)).natAbs ≤ (numerator - (right * denominator : Nat)).natAbs := by
  rcases inside with ⟨lower,upper⟩
  by_cases same : left = right
  · simp only [same,Nat.le_refl]
  by_cases ordered : left < right
  · have centerOrder : (4 * left : Nat) < 4 * right := Nat.mul_lt_mul_of_pos_left ordered (by decide)
    have midpoint := (distance_left (Int.ofNat_lt.mpr centerOrder)).mp center
    have integers : cell + 1 ≤ left + right := by
      simp only [Int.natCast_add,Int.natCast_mul] at midpoint
      omega
    have multiplied := Int.ofNat_le.mpr (Nat.mul_le_mul_right denominator integers)
    have orderedScaled := Nat.mul_lt_mul_of_pos_right ordered positive
    apply (distance_left (Int.ofNat_lt.mpr orderedScaled)).mpr
    simp only [Int.natCast_add,Int.natCast_mul] at multiplied upper ⊢
    grind only
  · have reversed : right < left := by omega
    have centerOrder : (4 * right : Nat) < 4 * left := Nat.mul_lt_mul_of_pos_left reversed (by decide)
    have midpoint := (distance_right (Int.ofNat_lt.mpr centerOrder)).mp center
    have integers : left + right ≤ cell := by
      simp only [Int.natCast_add,Int.natCast_mul] at midpoint
      omega
    have multiplied := Int.ofNat_le.mpr (Nat.mul_le_mul_right denominator integers)
    have orderedScaled := Nat.mul_lt_mul_of_pos_right reversed positive
    apply (distance_right (Int.ofNat_lt.mpr orderedScaled)).mpr
    simp only [Int.natCast_add,Int.natCast_mul] at multiplied lower ⊢
    grind only

theorem distinct_distance {cell denominator left right : Nat} {numerator : Int}
    (positive : 0 < denominator) (inside : Contains cell denominator numerator) (different : left ≠ right) :
    (numerator - (left * denominator : Nat)).natAbs ≠ (numerator - (right * denominator : Nat)).natAbs := by
  intro equal
  have midpoint : 2 * numerator = (left + right : Nat) * denominator := by
    by_cases ordered : left < right
    · have scaled := Int.ofNat_lt.mpr (Nat.mul_lt_mul_of_pos_right ordered positive)
      have first := (distance_left scaled).mp (Nat.le_of_eq equal)
      have second := (distance_right scaled).mp (Nat.le_of_eq equal.symm)
      simp only [Int.natCast_add,Int.natCast_mul] at first second ⊢
      grind only
    · have scaled := Int.ofNat_lt.mpr (Nat.mul_lt_mul_of_pos_right (show right < left by omega) positive)
      have first := (distance_left scaled).mp (Nat.le_of_eq equal.symm)
      have second := (distance_right scaled).mp (Nat.le_of_eq equal)
      simp only [Int.natCast_add,Int.natCast_mul] at first second ⊢
      grind only
  exact no_midpoint inside (left + right) midpoint

end RoundingCell

theorem FloatLattice.units_injective (fractionBits : Nat) {left right : Nat}
    (equal : FloatLattice.units fractionBits left = FloatLattice.units fractionBits right) : left = right := by
  by_cases ordered : left < right
  · have strict := FloatLattice.units_increasing fractionBits left right ordered
    omega
  · by_cases reversed : right < left
    · have strict := FloatLattice.units_increasing fractionBits right left reversed
      omega
    · omega

theorem RoundsFinite.of_nonnegative_nearest {width : FloatWidth} {exact : Fraction} {selected : Nat}
    (valid : exact.Valid) (nonnegative : 0 ≤ exact.numerator)
    (below : ¬ (overflowThreshold width).Le exact.absolute)
    (selectedBound : selected < FloatLattice.cutoff width)
    (nearest : ∀ code, code < FloatLattice.cutoff width →
      (exact.numerator * (2^FloatLattice.scale width : Nat) -
        (FloatLattice.units width.format.fractionBits selected * exact.denominator : Nat)).natAbs ≤
      (exact.numerator * (2^FloatLattice.scale width : Nat) -
        (FloatLattice.units width.format.fractionBits code * exact.denominator : Nat)).natAbs)
    (even : ∀ code, code < FloatLattice.cutoff width → code ≠ selected →
      (exact.numerator * (2^FloatLattice.scale width : Nat) -
        (FloatLattice.units width.format.fractionBits selected * exact.denominator : Nat)).natAbs =
      (exact.numerator * (2^FloatLattice.scale width : Nat) -
        (FloatLattice.units width.format.fractionBits code * exact.denominator : Nat)).natAbs → selected % 2 = 0) :
    RoundsFinite width exact false (FloatLattice.encode width false selected) := by
  let denominator := 2^FloatLattice.scale width
  let points := FloatLattice.units width.format.fractionBits
  have scaledNonnegative : 0 ≤ exact.numerator * (denominator : Int) :=
    Int.mul_nonneg nonnegative (Int.natCast_nonneg _)
  have cutoffPositive : 0 < FloatLattice.cutoff width := by cases width <;> decide
  have zeroNearest : (exact.numerator * denominator - (points selected * exact.denominator : Nat)).natAbs ≤
      (exact.numerator * denominator).natAbs := by
    have zero := nearest 0 cutoffPositive
    simpa [points,denominator,FloatLattice.units] using zero
  refine ⟨valid,below,false,FloatLattice.significand width selected,
    (FloatLattice.power width selected : Int) - FloatLattice.scale width,
    FloatLattice.value width false selected,FloatLattice.decode_encode _ _ _ selectedBound,rfl,?_,?_,?_⟩
  · intro _
    by_cases zero : exact.numerator = 0 <;> simp [zero,show ¬ exact.numerator < 0 by omega]
  · intro other otherSign otherSignificand otherExponent decoded
    rcases FloatLattice.finite_code decoded with ⟨code,codeBound,rfl,rfl,rfl⟩
    apply Fraction.distance_le_common valid (FloatLattice.common width false selected) (FloatLattice.common width otherSign code)
    cases otherSign with
    | false =>
        simpa only [FloatLattice.signed,Bool.false_eq_true,↓reduceIte,← Int.natCast_mul] using nearest code codeBound
    | true =>
        change (exact.numerator * denominator - FloatLattice.signed false (points selected) * exact.denominator).natAbs ≤
          (exact.numerator * denominator - FloatLattice.signed (!false) (points code) * exact.denominator).natAbs
        simp only [FloatLattice.signed_mul]
        rw [FloatLattice.opposite_distance _ (show FloatLattice.Aligned false (exact.numerator * denominator) from scaledNonnegative)]
        simp only [FloatLattice.signed,Bool.false_eq_true,↓reduceIte]
        omega
  · intro other otherSign otherSignificand otherExponent different decoded zeroSign equal
    rcases FloatLattice.finite_code decoded with ⟨code,codeBound,rfl,rfl,rfl⟩
    have equalDistance := Fraction.distance_equal_common valid
      (FloatLattice.common width false selected) (FloatLattice.common width otherSign code) equal
    rw [FloatLattice.significand_parity]
    cases otherSign with
    | false =>
        apply even code codeBound
        · intro same
          apply different
          simp only [same]
        · simpa only [FloatLattice.signed,Bool.false_eq_true,↓reduceIte,← Int.natCast_mul] using equalDistance
    | true =>
        have nonzero : code ≠ 0 := by
          rcases zeroSign with nonzero | impossible
          · intro zero
            exact nonzero ((FloatLattice.significand_zero width code).mpr zero)
          · cases impossible
        have pointsPositive : 0 < points code := by
          have increasing := FloatLattice.units_increasing width.format.fractionBits 0 code (by omega)
          simpa [points,FloatLattice.units] using increasing
        change (exact.numerator * denominator - FloatLattice.signed false (points selected) * exact.denominator).natAbs =
          (exact.numerator * denominator - FloatLattice.signed (!false) (points code) * exact.denominator).natAbs at equalDistance
        simp only [FloatLattice.signed_mul] at equalDistance
        rw [FloatLattice.opposite_distance _ (show FloatLattice.Aligned false (exact.numerator * denominator) from scaledNonnegative)] at equalDistance
        simp only [FloatLattice.signed,Bool.false_eq_true,↓reduceIte] at equalDistance
        have positiveProduct := Nat.mul_pos pointsPositive valid
        omega

/-- One decoded nonnegative result rounds every rational in an open
half-subnormal cell, whenever the rational is below the existing overflow
threshold. All possible IEEE pairwise tie midpoints lie outside that cell. -/
theorem RoundsFinite.open_cell (width : FloatWidth) (cell : Nat) :
    ∃ bits significand exponent,
      decodeFloat width bits = some (.finite false significand exponent) ∧
      ∀ exact : Fraction, exact.Valid →
        RoundingCell.Contains cell exact.denominator (exact.numerator * (2^FloatLattice.scale width : Nat)) →
        ¬ (overflowThreshold width).Le exact.absolute → RoundsFinite width exact false bits := by
  classical
  let denominator := 2^FloatLattice.scale width
  let points := FloatLattice.units width.format.fractionBits
  have cutoffPositive : 0 < FloatLattice.cutoff width := by cases width <;> decide
  have denominatorPositive : 0 < denominator := Nat.pow_pos (by decide)
  rcases FiniteGrid.nearest_even points (FloatLattice.cutoff width - 1) 4 ((2 * cell + 1 : Nat) : Int)
      (by decide) (fun left right ordered _ => FloatLattice.units_increasing _ left right ordered) with
    ⟨selected,bounded,nearest,_⟩
  have selectedBound : selected < FloatLattice.cutoff width := by omega
  refine ⟨FloatLattice.encode width false selected,FloatLattice.significand width selected,
    (FloatLattice.power width selected : Int) - FloatLattice.scale width,
    FloatLattice.decode_encode _ _ _ selectedBound,?_⟩
  intro exact valid inside below
  change RoundingCell.Contains cell exact.denominator (exact.numerator * denominator) at inside
  have positiveScaled : 0 < exact.numerator * (denominator : Int) := by
    have lower := inside.1
    have nonnegative : (0 : Int) ≤ (cell : Int) * exact.denominator :=
      Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    omega
  have positiveNumerator : 0 < exact.numerator := by
    by_cases positive : 0 < exact.numerator
    · exact positive
    · have product := Int.mul_nonpos_of_nonpos_of_nonneg (show exact.numerator ≤ 0 by omega) (Int.natCast_nonneg denominator)
      omega
  have actualNearest : ∀ code, code ≤ FloatLattice.cutoff width - 1 →
      (exact.numerator * denominator - (points selected * exact.denominator : Nat)).natAbs ≤
        (exact.numerator * denominator - (points code * exact.denominator : Nat)).natAbs := by
    intro code codeBound
    apply RoundingCell.nearest valid inside
    simpa only [FiniteGrid.distance,Nat.mul_comm] using nearest code codeBound
  apply RoundsFinite.of_nonnegative_nearest valid (Int.le_of_lt positiveNumerator) below selectedBound
  · intro code codeBound
    exact actualNearest code (by omega)
  · intro code _ different equal
    have differentPoints : points selected ≠ points code := by
      intro same
      exact different (FloatLattice.units_injective _ same).symm
    exact False.elim (RoundingCell.distinct_distance valid inside differentPoints equal)

/-- An exact midpoint-grid root is handled as a point interval, including
ties. Equivalent rational representations select the same nearest/even code. -/
theorem RoundsFinite.point (width : FloatWidth) (point : Nat) :
    ∃ bits significand exponent,
      decodeFloat width bits = some (.finite false significand exponent) ∧
      ∀ exact : Fraction, exact.Equal ⟨point,2 * 2^FloatLattice.scale width⟩ →
        ¬ (overflowThreshold width).Le exact.absolute → RoundsFinite width exact false bits := by
  classical
  let denominator := 2^FloatLattice.scale width
  let points := FloatLattice.units width.format.fractionBits
  have cutoffPositive : 0 < FloatLattice.cutoff width := by cases width <;> decide
  have denominatorPositive : 0 < denominator := Nat.pow_pos (by decide)
  rcases FiniteGrid.nearest_even points (FloatLattice.cutoff width - 1) 2 (point : Int)
      (by decide) (fun left right ordered _ => FloatLattice.units_increasing _ left right ordered) with
    ⟨selected,bounded,nearest,even⟩
  have selectedBound : selected < FloatLattice.cutoff width := by omega
  refine ⟨FloatLattice.encode width false selected,FloatLattice.significand width selected,
    (FloatLattice.power width selected : Int) - FloatLattice.scale width,
    FloatLattice.decode_encode _ _ _ selectedBound,?_⟩
  intro exact represented below
  have equation : 2 * (exact.numerator * denominator) = (point : Int) * exact.denominator := by
    have cross := represented.2.2
    change exact.numerator * (2 * denominator : Nat) = (point : Int) * exact.denominator at cross
    simp only [Int.natCast_mul] at cross
    grind only
  have nonnegative : 0 ≤ exact.numerator := by
    have rightNonnegative : (0 : Int) ≤ (point : Int) * exact.denominator :=
      Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    have scaledNonnegative : 0 ≤ exact.numerator * (denominator : Int) := by omega
    exact Int.nonneg_of_mul_nonneg_left scaledNonnegative (Int.ofNat_lt.mpr denominatorPositive)
  have distanceScaled : ∀ code,
      2 * (exact.numerator * denominator - (points code * exact.denominator : Nat)).natAbs =
        FiniteGrid.distance points 2 (point : Int) code * exact.denominator := by
    intro code
    have signed : (2 : Int) * (exact.numerator * denominator - (points code * exact.denominator : Nat)) =
        ((point : Int) - (points code * 2 : Nat)) * exact.denominator := by
      simp only [Int.natCast_mul]
      grind only
    have absolute := congrArg Int.natAbs signed
    simpa [Int.natAbs_mul,FiniteGrid.distance] using absolute
  apply RoundsFinite.of_nonnegative_nearest represented.1 nonnegative below selectedBound
  · intro code codeBound
    apply Nat.le_of_mul_le_mul_left (c := 2) _ (by decide)
    change 2 * (exact.numerator * denominator - (points selected * exact.denominator : Nat)).natAbs ≤
      2 * (exact.numerator * denominator - (points code * exact.denominator : Nat)).natAbs
    rw [distanceScaled,distanceScaled]
    exact Nat.mul_le_mul_right _ (nearest code (by omega))
  · intro code codeBound different equal
    apply even code (by omega) different
    apply Nat.eq_of_mul_eq_mul_right represented.1
    rw [← distanceScaled,← distanceScaled]
    exact congrArg (fun distance => 2 * distance) equal

/-- Every positive finite floating input admits the rational isolating
interval required by the authoritative square-root rule. Exact midpoint-grid
roots use a point interval; all other roots lie strictly inside one tie-free
cell. The entire interval remains below the actual overflow threshold. -/
theorem FloatCalculation.sqrt_finite_total {width : FloatWidth} {input significand : Nat} {exponent : Int}
    (decoded : decodeFloat width input = some (.finite false significand exponent)) (nonzero : significand ≠ 0) :
    ∃ result, FloatCalculation width .squareRoot [input] result := by
  rcases FloatLattice.finite_code decoded with ⟨code,codeBound,_,rfl,rfl⟩
  let magnitude := FloatLattice.units width.format.fractionBits code
  let scale := 2^FloatLattice.scale width
  have scalePositive : 0 < scale := Nat.pow_pos (by decide)
  have represented : (binaryFraction false (FloatLattice.significand width code)
      ((FloatLattice.power width code : Int) - FloatLattice.scale width)).Equal ⟨magnitude,scale⟩ := by
    simpa only [FloatLattice.value,FloatLattice.signed,Bool.false_eq_true,↓reduceIte] using FloatLattice.common width false code
  rcases RootIsolation.bracket (4 * magnitude * scale) with
    ⟨lower,upper,denominator,positive,ordered,lowerSquare,upperSquare,shape⟩
  have inputBound : 4 * magnitude * scale < (2 * FloatLattice.rootCap width) * (2 * FloatLattice.rootCap width) :=
    FloatLattice.rootCap_input codeBound
  have upperBound : upper ≤ (2 * FloatLattice.rootCap width) * denominator := by
    rcases shape with ⟨same,unit⟩ | ⟨cell,floor,_,ceiling⟩
    · rw [unit,Nat.mul_one,Nat.mul_one] at lowerSquare
      have strict := Nat.mul_self_lt_mul_self_iff.mp (Nat.lt_of_le_of_lt lowerSquare inputBound)
      rw [unit,Nat.mul_one,← same]
      omega
    · have strict := Nat.mul_self_lt_mul_self_iff.mp (Nat.lt_of_le_of_lt floor inputBound)
      have scaled := Nat.mul_le_mul_right denominator (show cell + 1 ≤ 2 * FloatLattice.rootCap width by omega)
      omega
  have lowerValid := RootIsolation.scaled_valid lower scalePositive positive
  have upperValid := RootIsolation.scaled_valid upper scalePositive positive
  have intervalOrder := RootIsolation.scaled_order scalePositive positive ordered
  have lowerSquared := (RootIsolation.scaled_lower scalePositive positive lowerSquare).trans represented.symm.le
  have upperSquared := represented.le.trans (RootIsolation.scaled_upper scalePositive positive upperSquare)
  have below : ∀ exact : Fraction,
      (RootIsolation.scaled lower scale denominator).Le exact →
      exact.Le (RootIsolation.scaled upper scale denominator) → ¬ (overflowThreshold width).Le exact.absolute := by
    intro exact lowerBound upperBound'
    apply FloatLattice.below_of_rootCap
    · exact lowerBound.nonnegative (Int.natCast_nonneg lower)
    · exact upperBound'.trans (RootIsolation.scaled_bounded scalePositive positive upperBound)
  rcases shape with ⟨same,unit⟩ | ⟨cell,_,lowerCell,upperCell⟩
  · rcases RoundsFinite.point width lower with ⟨result,resultSignificand,resultExponent,resultDecoded,rounding⟩
    refine ⟨result,.sqrtFinite decoded nonzero resultDecoded lowerValid upperValid intervalOrder
      (Int.natCast_nonneg lower) lowerSquared upperSquared ?_⟩
    intro exact lowerBound upperBound'
    apply rounding exact _ (below exact lowerBound upperBound')
    refine ⟨lowerBound.2.1,Nat.mul_pos (by decide) scalePositive,?_⟩
    have left := lowerBound.2.2
    have right := upperBound'.2.2
    change (lower : Int) * exact.denominator ≤ exact.numerator * (2 * scale * denominator : Nat) at left
    change exact.numerator * (2 * scale * denominator : Nat) ≤ (upper : Int) * exact.denominator at right
    rw [unit,Nat.mul_one] at left right
    rw [← same] at right
    change exact.numerator * (2 * scale : Nat) = (lower : Int) * exact.denominator
    omega
  · rcases RoundsFinite.open_cell width cell with ⟨result,resultSignificand,resultExponent,resultDecoded,rounding⟩
    have lowerInside := RoundingCell.scaled_inside scalePositive lowerCell (show lower < (cell + 1) * denominator by omega)
    have upperInside := RoundingCell.scaled_inside scalePositive (show cell * denominator < upper by omega) upperCell
    refine ⟨result,.sqrtFinite decoded nonzero resultDecoded lowerValid upperValid intervalOrder
      (Int.natCast_nonneg lower) lowerSquared upperSquared ?_⟩
    intro exact lowerBound upperBound'
    apply rounding exact lowerBound.2.1 _ (below exact lowerBound upperBound')
    exact RoundingCell.interval lowerInside upperInside lowerBound upperBound'

theorem FloatCalculation.sqrt_total {width : FloatWidth} {input : Nat} {meaning : FloatMeaning}
    (decoded : decodeFloat width input = some meaning) :
    ∃ result, FloatCalculation width .squareRoot [input] result := by
  cases meaning with
  | nan => exact ⟨_,.nan ⟨input,by simp,decoded⟩⟩
  | infinity sign =>
      cases sign with
      | false => exact ⟨input,.sqrtInfinity decoded⟩
      | true => exact ⟨_,.sqrtNegative (m := 0) (e := 0) (Or.inr decoded)⟩
  | finite sign significand exponent =>
      by_cases zero : significand = 0
      · subst significand
        exact ⟨input,.sqrtZero decoded⟩
      · cases sign with
        | false => exact FloatCalculation.sqrt_finite_total decoded zero
        | true => exact ⟨_,.sqrtNegative (Or.inl ⟨decoded,zero⟩)⟩

/-- Every correctly shaped floating operation has a specified valid outcome
for every valid operand bit pattern, including square-root isolation. -/
theorem FloatCalculation.total (width : FloatWidth) (operation : FloatOperation) (inputs : List Nat)
    (arity : inputs.length = Execution.FloatArity operation)
    (valid : ∀ bits ∈ inputs, (decodeFloat width bits).isSome = true) :
    ∃ result, FloatCalculation width operation inputs result := by
  by_cases sqrt : operation = .squareRoot
  · subst operation
    rcases List.length_eq_one_iff.mp arity with ⟨input,rfl⟩
    have inputValid := valid input (by simp)
    cases decoded : decodeFloat width input with
    | none => simp [decoded] at inputValid
    | some meaning => exact FloatCalculation.sqrt_total decoded
  · exact FloatCalculation.nonsqrt_total width operation inputs arity valid sqrt

theorem Execution.PrimitiveCalculation.floating_total (target : TargetProfile) (width : FloatWidth)
    (operation : FloatOperation) (inputs : List Nat) (arity : inputs.length = Execution.FloatArity operation)
    (valid : ∀ bits ∈ inputs, (decodeFloat width bits).isSome = true) :
    ∃ result, Execution.PrimitiveCalculation target (.floating operation width) [] (inputs.map (.floating width))
      (.ok (.floating width result)) ∧ (ScalarValue.floating width result).Valid target := by
  rcases FloatCalculation.total width operation inputs arity valid with ⟨result,calculated⟩
  exact ⟨result,.floating arity calculated,calculated.valid⟩

end Glorious.Language
