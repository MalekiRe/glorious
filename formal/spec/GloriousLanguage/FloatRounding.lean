import GloriousLanguage.ConversionPreservation

/-! Mathematical existence of nearest/even rounding. The finite search below
is a proof witness over an abstract strictly ordered lattice, not another
runtime floating evaluator. The intended consumer is the existing relational
`RoundsFinite` definition through the IEEE encoding lattice. -/
namespace Glorious.Language

namespace FiniteGrid

def distance (points : Nat → Nat) (denominator : Nat) (numerator : Int) (index : Nat) : Nat :=
  (numerator - (points index * denominator : Nat)).natAbs

/-- A point strictly between two equally distant points is closer. Integer
cross-products let us establish this without approximation or host floats. -/
theorem distance_between {numerator left middle right : Int}
    (orderedLeft : left < middle) (orderedRight : middle < right)
    (equal : (numerator - left).natAbs = (numerator - right).natAbs) :
    (numerator - middle).natAbs < (numerator - left).natAbs := by
  have leftSign := Int.natAbs_eq_iff.mp (rfl : (numerator - left).natAbs = (numerator - left).natAbs)
  have rightSign := Int.natAbs_eq_iff.mp (rfl : (numerator - right).natAbs = (numerator - right).natAbs)
  have middleSign := Int.natAbs_eq_iff.mp (rfl : (numerator - middle).natAbs = (numerator - middle).natAbs)
  rcases leftSign with leftSign | leftSign <;>
    rcases rightSign with rightSign | rightSign <;>
    rcases middleSign with middleSign | middleSign <;> omega

/-- Nearest/even selection exists on every finite strictly increasing lattice
whose code parity supplies the tie parity. There is no gap in which all nearest
candidates can be odd: equal-distance odd codes enclose a strictly closer code. -/
theorem nearest_even (points : Nat → Nat) (last denominator : Nat) (numerator : Int)
    (positive : 0 < denominator)
    (increasing : ∀ left right, left < right → right ≤ last → points left < points right) :
    ∃ selected, selected ≤ last ∧
      (∀ other, other ≤ last → distance points denominator numerator selected ≤ distance points denominator numerator other) ∧
      (∀ other, other ≤ last → other ≠ selected →
        distance points denominator numerator selected = distance points denominator numerator other → selected % 2 = 0) := by
  let metric := fun index => 2 * distance points denominator numerator index + index % 2
  let selected := (List.range (last + 1)).minOn metric (by simp)
  have bounded : selected ≤ last := by
    have member : selected ∈ List.range (last + 1) := List.minOn_mem
    simp only [List.mem_range] at member
    omega
  have optimal : ∀ other, other ≤ last → metric selected ≤ metric other := by
    intro other bound
    exact List.apply_minOn_le_of_mem (by simp only [List.mem_range]; omega)
  have nearest : ∀ other, other ≤ last →
      distance points denominator numerator selected ≤ distance points denominator numerator other := by
    intro other bound
    have minimal := optimal other bound
    dsimp [metric] at minimal
    omega
  refine ⟨selected,bounded,nearest,?_⟩
  intro other otherBound different sameDistance
  by_cases even : selected % 2 = 0
  · exact even
  have otherOdd : other % 2 = 1 := by
    have minimal := optimal other otherBound
    dsimp [metric] at minimal
    omega
  by_cases ordered : selected < other
  · have middleLeft : selected < selected + 1 := by omega
    have middleRight : selected + 1 < other := by omega
    have middleBound : selected + 1 ≤ last := by omega
    have first := Nat.mul_lt_mul_of_pos_right (increasing selected (selected + 1) middleLeft middleBound) positive
    have second := Nat.mul_lt_mul_of_pos_right (increasing (selected + 1) other middleRight otherBound) positive
    have closer := distance_between (numerator := numerator)
      (Int.ofNat_lt.mpr first) (Int.ofNat_lt.mpr second) sameDistance
    have minimal := nearest (selected + 1) middleBound
    exact False.elim (Nat.not_lt_of_ge minimal closer)
  · have middleLeft : other < other + 1 := by omega
    have middleRight : other + 1 < selected := by omega
    have middleBound : other + 1 ≤ last := by omega
    have first := Nat.mul_lt_mul_of_pos_right (increasing other (other + 1) middleLeft middleBound) positive
    have second := Nat.mul_lt_mul_of_pos_right (increasing (other + 1) selected middleRight bounded) positive
    have closer := distance_between (numerator := numerator)
      (Int.ofNat_lt.mpr first) (Int.ofNat_lt.mpr second) sameDistance.symm
    have minimal := nearest (other + 1) middleBound
    change distance points denominator numerator (other + 1) < distance points denominator numerator other at closer
    rw [← sameDistance] at closer
    exact False.elim (Nat.not_lt_of_ge minimal closer)

end FiniteGrid

theorem binaryFraction.common_denominator (negative : Bool) (significand power scale : Nat) :
    (binaryFraction negative significand ((power : Int) - scale)).Equal
      ⟨(if negative then -1 else 1) * (significand : Int) * (2 : Int)^power,2^scale⟩ := by
  refine ⟨binaryFraction.valid _ _ _,Nat.pow_pos (by decide),?_⟩
  by_cases below : power < scale
  · have negativeExponent : (power : Int) - scale < 0 := by omega
    have magnitude : ((power : Int) - scale).natAbs = scale - power := by omega
    simp only [binaryFraction,negativeExponent,↓reduceIte,magnitude,Int.natCast_pow]
    change (if negative then -1 else 1) * (significand : Int) * 2^scale =
      (if negative then -1 else 1) * (significand : Int) * 2^power * 2^(scale-power)
    have powers : (2 : Int)^scale = 2^power * 2^(scale-power) := by
      rw [← Int.pow_add,Nat.add_sub_cancel' (Nat.le_of_lt below)]
    simp only [powers,Int.mul_assoc]
  · have nonnegativeExponent : ¬ (power : Int) - scale < 0 := by omega
    simp only [binaryFraction,nonnegativeExponent,↓reduceIte,Int.toNat_sub,Int.natCast_pow,Int.ofNat_one,Int.mul_one]
    change (if negative then -1 else 1) * (significand : Int) * 2^(power-scale) * 2^scale =
      (if negative then -1 else 1) * (significand : Int) * 2^power
    rw [Int.mul_assoc,← Int.pow_add,Nat.sub_add_cancel (by omega)]

namespace Fraction

theorem distance_cross {exact value : Fraction} {numerator : Int} {denominator : Nat}
    (represented : value.Equal ⟨numerator,denominator⟩) :
    (exact.subtract value).numerator.natAbs * denominator =
      (exact.numerator * denominator - numerator * exact.denominator).natAbs * value.denominator := by
  have cross := represented.2.2
  change value.numerator * (denominator : Int) = numerator * value.denominator at cross
  have signed : (exact.subtract value).numerator * (denominator : Int) =
      (exact.numerator * denominator - numerator * exact.denominator) * value.denominator := by
    simp only [subtract,add,negate,Int.neg_mul,← Int.sub_eq_add_neg]
    grind only
  have absolute := congrArg Int.natAbs signed
  simpa only [Int.natAbs_mul,Int.natAbs_natCast] using absolute

theorem distance_le_common {exact left right : Fraction} {x y : Int} {denominator : Nat}
    (valid : exact.Valid) (leftRep : left.Equal ⟨x,denominator⟩) (rightRep : right.Equal ⟨y,denominator⟩)
    (nearest : (exact.numerator * denominator - x * exact.denominator).natAbs ≤
      (exact.numerator * denominator - y * exact.denominator).natAbs) :
    (exact.subtract left).absolute.Le (exact.subtract right).absolute := by
  have leftCross := distance_cross (exact := exact) leftRep
  have rightCross := distance_cross (exact := exact) rightRep
  refine ⟨Nat.mul_pos valid leftRep.1,Nat.mul_pos valid rightRep.1,?_⟩
  change ((exact.subtract left).numerator.natAbs : Int) * (exact.denominator * right.denominator : Nat) ≤
    ((exact.subtract right).numerator.natAbs : Int) * (exact.denominator * left.denominator : Nat)
  simp only [← Int.natCast_mul,Int.ofNat_le]
  apply Nat.le_of_mul_le_mul_right (c := denominator) _ leftRep.2.1
  calc
    (exact.subtract left).numerator.natAbs * (exact.denominator * right.denominator) * denominator =
        ((exact.subtract left).numerator.natAbs * denominator) * (exact.denominator * right.denominator) := by ac_rfl
    _ = ((exact.numerator * denominator - x * exact.denominator).natAbs * left.denominator) *
        (exact.denominator * right.denominator) := by rw [leftCross]
    _ = (exact.numerator * denominator - x * exact.denominator).natAbs *
        (left.denominator * exact.denominator * right.denominator) := by ac_rfl
    _ ≤ (exact.numerator * denominator - y * exact.denominator).natAbs *
        (left.denominator * exact.denominator * right.denominator) := Nat.mul_le_mul_right _ nearest
    _ = ((exact.numerator * denominator - y * exact.denominator).natAbs * right.denominator) *
        (exact.denominator * left.denominator) := by ac_rfl
    _ = ((exact.subtract right).numerator.natAbs * denominator) *
        (exact.denominator * left.denominator) := by rw [rightCross]
    _ = (exact.subtract right).numerator.natAbs * (exact.denominator * left.denominator) * denominator := by ac_rfl

theorem distance_equal_common {exact left right : Fraction} {x y : Int} {denominator : Nat}
    (valid : exact.Valid) (leftRep : left.Equal ⟨x,denominator⟩) (rightRep : right.Equal ⟨y,denominator⟩)
    (equal : (exact.subtract left).absolute.Equal (exact.subtract right).absolute) :
    (exact.numerator * denominator - x * exact.denominator).natAbs =
      (exact.numerator * denominator - y * exact.denominator).natAbs := by
  have leftCross := distance_cross (exact := exact) leftRep
  have rightCross := distance_cross (exact := exact) rightRep
  have cross := equal.2.2
  change ((exact.subtract left).numerator.natAbs : Int) * (exact.denominator * right.denominator : Nat) =
    ((exact.subtract right).numerator.natAbs : Int) * (exact.denominator * left.denominator : Nat) at cross
  simp only [← Int.natCast_mul,Int.natCast_inj] at cross
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos leftRep.1 (Nat.mul_pos valid rightRep.1))
  calc
    (exact.numerator * denominator - x * exact.denominator).natAbs *
        (left.denominator * (exact.denominator * right.denominator)) =
        ((exact.subtract left).numerator.natAbs * denominator) * (exact.denominator * right.denominator) := by
          rw [leftCross]; ac_rfl
    _ = ((exact.subtract left).numerator.natAbs * (exact.denominator * right.denominator)) * denominator := by ac_rfl
    _ = ((exact.subtract right).numerator.natAbs * (exact.denominator * left.denominator)) * denominator := by rw [cross]
    _ = ((exact.subtract right).numerator.natAbs * denominator) * (exact.denominator * left.denominator) := by ac_rfl
    _ = (exact.numerator * denominator - y * exact.denominator).natAbs *
        (left.denominator * (exact.denominator * right.denominator)) := by rw [rightCross]; ac_rfl

end Fraction

namespace FloatLattice

def base (width : FloatWidth) : Nat := 2^width.format.fractionBits
def cutoff (width : FloatWidth) : Nat := (2^width.format.exponentBits-1)*base width
def signMask (width : FloatWidth) : Nat := 2^(width.format.exponentBits+width.format.fractionBits)
def scale (width : FloatWidth) : Nat := width.format.bias+width.format.fractionBits-1
def encode (width : FloatWidth) (negative : Bool) (code : Nat) : Nat :=
  (if negative then signMask width else 0) + code
def significand (width : FloatWidth) (code : Nat) : Nat :=
  if code / base width = 0 then code % base width else base width + code % base width
def power (width : FloatWidth) (code : Nat) : Nat := code / base width - 1
def meaning (width : FloatWidth) (negative : Bool) (code : Nat) : FloatMeaning :=
  .finite negative (significand width code) ((power width code : Int) - scale width)

theorem decode_encode (width : FloatWidth) (negative : Bool) (code : Nat)
    (bounded : code < cutoff width) :
    decodeFloat width (encode width negative code) = some (meaning width negative code) := by
  have signCorrect : (encode width negative code / signMask width != 0) = negative := by
    cases width <;> cases negative <;>
      simp [cutoff,base,FloatWidth.format] at bounded <;>
      simp [encode,signMask,FloatWidth.format] <;> omega
  cases width <;> cases negative <;>
    simp [cutoff,base,FloatWidth.format] at bounded <;>
    simp [encode,signMask,FloatWidth.format] at signCorrect <;>
    simp [decodeFloat,encode,signMask,meaning,significand,power,scale,base,FloatWidth.format] <;>
    (try simp only [signCorrect]) <;>
    (constructor; · omega) <;>
    repeat' first | omega | split | simp_all

theorem finite_code {width : FloatWidth} {bits m : Nat} {negative : Bool} {exponent : Int}
    (decoded : decodeFloat width bits = some (.finite negative m exponent)) :
    ∃ code, code < cutoff width ∧ bits = encode width negative code ∧
      m = significand width code ∧ exponent = (power width code : Int) - scale width := by
  refine ⟨bits % signMask width,?_⟩
  unfold decodeFloat at decoded
  dsimp only at decoded
  split at decoded
  · contradiction
  · split at decoded
    · split at decoded <;> simp at decoded
    · split at decoded <;>
        simp only [Option.some.injEq,FloatMeaning.finite.injEq] at decoded <;>
        cases width <;>
        simp [cutoff,base,encode,signMask,significand,power,scale,FloatWidth.format] at * <;>
        repeat' first | omega | split | simp_all

/-- A positive finite encoding, measured in minimum-subnormal units. This is
a mathematical projection of the existing exponent/fraction bit fields. -/
def units (fractionBits code : Nat) : Nat :=
  let base := 2 ^ fractionBits
  let exponent := code / base
  let fraction := code % base
  if exponent = 0 then fraction else (base + fraction) * 2 ^ (exponent - 1)

theorem units_components {fractionBits exponent fraction : Nat}
    (bounded : fraction < 2 ^ fractionBits) :
    units fractionBits (exponent * 2 ^ fractionBits + fraction) =
      if exponent = 0 then fraction else (2 ^ fractionBits + fraction) * 2 ^ (exponent - 1) := by
  have basePositive : 0 < 2 ^ fractionBits := Nat.pow_pos (by decide)
  have division : (exponent * 2 ^ fractionBits + fraction) / 2 ^ fractionBits = exponent := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ basePositive,Nat.div_eq_of_lt bounded,Nat.zero_add]
  simp only [units,division,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt bounded]

theorem units_step (fractionBits code : Nat) : units fractionBits code < units fractionBits (code + 1) := by
  let base := 2 ^ fractionBits
  have basePositive : 0 < base := Nat.pow_pos (by decide)
  let exponent := code / base
  let fraction := code % base
  have fractionBound : fraction < base := Nat.mod_lt _ basePositive
  have decomposition : code = exponent * base + fraction := by
    simpa [exponent,fraction,Nat.mul_comm,Nat.add_comm] using (Nat.mod_add_div code base).symm
  have current := units_components (fractionBits := fractionBits) (exponent := exponent) fractionBound
  have currentEq : units fractionBits code =
      if exponent = 0 then fraction else (base + fraction) * 2 ^ (exponent - 1) := by
    change units fractionBits (exponent * base + fraction) = _ at current
    rw [← decomposition] at current
    exact current
  by_cases nextFraction : fraction + 1 < base
  · have next := units_components (fractionBits := fractionBits) (exponent := exponent) nextFraction
    have nextCode : code + 1 = exponent * base + (fraction + 1) := by omega
    have nextEq : units fractionBits (code + 1) =
        if exponent = 0 then fraction + 1 else (base + (fraction + 1)) * 2 ^ (exponent - 1) := by
      change units fractionBits (exponent * base + (fraction + 1)) = _ at next
      rw [← nextCode] at next
      exact next
    rw [currentEq,nextEq]
    by_cases zero : exponent = 0
    · simp [zero]
    · simp only [zero,↓reduceIte]
      exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pow_pos (by decide))
  · have wrap : fraction + 1 = base := by omega
    have nextCode : code + 1 = (exponent + 1) * base + 0 := by
      rw [Nat.add_mul]
      omega
    have next := units_components (fractionBits := fractionBits) (exponent := exponent + 1)
      (fraction := 0) basePositive
    have nextEq : units fractionBits (code + 1) = base * 2 ^ exponent := by
      change units fractionBits ((exponent + 1) * base + 0) = _ at next
      rw [← nextCode] at next
      simpa using next
    rw [currentEq,nextEq]
    by_cases zero : exponent = 0
    · simp only [zero,↓reduceIte,Nat.pow_zero,Nat.mul_one]
      exact fractionBound
    · simp only [zero,↓reduceIte]
      have power : (2 : Nat) ^ exponent = 2 ^ (exponent - 1) * 2 := by
        calc
          2 ^ exponent = 2 ^ ((exponent - 1) + 1) :=
            congrArg (fun power : Nat => 2 ^ power) (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr zero)).symm
          _ = 2 ^ (exponent - 1) * 2 := Nat.pow_succ _ _
      rw [power]
      have less : base + fraction < base * 2 := by omega
      have multiplied := Nat.mul_lt_mul_of_pos_right (k := 2 ^ (exponent - 1)) less
        (Nat.pow_pos (by decide : 0 < (2 : Nat)))
      simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using multiplied

theorem units_increasing (fractionBits : Nat) :
    ∀ left right, left < right → units fractionBits left < units fractionBits right := by
  intro left right
  induction right with
  | zero => intro impossible; omega
  | succ right ih =>
      intro ordered
      by_cases same : left = right
      · subst right
        exact units_step fractionBits left
      · exact Nat.lt_trans (ih (by omega)) (units_step fractionBits right)

theorem units_significand (width : FloatWidth) (code : Nat) :
    units width.format.fractionBits code = significand width code * 2^power width code := by
  by_cases zero : code / 2^width.format.fractionBits = 0 <;>
    simp only [units,significand,power,base,zero,↓reduceIte,Nat.zero_sub,Nat.pow_zero,Nat.mul_one]

theorem significand_parity (width : FloatWidth) (code : Nat) :
    significand width code % 2 = code % 2 := by
  cases width <;> simp [significand,base,FloatWidth.format] <;> split <;> omega

theorem significand_zero (width : FloatWidth) (code : Nat) :
    significand width code = 0 ↔ code = 0 := by
  cases width <;> simp [significand,base,FloatWidth.format] <;> split <;> omega

def signed (negative : Bool) (magnitude : Nat) : Int := if negative then -(magnitude : Int) else magnitude
def Aligned (negative : Bool) (numerator : Int) : Prop := if negative then numerator ≤ 0 else 0 ≤ numerator

theorem aligned_distance {negative : Bool} {numerator : Int} (magnitude : Nat)
    (aligned : Aligned negative numerator) :
    (numerator - signed negative magnitude).natAbs = ((numerator.natAbs : Int) - magnitude).natAbs := by
  cases negative with
  | false =>
      change 0 ≤ numerator at aligned
      simp only [signed,Bool.false_eq_true,↓reduceIte,Int.natAbs_of_nonneg aligned]
  | true =>
      change numerator ≤ 0 at aligned
      simp only [signed,↓reduceIte,Int.ofNat_natAbs_of_nonpos aligned]
      have opposite : numerator - -(magnitude : Int) = -(-numerator - magnitude) := by omega
      rw [opposite,Int.natAbs_neg]

theorem opposite_distance {negative : Bool} {numerator : Int} (magnitude : Nat)
    (aligned : Aligned negative numerator) :
    (numerator - signed (!negative) magnitude).natAbs = numerator.natAbs + magnitude := by
  cases negative with
  | false =>
      change 0 ≤ numerator at aligned
      simp only [signed,Bool.not_false,↓reduceIte]
      have nonnegative : 0 ≤ numerator - -(magnitude : Int) := by omega
      have absolute := Int.natAbs_of_nonneg nonnegative
      have original := Int.natAbs_of_nonneg aligned
      omega
  | true =>
      change numerator ≤ 0 at aligned
      simp only [signed,Bool.not_true,Bool.false_eq_true,↓reduceIte]
      have nonpositive : numerator - (magnitude : Int) ≤ 0 := by omega
      have absolute := Int.ofNat_natAbs_of_nonpos nonpositive
      have original := Int.ofNat_natAbs_of_nonpos aligned
      omega

theorem signed_mul (negative : Bool) (magnitude denominator : Nat) :
    signed negative magnitude * (denominator : Int) = signed negative (magnitude * denominator) := by
  cases negative <;> simp [signed,Int.natCast_mul,Int.neg_mul]

theorem distance_scaled {negative : Bool} {numerator : Int} (scale denominator magnitude : Nat)
    (aligned : Aligned negative (numerator * scale)) :
    (numerator * scale - signed negative magnitude * denominator).natAbs =
      ((numerator.natAbs * scale : Nat) - (magnitude * denominator : Nat) : Int).natAbs := by
  rw [signed_mul,aligned_distance _ aligned,Int.natAbs_mul,Int.natAbs_natCast]

theorem opposite_scaled {negative : Bool} {numerator : Int} (scale denominator magnitude : Nat)
    (aligned : Aligned negative (numerator * scale)) :
    (numerator * scale - signed (!negative) magnitude * denominator).natAbs =
      numerator.natAbs * scale + magnitude * denominator := by
  rw [signed_mul,opposite_distance _ aligned,Int.natAbs_mul,Int.natAbs_natCast]

def roundingSign (numerator : Int) (negativeZero : Bool) : Bool :=
  if numerator = 0 then negativeZero else decide (numerator < 0)

theorem roundingSign_aligned (numerator : Int) (negativeZero : Bool) (scale : Nat) :
    Aligned (roundingSign numerator negativeZero) (numerator * scale) := by
  by_cases zero : numerator = 0
  · cases negativeZero <;> simp [roundingSign,zero,Aligned]
  · by_cases negative : numerator < 0
    · simp only [roundingSign,zero,negative,↓reduceIte,decide_true,Aligned]
      exact Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (Int.natCast_nonneg _)
    · simp only [roundingSign,zero,negative,↓reduceIte,decide_false,Aligned,Bool.false_eq_true]
      exact Int.mul_nonneg (by omega) (Int.natCast_nonneg _)

def value (width : FloatWidth) (negative : Bool) (code : Nat) : Fraction :=
  binaryFraction negative (significand width code) ((power width code : Int) - scale width)

theorem common (width : FloatWidth) (negative : Bool) (code : Nat) :
    (value width negative code).Equal ⟨signed negative (units width.format.fractionBits code),2^scale width⟩ := by
  have represented := binaryFraction.common_denominator negative (significand width code) (power width code) (scale width)
  have numerator : (if negative then -1 else 1) * (significand width code : Int) * 2^power width code =
      signed negative (units width.format.fractionBits code) := by
    rw [units_significand]
    cases negative <;> simp [signed,Int.natCast_mul,Int.natCast_pow,Int.neg_mul]
  simpa only [value,numerator] using represented

end FloatLattice

/-- Every valid exact fraction below the overflow threshold has an actual
nearest/even finite bit pattern. The proof searches only the existing decoder's
finite lattice and retains the prescribed sign for a zero result. -/
theorem RoundsFinite.total (width : FloatWidth) (exact : Fraction) (negativeZero : Bool)
    (valid : exact.Valid) (below : ¬ (overflowThreshold width).Le exact.absolute) :
    ∃ bits, RoundsFinite width exact negativeZero bits := by
  classical
  let denominator := 2^FloatLattice.scale width
  let negative := FloatLattice.roundingSign exact.numerator negativeZero
  let points := FloatLattice.units width.format.fractionBits
  let distance := FiniteGrid.distance points exact.denominator ((exact.numerator.natAbs * denominator : Nat) : Int)
  have aligned : FloatLattice.Aligned negative (exact.numerator * denominator) :=
    FloatLattice.roundingSign_aligned _ _ _
  have cutoffPositive : 0 < FloatLattice.cutoff width := by cases width <;> decide
  rcases FiniteGrid.nearest_even points (FloatLattice.cutoff width - 1) exact.denominator
      ((exact.numerator.natAbs * denominator : Nat) : Int) valid
      (fun left right ordered _ => FloatLattice.units_increasing _ left right ordered) with
    ⟨selected,bounded,nearest,even⟩
  have selectedBound : selected < FloatLattice.cutoff width := by omega
  have normalized : ∀ code,
      (exact.numerator * denominator - FloatLattice.signed negative (points code) * exact.denominator).natAbs =
        distance code := by
    intro code
    exact FloatLattice.distance_scaled _ _ _ aligned
  have opposite : ∀ code,
      (exact.numerator * denominator - FloatLattice.signed (!negative) (points code) * exact.denominator).natAbs =
        exact.numerator.natAbs * denominator + points code * exact.denominator := by
    intro code
    exact FloatLattice.opposite_scaled _ _ _ aligned
  have zeroDistance : distance 0 = exact.numerator.natAbs * denominator := by
    simp [distance,FiniteGrid.distance,points,FloatLattice.units,Int.natAbs_mul]
  have zeroNearest : distance selected ≤ exact.numerator.natAbs * denominator := by
    have bound : distance selected ≤ distance 0 := nearest 0 (Nat.zero_le _)
    rwa [zeroDistance] at bound
  refine ⟨FloatLattice.encode width negative selected,valid,below,negative,
    FloatLattice.significand width selected,(FloatLattice.power width selected : Int) - FloatLattice.scale width,
    FloatLattice.value width negative selected,FloatLattice.decode_encode _ _ _ selectedBound,rfl,?_,?_,?_⟩
  · intro _
    rfl
  · intro other otherSign otherSignificand otherExponent decoded
    rcases FloatLattice.finite_code decoded with ⟨code,codeBound,rfl,rfl,rfl⟩
    apply Fraction.distance_le_common valid (FloatLattice.common width negative selected) (FloatLattice.common width otherSign code)
    change (exact.numerator * denominator - FloatLattice.signed negative (points selected) * exact.denominator).natAbs ≤
      (exact.numerator * denominator - FloatLattice.signed otherSign (points code) * exact.denominator).natAbs
    rw [normalized]
    by_cases sameSign : otherSign = negative
    · rw [sameSign,normalized]
      exact nearest code (by omega)
    · have oppositeSign : otherSign = !negative := Bool.eq_not_of_ne sameSign
      rw [oppositeSign,opposite]
      omega
  · intro other otherSign otherSignificand otherExponent different decoded zeroSign equal
    rcases FloatLattice.finite_code decoded with ⟨code,codeBound,rfl,rfl,rfl⟩
    have equalDistance := Fraction.distance_equal_common valid
      (FloatLattice.common width negative selected) (FloatLattice.common width otherSign code) equal
    change (exact.numerator * denominator - FloatLattice.signed negative (points selected) * exact.denominator).natAbs =
      (exact.numerator * denominator - FloatLattice.signed otherSign (points code) * exact.denominator).natAbs at equalDistance
    rw [normalized] at equalDistance
    rw [FloatLattice.significand_parity]
    by_cases sameSign : otherSign = negative
    · rw [sameSign,normalized] at equalDistance
      apply even code (by omega) _ equalDistance
      intro sameCode
      apply different
      simp only [sameSign,sameCode]
    · have oppositeSign : otherSign = !negative := Bool.eq_not_of_ne sameSign
      rw [oppositeSign,opposite] at equalDistance
      have nonzero : code ≠ 0 := by
        rcases zeroSign with nonzero | sameSign'
        · intro zero
          exact nonzero ((FloatLattice.significand_zero width code).mpr zero)
        · exact False.elim (sameSign sameSign')
      have positive : 0 < points code := by
        have increasing := FloatLattice.units_increasing width.format.fractionBits 0 code (by omega)
        change FloatLattice.units width.format.fractionBits 0 < points code at increasing
        have zero : FloatLattice.units width.format.fractionBits 0 = 0 := by simp [FloatLattice.units]
        rwa [zero] at increasing
      have positiveProduct := Nat.mul_pos positive valid
      omega

/-- The authoritative rounding relation is total on valid exact arithmetic,
including overflow, without taking a rounding witness as a premise. -/
theorem Rounded.total (width : FloatWidth) (exact : Fraction) (negativeZero : Bool)
    (valid : exact.Valid) : ∃ bits, Rounded width exact negativeZero bits := by
  classical
  by_cases overflow : (overflowThreshold width).Le exact.absolute
  · rcases decodeFloat.infinity_exists width (decide (exact.numerator < 0)) with ⟨bits,decoded⟩
    exact ⟨bits,.overflow valid overflow decoded⟩
  · rcases RoundsFinite.total width exact negativeZero valid overflow with ⟨bits,rounded⟩
    exact ⟨bits,.finite rounded⟩

end Glorious.Language
