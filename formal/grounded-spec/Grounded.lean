/-!
# Closed scalar expressions: source AST to value

Normative basis: language specification §§3.2–3.4, 4.1, and 7.2.
Integer literals have an explicitly selected fixed-width type and a decoded
nonnegative magnitude. Character literals have a decoded scalar number.
Token decoding, inference, prefix negation, target-size integers, floating
conversion, static strings, and physical realization are outside this subset.
Admission has no execution premise. No prior specification modules are imported.
-/

namespace Grounded

inductive Width where
  | w8 | w16 | w32 | w64 | w128

def Width.bits : Width → Nat
  | .w8 => 8
  | .w16 => 16
  | .w32 => 32
  | .w64 => 64
  | .w128 => 128

structure IntegerType where
  signed : Bool
  width : Width

/-- Mathematical scalar range; there is no implicit wrapping of literals. -/
def IntegerType.Contains (type : IntegerType) (value : Int) : Prop :=
  let bound : Int := 2 ^ (type.width.bits - if type.signed then 1 else 0)
  (if type.signed then -bound else 0) ≤ value ∧ value < bound

def UnicodeScalar (number : Nat) : Prop :=
  number < 0x110000 ∧ (number < 0xd800 ∨ 0xe000 ≤ number)

inductive Expr where
  | unit
  | integer (type : IntegerType) (magnitude : Nat)
  | character (number : Nat)

inductive Ty where
  | unit
  | integer (type : IntegerType)
  | character

inductive Value where
  | unit
  | integer (type : IntegerType) (number : Int)
  | character (number : Nat)

inductive HasType : Expr → Ty → Prop where
  | unit : HasType .unit .unit
  | integer {type : IntegerType} {magnitude : Nat}
      (fits : type.Contains magnitude) :
      HasType (.integer type magnitude) (.integer type)
  | character {number : Nat} (valid : UnicodeScalar number) :
      HasType (.character number) .character

inductive ValueHasType : Value → Ty → Prop where
  | unit : ValueHasType .unit .unit
  | integer {type : IntegerType} {number : Int}
      (fits : type.Contains number) :
      ValueHasType (.integer type number) (.integer type)
  | character {number : Nat} (valid : UnicodeScalar number) :
      ValueHasType (.character number) .character

inductive Evaluates : Expr → Value → Prop where
  | unit : Evaluates .unit .unit
  | integer {type : IntegerType} {magnitude : Nat}
      (fits : type.Contains magnitude) :
      Evaluates (.integer type magnitude) (.integer type magnitude)
  | character {number : Nat} (valid : UnicodeScalar number) :
      Evaluates (.character number) (.character number)

/-- Every admitted expression terminates with a correctly typed, unique result.
Invalid scalar encodings are excluded by admission, not hidden in a premise
asserting existence of execution. -/
theorem correctness {expression : Expr} {type : Ty}
    (admitted : HasType expression type) :
    ∃ value, Evaluates expression value ∧ ValueHasType value type ∧
      ∀ other, Evaluates expression other → other = value := by
  cases admitted with
  | unit =>
    refine ⟨.unit, .unit, .unit, ?_⟩
    intro other evaluated
    cases evaluated
    rfl
  | integer fits =>
    refine ⟨_, .integer fits, .integer fits, ?_⟩
    intro other evaluated
    cases evaluated
    rfl
  | character valid =>
    refine ⟨_, .character valid, .character valid, ?_⟩
    intro other evaluated
    cases evaluated
    rfl

/-- Exact admission boundary: every in-range literal is admitted and every
out-of-range literal is rejected. This covers all widths, not selected examples. -/
theorem integer_admission (type : IntegerType) (magnitude : Nat) :
    (∃ result, HasType (.integer type magnitude) result) ↔
      type.Contains magnitude := by
  constructor
  · rintro ⟨_, admitted⟩
    cases admitted with
    | integer fits => exact fits
  · intro fits
    exact ⟨_, .integer fits⟩

theorem character_admission (number : Nat) :
    (∃ result, HasType (.character number) result) ↔ UnicodeScalar number := by
  constructor
  · rintro ⟨_, admitted⟩
    cases admitted with
    | character valid => exact valid
  · intro valid
    exact ⟨_, .character valid⟩

/-- The original subset retains precisely its admission and evaluation meaning.
The extended general theorem supplies its terminating, typed execution. -/
theorem unit_agreement : HasType .unit .unit ∧
    ∀ value, Evaluates .unit value ↔ value = .unit := by
  obtain ⟨value, evaluated, _, unique⟩ := correctness HasType.unit
  have same : value = .unit := by cases evaluated; rfl
  refine ⟨.unit, fun other => ⟨?_, ?_⟩⟩
  · intro evaluation
    exact (unique other evaluation).trans same
  · intro equal
    subst other
    exact .unit

end Grounded
