import GloriousLanguage.ConversionPreservation
import GloriousLanguage.Preservation

/-! The scalar manifest contract is consumed by actual call admission and
calculation. Nonfloating result families have a general normal-or-fatal outcome;
floating-result progress still requires the separate rounding/sqrt existence
theorems. Storage allocation/initialization progress is not assumed here. -/
namespace Glorious.Language

def ScalarOperandsTyped (target : TargetProfile) (values : List ScalarValue) (types : List Term) : Prop :=
  ListRel (fun value type => value.Valid target ∧ .scalar value.type = type) values types

theorem ScalarOperandsTyped.valid {target : TargetProfile} {values : List ScalarValue} {types : List Term}
    (typed : ScalarOperandsTyped target values types) : ∀ value ∈ values, value.Valid target := by
  induction typed with
  | nil => simp
  | cons current _ ih =>
      intro value member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact current.1
      · exact ih value member

theorem ScalarOperandsTyped.integers {target : TargetProfile} {sign : Bool} {width : Width}
    {values : List ScalarValue} {count : Nat}
    (typed : ScalarOperandsTyped target values (List.replicate count (.scalar (.integer sign width)))) :
    ∃ integers : List Int, values = integers.map (.integer sign width) ∧ integers.length = count ∧
      ∀ integer ∈ integers, IntegerRange target sign width integer := by
  induction count generalizing values with
  | zero =>
      cases typed
      exact ⟨[],rfl,rfl,by simp⟩
  | succ count ih =>
      cases typed with
      | @cons first _ rest _ current remainder =>
          cases first with
          | character _ => cases current.2
          | floating _ _ => cases current.2
          | integer inputSign inputWidth integer =>
              have shape := current.2
              simp only [ScalarValue.type,Term.scalar.injEq,Scalar.integer.injEq] at shape
              rcases shape with ⟨rfl,rfl⟩
              rcases ih remainder with ⟨integers,rfl,length,ranges⟩
              refine ⟨integer :: integers,rfl,by simp [length],?_⟩
              intro value member
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · exact current.1.2
              · exact ranges value member

theorem ScalarPrimitiveSignature.arguments_valid {target : TargetProfile} {primitive : Primitive}
    {arguments parameters : List Term} {result : Term}
    (signature : ScalarPrimitiveSignature target primitive arguments parameters result) :
    ∀ scalar, .scalar scalar ∈ arguments → scalar.Valid target := by
  cases signature <;> simp_all

namespace Execution

theorem PrimitiveCalculation.result_type {target : TargetProfile} {primitive : Primitive}
    {arguments parameters : List Term} {output : Term} {values : List ScalarValue} {result : ScalarValue}
    (signature : ScalarPrimitiveSignature target primitive arguments parameters output)
    (calculated : PrimitiveCalculation target primitive arguments values (.ok result)) : .scalar result.type = output := by
  cases calculated with
  | integer _ => cases signature; rfl
  | floating _ _ => cases signature; rfl
  | equal _ _ _ _ => cases signature; rfl
  | less _ _ _ _ => cases signature; rfl
  | convert converted =>
      cases signature
      exact congrArg Term.scalar converted.type

theorem PrimitiveCalculation.typed_result {target : TargetProfile} {primitive : Primitive}
    {arguments parameters : List Term} {output : Term} {values : List ScalarValue} {result : ScalarValue}
    (signature : ScalarPrimitiveSignature target primitive arguments parameters output)
    (inputs : ScalarOperandsTyped target values parameters)
    (calculated : PrimitiveCalculation target primitive arguments values (.ok result)) :
    result.Valid target ∧ .scalar result.type = output :=
  ⟨calculated.valid inputs.valid signature.arguments_valid,calculated.result_type signature⟩

theorem PrimitiveCalculation.equal_total {target : TargetProfile} {left right : ScalarValue}
    (leftValid : left.Valid target) (rightValid : right.Valid target) (sameType : left.type = right.type) :
    ∃ result, PrimitiveCalculation target .scalarEqual [] [left,right] (.ok result) := by
  classical
  by_cases equal : ScalarEqual left right
  · exact ⟨_,.equal sameType leftValid rightValid (Or.inl ⟨rfl,equal⟩)⟩
  · exact ⟨_,.equal sameType leftValid rightValid (Or.inr ⟨rfl,equal⟩)⟩

theorem PrimitiveCalculation.less_total {target : TargetProfile} {left right : ScalarValue}
    (leftValid : left.Valid target) (rightValid : right.Valid target) (sameType : left.type = right.type) :
    ∃ result, PrimitiveCalculation target .scalarLess [] [left,right] (.ok result) := by
  classical
  by_cases less : ScalarLess left right
  · exact ⟨_,.less sameType leftValid rightValid (Or.inl ⟨rfl,less⟩)⟩
  · exact ⟨_,.less sameType leftValid rightValid (Or.inr ⟨rfl,less⟩)⟩

end Execution

/-- Every admitted nonfloating-result scalar call has a specified calculation
outcome. This includes floating comparisons and all finite/nonfinite numeric
inputs to integer conversion, not only operations on integer input values. -/
theorem ScalarPrimitiveSignature.nonfloating_progress {target : TargetProfile} {primitive : Primitive}
    {arguments parameters : List Term} {output : Term} {values : List ScalarValue}
    (signature : ScalarPrimitiveSignature target primitive arguments parameters output)
    (inputs : ScalarOperandsTyped target values parameters)
    (nonfloating : ∀ width, output ≠ .scalar (.floating width)) :
    ∃ outcome, Execution.PrimitiveCalculation target primitive arguments values outcome ∧
      ∀ result, outcome = .ok result → result.Valid target ∧ .scalar result.type = output := by
  have safe := fun result calculated => Execution.PrimitiveCalculation.typed_result signature inputs
    (show Execution.PrimitiveCalculation target primitive arguments values (.ok result) from calculated)
  suffices progress : ∃ outcome, Execution.PrimitiveCalculation target primitive arguments values outcome by
    rcases progress with ⟨outcome,calculated⟩
    refine ⟨outcome,calculated,?_⟩
    intro result same
    subst outcome
    exact safe result calculated
  cases signature with
  | @integer operation sign width overflow valid =>
      rcases ScalarOperandsTyped.integers inputs with ⟨integers,rfl,arity,ranges⟩
      rcases Execution.PrimitiveCalculation.integer_total valid operation overflow integers arity ranges with
        ⟨outcome,calculated,_⟩
      exact ⟨outcome,calculated⟩
  | floating => exact False.elim (nonfloating _ rfl)
  | equal valid =>
      cases inputs with
      | cons left rest =>
          cases rest with
          | cons right done =>
              cases done
              have same := Term.scalar.inj (left.2.trans right.2.symm)
              rcases Execution.PrimitiveCalculation.equal_total left.1 right.1 same with ⟨result,calculated⟩
              exact ⟨_,calculated⟩
  | less valid =>
      cases inputs with
      | cons left rest =>
          cases rest with
          | cons right done =>
              cases done
              have same := Term.scalar.inj (left.2.trans right.2.symm)
              rcases Execution.PrimitiveCalculation.less_total left.1 right.1 same with ⟨result,calculated⟩
              exact ⟨_,calculated⟩
  | @convert policy source destination sourceValid destinationValid supported =>
      cases inputs with
      | @cons value _ _ _ typed done =>
          cases done
          cases destination with
          | floating width => exact False.elim (nonfloating width rfl)
          | integer sign width =>
              rcases Execution.ScalarConversion.to_integer_total typed.1 policy sign width with ⟨outcome,converted⟩
              exact ⟨outcome,.convert converted⟩
          | character =>
              have sourceType := Term.scalar.inj typed.2
              cases value with
              | integer sign width integer =>
                  rcases Execution.ScalarConversion.to_character_total typed.1.2 policy with ⟨outcome,converted⟩
                  exact ⟨outcome,.convert converted⟩
              | floating _ _ => cases sourceType; cases supported
              | character _ => cases sourceType; cases supported

theorem Typing.ValueTyped.scalar_head {program : Kernel.Program} {world : World} {value : Value}
    {scalar : ScalarValue} (typed : Typing.ValueTyped program world value) (head : value.head = .scalar scalar) :
    value.type = .scalar scalar.type ∧ scalar.Valid program.declarations.input.target := by
  cases typed <;> simp_all [Value.head,Value.type,Execution.ConstructorHead]

namespace Execution

/-- Operand validity comes from the actual resident typing, not a new scalar
store inventory or a post-calculation validity assertion. -/
theorem ScalarAt.valid {program : Kernel.Program} {world : World} {source : ResolvedPlace} {scalar : ScalarValue}
    (worldTyped : Typing.WorldTyped program world) (observed : ScalarAt world source scalar) :
    scalar.Valid program.declarations.input.target := by
  rcases observed.2 with ⟨value,stored,head,_⟩
  exact ((worldTyped.2.1 _ _ (World.resident_iff_stores.mpr stored)).scalar_head head).2

theorem ScalarValues.typed {program : Kernel.Program} {world : World} {sources : List ResolvedPlace}
    {values : List ScalarValue} {types : List Term} (worldTyped : Typing.WorldTyped program world)
    (observed : ScalarValues world sources values)
    (sourceTypes : ListRel (fun source type => ∃ value, world.Stores source.address value ∧ value.type = type) sources types) :
    ScalarOperandsTyped program.declarations.input.target values types := by
  induction observed generalizing types with
  | nil => cases sourceTypes; exact .nil
  | cons current rest ih =>
      cases sourceTypes with
      | cons currentType restTypes =>
          rcases current.2 with ⟨value,stored,head,_⟩
          rcases currentType with ⟨typedValue,typedStored,valueType⟩
          have same := Option.some.inj (stored.symm.trans typedStored)
          subst typedValue
          have scalar := (worldTyped.2.1 _ _ (World.resident_iff_stores.mpr stored)).scalar_head head
          exact .cons ⟨scalar.2,scalar.1.symm.trans valueType⟩ (ih restTypes)

/-- The manifest-selected signature and the actual scalar reads jointly
establish calculation progress. Creating the destination is the independent
storage-progress obligation, not a prospective typed-result assumption. -/
theorem ScalarValues.nonfloating_progress {program : Kernel.Program} {world : World} {sources : List ResolvedPlace}
    {values : List ScalarValue} {binding : RuntimeBinding} {arguments : List Term} {signature : Signature}
    {primitive : Primitive} (worldTyped : Typing.WorldTyped program world)
    (bound : binding.ScalarSignature program.declarations.input.target arguments signature)
    (identity : binding.primitive = some primitive) (scalar : primitive.IsScalar)
    (observed : ScalarValues world sources values)
    (sourceTypes : ListRel (fun source type => ∃ value, world.Stores source.address value ∧ value.type = type)
      sources signature.parameters)
    (nonfloating : ∀ width, signature.result ≠ .scalar (.floating width)) :
    ∃ outcome, PrimitiveCalculation program.declarations.input.target primitive arguments values outcome ∧
      ∀ result, outcome = .ok result → result.Valid program.declarations.input.target ∧ .scalar result.type = signature.result :=
  (bound primitive identity scalar).nonfloating_progress (observed.typed worldTyped sourceTypes) nonfloating

end Execution
end Glorious.Language
