import GloriousLanguage.FloatDeterminism
import GloriousLanguage.IntegerDeterminism
import GloriousLanguage.ScalarProgress

/-! The shared scalar calculation relation has one outcome, not merely one
successful value. Arithmetic faults cannot coexist with successful conversion. -/
namespace Glorious.Language.Execution

theorem ScalarConversion.deterministic {target : TargetProfile} {policy : ConversionPolicy}
    {source : ScalarValue} {destination : Scalar} {left right : Except Fatal ScalarValue}
    (first : ScalarConversion target policy source destination left)
    (second : ScalarConversion target policy source destination right) : left = right := by
  cases first <;> cases second <;> simp_all
  all_goals grind only [IntegerResult.deterministic,FractionIntegerConversion.deterministic,
    RoundedConversion.deterministic,decodeFloat.infinity_injective]

theorem ScalarValue.integer_map_eq (sign : Bool) (width : Width) {left right : List Int} :
    left.map (Glorious.Language.ScalarValue.integer sign width) = right.map (Glorious.Language.ScalarValue.integer sign width) ↔ left = right :=
  List.map_inj_right (fun _ _ equal => by cases equal; rfl)

theorem ScalarValue.floating_map_eq (width : FloatWidth) {left right : List Nat} :
    left.map (Glorious.Language.ScalarValue.floating width) = right.map (Glorious.Language.ScalarValue.floating width) ↔ left = right :=
  List.map_inj_right (fun _ _ equal => by cases equal; rfl)

theorem PrimitiveCalculation.deterministic {target : TargetProfile} {primitive : Primitive}
    {arguments : List Term} {inputs : List ScalarValue} {left right : Except Fatal ScalarValue}
    (first : PrimitiveCalculation target primitive arguments inputs left)
    (second : PrimitiveCalculation target primitive arguments inputs right) : left = right := by
  generalize inputsEqual : inputs = secondInputs at second
  cases first <;> cases second <;> simp_all [ScalarValue.integer_map_eq,ScalarValue.floating_map_eq]
  all_goals grind only [IntegerCalculation.deterministic,FloatCalculation.deterministic,ScalarConversion.deterministic]

end Glorious.Language.Execution

namespace Glorious.Language

/-- Admitted scalar calls have exactly one normal/fatal calculation outcome;
every successful result has the manifest result type and is valid. -/
theorem ScalarPrimitiveSignature.unique_progress {target : TargetProfile} {primitive : Primitive}
    {arguments parameters : List Term} {output : Term} {values : List ScalarValue}
    (signature : ScalarPrimitiveSignature target primitive arguments parameters output)
    (inputs : ScalarOperandsTyped target values parameters) :
    ∃ outcome, Execution.PrimitiveCalculation target primitive arguments values outcome ∧
      (∀ other, Execution.PrimitiveCalculation target primitive arguments values other → other = outcome) ∧
      (∀ result, outcome = .ok result → result.Valid target ∧ .scalar result.type = output) := by
  rcases signature.progress inputs with ⟨outcome,calculated,typed⟩
  exact ⟨outcome,calculated,fun _ other => other.deterministic calculated,typed⟩

theorem Execution.ScalarValues.unique_progress {program : Kernel.Program} {world : World} {sources : List ResolvedPlace}
    {values : List ScalarValue} {binding : RuntimeBinding} {arguments : List Term} {signature : Signature}
    {primitive : Primitive} (worldTyped : Typing.WorldTyped program world)
    (bound : binding.ScalarSignature program.declarations.input.target arguments signature)
    (identity : binding.primitive = some primitive) (scalar : primitive.IsScalar)
    (observed : Execution.ScalarValues world sources values)
    (sourceTypes : ListRel (fun source type => ∃ value, world.Stores source.address value ∧ value.type = type)
      sources signature.parameters) :
    ∃ outcome, Execution.PrimitiveCalculation program.declarations.input.target primitive arguments values outcome ∧
      (∀ other, Execution.PrimitiveCalculation program.declarations.input.target primitive arguments values other → other = outcome) ∧
      (∀ result, outcome = .ok result → result.Valid program.declarations.input.target ∧ .scalar result.type = signature.result) :=
  (bound primitive identity scalar).unique_progress (observed.typed worldTyped sourceTypes)

end Glorious.Language
