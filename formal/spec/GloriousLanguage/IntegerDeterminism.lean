import GloriousLanguage.ConversionPreservation

/-! Integer arithmetic's explicit faults and normal outcomes are disjoint.
Totality alone does not establish the language's deterministic scalar contract. -/
namespace Glorious.Language.Execution

theorem IntegerCalculation.deterministic {target : TargetProfile} {sign : Bool} {width : Width}
    {operation : IntegerOperation} {overflow : Overflow} {inputs : List Int} {first second : Except Fatal Int}
    (left : IntegerCalculation target sign width operation overflow inputs first)
    (right : IntegerCalculation target sign width operation overflow inputs second) : first = second := by
  cases left with
  | binary arity leftRange rightRange shift calculated result =>
      cases right with
      | binary _ _ _ _ calculatedRight resultRight =>
          have rawEq := Option.some.inj (calculated.symm.trans calculatedRight)
          cases rawEq
          exact result.deterministic resultRight
      | zeroDivisor operation _ =>
          rcases operation with rfl | rfl <;> simp [integerOperation] at calculated
      | invalidShift operation _ _ invalid =>
          have bounds := shift operation
          simp only [Int.ofNat_eq_natCast] at invalid
          omega
  | unary _ result =>
      cases right with
      | unary _ other => exact result.deterministic other
  | zeroDivisor operation range =>
      cases right with
      | binary _ _ _ _ calculated _ =>
          rcases operation with rfl | rfl <;> simp [integerOperation] at calculated
      | zeroDivisor _ _ => rfl
      | invalidShift operationShift _ _ _ =>
          rcases operation with rfl | rfl <;> simp at operationShift
  | invalidShift operation rangeLeft rangeRight invalid =>
      cases right with
      | binary _ _ _ shift _ _ =>
          have bounds := shift operation
          simp only [Int.ofNat_eq_natCast] at invalid
          omega
      | zeroDivisor operationZero _ =>
          rcases operation with rfl | rfl <;> simp at operationZero
      | invalidShift _ _ _ _ => rfl

end Glorious.Language.Execution
