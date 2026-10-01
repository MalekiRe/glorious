import Grounded.Checking
import Grounded.Execution

/-! Composition of operation contracts into the terminating fragment theorem.
Execution itself does not import expression checking or these correctness proofs. -/
namespace Grounded

variable {program : Program} {home : Module}

/-- Every admitted expression produces a uniquely determined, correctly typed
result and updated lexical environment. Later expressions consume that actual
post-state; scopes remove only their own bindings. -/
theorem correctness {context : List (String × BindingType)} {expression : Expr} {type : Ty}
    (admitted : HasType program home context expression type)
    {environment : List (String × Value)} (environmentTyped : EnvironmentTyped program environment context) :
    ∃ value after, Evaluates program environment expression value after ∧ ValueHasType program value type ∧
      EnvironmentTyped program after context ∧
      EnvironmentFrame context environment after ∧
      ∀ other otherAfter, Evaluates program environment expression other otherAfter → other = value ∧ otherAfter = after := by
  induction admitted using HasType.rec
    (motive_2 := fun home context expressions types _ =>
      ∀ environment, EnvironmentTyped program environment context →
        ∃ values after, EvaluatesMany program environment expressions values after ∧ ValuesHaveTypes program values types ∧
          EnvironmentTyped program after context ∧
          EnvironmentFrame context environment after ∧
          ∀ other otherAfter, EvaluatesMany program environment expressions other otherAfter → other = values ∧ otherAfter = after)
    (motive_3 := fun home context subject result previous arms _ =>
      ∀ environment, EnvironmentTyped program environment context →
      ∀ value, ValueHasType program value subject → ∀ bindings body,
        selectArm value arms = some (bindings, body) →
        ∃ resultValue after, Evaluates program (bindings ++ environment) body resultValue after ∧
          ValueHasType program resultValue result ∧ EnvironmentTyped program (after.drop bindings.length) context ∧
          EnvironmentFrame context environment (after.drop bindings.length) ∧
          ∀ other otherAfter, Evaluates program (bindings ++ environment) body other otherAfter → other = resultValue ∧ otherAfter = after)
    generalizing environment with
  | unit =>
    refine ⟨.unit, environment, .unit, .unit, environmentTyped, environmentTyped.frame_refl, ?_⟩
    intro other otherAfter evaluated
    cases evaluated
    exact ⟨rfl, rfl⟩
  | integer fits =>
    refine ⟨_, environment, .integer fits, .integer fits, environmentTyped, environmentTyped.frame_refl, ?_⟩
    intro other otherAfter evaluated
    cases evaluated
    exact ⟨rfl, rfl⟩
  | character valid =>
    refine ⟨_, environment, .character valid, .character valid, environmentTyped, environmentTyped.frame_refl, ?_⟩
    intro other otherAfter evaluated
    cases evaluated
    exact ⟨rfl, rfl⟩
  | constant declared visible resolved structural initialized ih =>
    obtain ⟨value, after, evaluated, typed, afterTyped, afterFrame, unique⟩ := ih EnvironmentTyped.nil
    cases afterTyped
    refine ⟨value, environment, .constant declared evaluated, typed, environmentTyped, environmentTyped.frame_refl, ?_⟩
    intro other otherAfter evaluation
    cases evaluation with
    | constant otherDeclared otherEval =>
      have same := Option.some.inj (otherDeclared.symm.trans declared)
      cases same
      exact ⟨(unique other [] otherEval).1, rfl⟩
  | @call home context identity arguments declaration declared visible distinct discard inputs body inputsIH bodyIH =>
    obtain ⟨values, middle, inputsEval, inputsTyped, middleTyped, middleFrame, inputsUnique⟩ := inputsIH environment environmentTyped
    have bindParameters : ∀ (parameters : List (String × BindingType)) (values : List Value),
        ValuesHaveTypes program values (parameters.map (fun parameter => parameter.2.type)) →
        EnvironmentTyped program (List.zip (parameters.map Prod.fst) values) parameters := by
      intro parameters
      induction parameters with
      | nil => intro values typed; cases typed; exact .nil
      | cons parameter parameters ih =>
        intro values typed
        cases typed with
        | cons headTyped tailTyped => exact .cons headTyped (ih _ tailTyped)
    obtain ⟨value, localAfter, bodyEval, valueTyped, _, _, bodyUnique⟩ :=
      bodyIH (bindParameters declaration.parameters values inputsTyped)
    refine ⟨value, middle, .call declared inputsEval bodyEval, valueTyped, middleTyped, middleFrame, ?_⟩
    intro other otherAfter evaluation
    cases evaluation with
    | call otherDeclared otherInputs otherBody =>
      have sameDeclaration := Option.some.inj (otherDeclared.symm.trans declared)
      cases sameDeclaration
      obtain ⟨rfl, rfl⟩ := inputsUnique _ _ otherInputs
      exact ⟨(bodyUnique _ _ otherBody).1, rfl⟩
  | applyPatterns argumentsTyped nonempty covered bodies argumentsIH bodiesIH =>
    obtain ⟨values, middle, argumentsEval, valuesTyped, middleTyped, middleFrame, argumentsUnique⟩ := argumentsIH environment environmentTyped
    have subjectTyped := valuesTyped.argument
    obtain ⟨bindings, body, selected⟩ := covered.selectArm subjectTyped
    obtain ⟨value, after, bodyEval, valueTyped, afterTyped, afterFrame, unique⟩ :=
      bodiesIH middle middleTyped _ subjectTyped bindings body selected
    refine ⟨value, after.drop bindings.length, .applyPatterns argumentsEval selected bodyEval, valueTyped, afterTyped, middleFrame.trans afterFrame, ?_⟩
    intro other otherAfter evaluation
    cases evaluation with
    | applyPatterns otherArguments otherSelected otherBody =>
      obtain ⟨rfl, rfl⟩ := argumentsUnique _ _ otherArguments
      have sameSelection := Option.some.inj (otherSelected.symm.trans selected)
      cases sameSelection
      obtain ⟨rfl, rfl⟩ := unique _ _ otherBody
      exact ⟨rfl, rfl⟩
  | group typed ih =>
    obtain ⟨value, after, evaluated, valueTyped, afterTyped, afterFrame, unique⟩ := ih environmentTyped
    refine ⟨value, after, .group evaluated, valueTyped, afterTyped, afterFrame, ?_⟩
    intro other otherAfter evaluation
    cases evaluation with
    | group inner => exact unique _ _ inner
  | read selected copyable =>
    obtain ⟨value, selectedValue, valueTyped⟩ := environmentTyped.readPlace selected
    refine ⟨value, environment, .read selectedValue, valueTyped, environmentTyped, environmentTyped.frame_refl, ?_⟩
    intro other otherAfter evaluated
    cases evaluated with
    | read found => exact ⟨Option.some.inj (found.symm.trans selectedValue), rfl⟩
  | sequence head drop tail headIH tailIH =>
    obtain ⟨discarded, middle, headEval, _, middleTyped, middleFrame, headUnique⟩ := headIH environmentTyped
    obtain ⟨value, after, tailEval, valueTyped, afterTyped, afterFrame, unique⟩ := tailIH middleTyped
    refine ⟨value, after, .sequence headEval tailEval, valueTyped, afterTyped, middleFrame.trans afterFrame, ?_⟩
    intro other otherAfter evaluated
    cases evaluated with
    | sequence otherHead otherTail =>
      obtain ⟨rfl, rfl⟩ := headUnique _ _ otherHead
      exact unique _ _ otherTail
  | bind initialized drop annotated continued initialIH bodyIH =>
    obtain ⟨resident, middle, initialEval, residentTyped, middleTyped, middleFrame, initialUnique⟩ := initialIH environmentTyped
    obtain ⟨value, after, bodyEval, valueTyped, afterTyped, afterFrame, bodyUnique⟩ := bodyIH (.cons residentTyped middleTyped)
    refine ⟨value, after.drop 1, .bind initialEval bodyEval, valueTyped, afterTyped.drop 1, middleFrame.trans (afterFrame.drop 1), ?_⟩
    intro other otherAfter evaluated
    cases evaluated with
    | bind otherInitial otherBody =>
      obtain ⟨rfl, rfl⟩ := initialUnique _ _ otherInitial
      obtain ⟨rfl, rfl⟩ := bodyUnique _ _ otherBody
      exact ⟨rfl, rfl⟩
  | assign selected discard resident continued residentIH bodyIH =>
    obtain ⟨replacement, middle, evaluated, residentTyped, middleTyped, middleFrame, residentUnique⟩ := residentIH environmentTyped
    obtain ⟨updated, written, updatedTyped, updatedFrame, _⟩ := middleTyped.writePlace selected residentTyped
    obtain ⟨value, after, bodyEval, valueTyped, afterTyped, afterFrame, bodyUnique⟩ := bodyIH updatedTyped
    refine ⟨value, after, .assign evaluated written bodyEval, valueTyped, afterTyped, middleFrame.trans (updatedFrame.trans afterFrame), ?_⟩
    intro other otherAfter evaluation
    cases evaluation with
    | assign otherEval otherWritten otherBody =>
      obtain ⟨rfl, rfl⟩ := residentUnique _ _ otherEval
      have same := Option.some.inj (otherWritten.symm.trans written)
      cases same
      exact bodyUnique _ _ otherBody
  | tuple head tail headIH tailIH =>
    obtain ⟨first, middle, headEval, headTyped, middleTyped, middleFrame, headUnique⟩ := headIH environmentTyped
    obtain ⟨rest, after, tailEval, tailTyped, afterTyped, afterFrame, tailUnique⟩ := tailIH middle middleTyped
    refine ⟨.tuple first rest, after, .tuple headEval tailEval, .tuple headTyped tailTyped, afterTyped, middleFrame.trans afterFrame, ?_⟩
    intro other otherAfter evaluated
    cases evaluated with
    | tuple otherHead otherTail =>
      obtain ⟨rfl, rfl⟩ := headUnique _ _ otherHead
      obtain ⟨rfl, rfl⟩ := tailUnique _ _ otherTail
      exact ⟨rfl, rfl⟩
  | array residents elementValid size ih =>
    obtain ⟨values, after, evaluated, typed, afterTyped, afterFrame, unique⟩ := ih environment environmentTyped
    refine ⟨.array values, after, .array evaluated, .array typed elementValid size, afterTyped, afterFrame, ?_⟩
    intro other otherAfter evaluation
    cases evaluation with
    | array elements =>
      obtain ⟨rfl, rfl⟩ := unique _ _ elements
      exact ⟨rfl, rfl⟩
  | project source discard selected sourceIH =>
    obtain ⟨aggregate, after, sourceEval, aggregateTyped, afterTyped, afterFrame, sourceUnique⟩ := sourceIH environmentTyped
    obtain ⟨value, fieldSelected, valueTyped, _⟩ := selected.access aggregateTyped
    refine ⟨value, after, .project sourceEval fieldSelected, valueTyped, afterTyped, afterFrame, ?_⟩
    intro other otherAfter evaluated
    cases evaluated with
    | project otherSource otherSelected =>
      obtain ⟨same, rfl⟩ := sourceUnique _ _ otherSource
      cases same
      exact ⟨congrArg Prod.snd (Option.some.inj (otherSelected.symm.trans fieldSelected)), rfl⟩
  | construct declared chosen finite copyable visible access residents ih =>
    obtain ⟨values, after, evaluated, typed, afterTyped, afterFrame, unique⟩ := ih environment environmentTyped
    refine ⟨_, after, .construct evaluated, .nominal declared chosen finite typed, afterTyped, afterFrame, ?_⟩
    intro other otherAfter evaluation
    cases evaluation with
    | construct otherFields =>
      obtain ⟨rfl, rfl⟩ := unique _ _ otherFields
      exact ⟨rfl, rfl⟩
  | nil =>
    rename_i environment environmentTyped
    refine ⟨[], environment, .nil, .nil, environmentTyped, environmentTyped.frame_refl, ?_⟩
    intro other otherAfter evaluated
    cases evaluated
    exact ⟨rfl, rfl⟩
  | cons head tail headIH tailIH =>
    rename_i environment environmentTyped
    obtain ⟨first, middle, headEval, headTyped, middleTyped, middleFrame, headUnique⟩ := headIH environmentTyped
    obtain ⟨rest, after, tailEval, tailTyped, afterTyped, afterFrame, tailUnique⟩ := tailIH middle middleTyped
    refine ⟨first :: rest, after, .cons headEval tailEval, .cons headTyped tailTyped, afterTyped, middleFrame.trans afterFrame, ?_⟩
    intro other otherAfter evaluated
    cases evaluated with
    | cons otherHead otherTail =>
      obtain ⟨rfl, rfl⟩ := headUnique _ _ otherHead
      obtain ⟨rfl, rfl⟩ := tailUnique _ _ otherTail
      exact ⟨rfl, rfl⟩
  | empty =>
    rename_i environment environmentTyped value valueTyped bindings body selected
    simp [selectArm] at selected
  | clause patternTyped distinct useful bodyTyped tailTyped bodyIH tailIH =>
    rename_i environment environmentTyped value valueTyped bindings body selected
    simp only [selectArm] at selected
    split at selected
    next matched found =>
      have same := Option.some.inj selected
      cases same
      have bindingsTyped := patternTyped.bindings valueTyped found
      obtain ⟨result, after, evaluated, resultTyped, afterTyped, afterFrame, unique⟩ :=
        bodyIH (EnvironmentTyped.append bindingsTyped environmentTyped)
      refine ⟨result, after, evaluated, resultTyped, ?_, ?_, unique⟩
      · simpa [bindingsTyped.length] using afterTyped.drop bindings.length
      · simpa [bindingsTyped.length] using afterFrame.drop bindings.length
    next missed => exact tailIH environment environmentTyped value valueTyped bindings body selected


theorem closed_correctness {expression : Expr} {type : Ty}
    (admitted : HasType program home [] expression type) :
    ∃ value, Evaluates program [] expression value [] ∧ ValueHasType program value type ∧
      ∀ other after, Evaluates program [] expression other after → other = value ∧ after = [] := by
  obtain ⟨value, after, evaluated, typed, afterTyped, afterFrame, unique⟩ := correctness admitted .nil
  cases afterTyped
  exact ⟨value, evaluated, typed, unique⟩

/-- Exact admission boundary, in every lexical context and at every width. -/
theorem integer_admission (context : List (String × BindingType)) (type : IntegerType) (magnitude : Nat) :
    (∃ result, HasType program home context (.integer type magnitude) result) ↔ type.Contains program.target magnitude := by
  constructor
  · rintro ⟨_, admitted⟩
    cases admitted with
    | integer fits => exact fits
  · intro fits
    exact ⟨_, .integer fits⟩

theorem character_admission (context : List (String × BindingType)) (number : Nat) :
    (∃ result, HasType program home context (.character number) result) ↔ UnicodeScalar number := by
  constructor
  · rintro ⟨_, admitted⟩
    cases admitted with
    | character valid => exact valid
  · intro valid
    exact ⟨_, .character valid⟩

/-- The original unit subset retains precisely its admission and evaluation meaning. -/
theorem unit_agreement : HasType program home [] .unit .unit ∧
    ∀ value, Evaluates program [] .unit value [] ↔ value = .unit := by
  obtain ⟨value, evaluated, _, unique⟩ := closed_correctness (program := program) (home := home) HasType.unit
  have same : value = .unit := by cases evaluated; rfl
  refine ⟨.unit, fun other => ⟨?_, ?_⟩⟩
  · intro evaluation
    exact (unique other [] evaluation).1.trans same
  · intro equal
    subst other
    exact .unit

end Grounded
