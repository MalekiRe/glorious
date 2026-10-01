import Grounded.ConfigurationTyping
import Grounded.Evaluation

/-! Source checking constructs entry realization and proves safety of every
execution prefix. The finite-call fragment additionally has terminating correctness. -/
namespace Grounded

variable {program : Program} {home : Module}

/-- Safety of every actual execution prefix follows from checking and current
entry values. Preservation and progress are conclusions, not admission fields. -/
theorem HasType.soundness {context : StaticContext} {expression : Expr} {type : Ty}
    (checked : HasType program home context expression type) {environment : Environment}
    (store : EnvironmentTyped program environment context) {state : Configuration}
    (run : Run program ⟨environment, .expression expression, []⟩ state) :
    ConfigurationTyped program context (.one type) state ∧
      (Terminal state ∨ ∃ next, Step program state next) := by
  have current := (ConfigurationTyped.entry checked store).run run
  exact ⟨current, current.progress⟩


/-- Checking the finite-call fragment constructs a machine run and its storage
postconditions. Operational determinism is proved independently. -/
theorem HasType.executes {context : List (String × BindingType)} {expression : Expr} {type : Ty}
    (admitted : HasType program home context expression type)
    {environment : Environment} (environmentTyped : EnvironmentTyped program environment context) :
    ∃ value after, Evaluates program environment expression value after ∧ ValueHasType program value type ∧
      EnvironmentTyped program after context ∧ EnvironmentFrame context environment after := by
  induction admitted using HasType.rec
    (motive_2 := fun home context expressions types _ =>
      ∀ environment, EnvironmentTyped program environment context →
        ∃ values after, EvaluatesMany program environment expressions values after ∧ ValuesHaveTypes program values types ∧
          EnvironmentTyped program after context ∧ EnvironmentFrame context environment after)
    (motive_3 := fun home context subject result previous arms _ =>
      ∀ environment, EnvironmentTyped program environment context →
      ∀ value, ValueHasType program value subject → ∀ bindings body,
        selectArm value arms = some (bindings, body) →
        ∃ resultValue after, Evaluates program (bindings ++ environment) body resultValue after ∧
          ValueHasType program resultValue result ∧ EnvironmentTyped program (after.drop bindings.length) context ∧
          EnvironmentFrame context environment (after.drop bindings.length))
    generalizing environment with
  | unit =>
    exact ⟨.unit, environment, .unit, .unit, environmentTyped, environmentTyped.frame_refl⟩
  | integer fits =>
    exact ⟨_, environment, .integer fits, .integer fits, environmentTyped, environmentTyped.frame_refl⟩
  | character valid =>
    exact ⟨_, environment, .character valid, .character valid, environmentTyped, environmentTyped.frame_refl⟩
  | constant declared visible resolved structural initialized ih =>
    obtain ⟨value, after, evaluated, typed, afterTyped, afterFrame⟩ := ih EnvironmentTyped.nil
    cases afterTyped
    exact ⟨value, environment, .constant declared evaluated, typed, environmentTyped, environmentTyped.frame_refl⟩
  | @call home context identity arguments declaration declared visible distinct discard inputs body inputsIH bodyIH =>
    obtain ⟨values, middle, inputsEval, inputsTyped, middleTyped, middleFrame⟩ := inputsIH environment environmentTyped
    obtain ⟨value, localAfter, bodyEval, valueTyped, _, _⟩ :=
      bodyIH (EnvironmentTyped.parameters declaration.parameters values inputsTyped)
    exact ⟨value, middle, .call declared inputsEval bodyEval, valueTyped, middleTyped, middleFrame⟩
  | applyPatterns argumentsTyped nonempty covered bodies argumentsIH bodiesIH =>
    obtain ⟨values, middle, argumentsEval, valuesTyped, middleTyped, middleFrame⟩ := argumentsIH environment environmentTyped
    have subjectTyped := valuesTyped.argument
    obtain ⟨bindings, body, selected⟩ := covered.selectArm subjectTyped
    obtain ⟨value, after, bodyEval, valueTyped, afterTyped, afterFrame⟩ :=
      bodiesIH middle middleTyped _ subjectTyped bindings body selected
    exact ⟨value, after.drop bindings.length, .applyPatterns argumentsEval selected bodyEval, valueTyped, afterTyped, middleFrame.trans afterFrame⟩
  | group typed ih =>
    obtain ⟨value, after, evaluated, valueTyped, afterTyped, afterFrame⟩ := ih environmentTyped
    exact ⟨value, after, .group evaluated, valueTyped, afterTyped, afterFrame⟩
  | read selected copyable =>
    obtain ⟨value, selectedValue, valueTyped⟩ := environmentTyped.readPlace selected
    exact ⟨value, environment, .read selectedValue, valueTyped, environmentTyped, environmentTyped.frame_refl⟩
  | sequence head drop tail headIH tailIH =>
    obtain ⟨discarded, middle, headEval, _, middleTyped, middleFrame⟩ := headIH environmentTyped
    obtain ⟨value, after, tailEval, valueTyped, afterTyped, afterFrame⟩ := tailIH middleTyped
    exact ⟨value, after, .sequence headEval tailEval, valueTyped, afterTyped, middleFrame.trans afterFrame⟩
  | bind initialized drop annotated continued initialIH bodyIH =>
    obtain ⟨resident, middle, initialEval, residentTyped, middleTyped, middleFrame⟩ := initialIH environmentTyped
    obtain ⟨value, after, bodyEval, valueTyped, afterTyped, afterFrame⟩ := bodyIH (.cons residentTyped middleTyped)
    exact ⟨value, after.drop 1, .bind initialEval bodyEval, valueTyped, afterTyped.drop 1, middleFrame.trans (afterFrame.drop 1)⟩
  | assign selected discard resident continued residentIH bodyIH =>
    obtain ⟨replacement, middle, evaluated, residentTyped, middleTyped, middleFrame⟩ := residentIH environmentTyped
    obtain ⟨updated, written, updatedTyped, updatedFrame, _⟩ := middleTyped.writePlace selected residentTyped
    obtain ⟨value, after, bodyEval, valueTyped, afterTyped, afterFrame⟩ := bodyIH updatedTyped
    exact ⟨value, after, .assign evaluated written bodyEval, valueTyped, afterTyped, middleFrame.trans (updatedFrame.trans afterFrame)⟩
  | tuple head tail headIH tailIH =>
    obtain ⟨first, middle, headEval, headTyped, middleTyped, middleFrame⟩ := headIH environmentTyped
    obtain ⟨rest, after, tailEval, tailTyped, afterTyped, afterFrame⟩ := tailIH middle middleTyped
    exact ⟨.tuple first rest, after, .tuple headEval tailEval, .tuple headTyped tailTyped, afterTyped, middleFrame.trans afterFrame⟩
  | array residents elementValid size ih =>
    obtain ⟨values, after, evaluated, typed, afterTyped, afterFrame⟩ := ih environment environmentTyped
    exact ⟨.array values, after, .array evaluated, .array typed elementValid size, afterTyped, afterFrame⟩
  | project source discard selected sourceIH =>
    obtain ⟨aggregate, after, sourceEval, aggregateTyped, afterTyped, afterFrame⟩ := sourceIH environmentTyped
    obtain ⟨value, fieldSelected, valueTyped, _⟩ := selected.access aggregateTyped
    exact ⟨value, after, .project sourceEval fieldSelected, valueTyped, afterTyped, afterFrame⟩
  | construct declared chosen finite copyable visible access residents ih =>
    obtain ⟨values, after, evaluated, typed, afterTyped, afterFrame⟩ := ih environment environmentTyped
    exact ⟨_, after, .construct evaluated, .nominal declared chosen finite typed, afterTyped, afterFrame⟩
  | nil =>
    rename_i environment environmentTyped
    exact ⟨[], environment, .nil, .nil, environmentTyped, environmentTyped.frame_refl⟩
  | cons head tail headIH tailIH =>
    rename_i environment environmentTyped
    obtain ⟨first, middle, headEval, headTyped, middleTyped, middleFrame⟩ := headIH environmentTyped
    obtain ⟨rest, after, tailEval, tailTyped, afterTyped, afterFrame⟩ := tailIH middle middleTyped
    exact ⟨first :: rest, after, .cons headEval tailEval, .cons headTyped tailTyped, afterTyped, middleFrame.trans afterFrame⟩
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
      obtain ⟨result, after, evaluated, resultTyped, afterTyped, afterFrame⟩ :=
        bodyIH (EnvironmentTyped.append bindingsTyped environmentTyped)
      refine ⟨result, after, evaluated, resultTyped, ?_, ?_⟩
      · simpa [bindingsTyped.length] using afterTyped.drop bindings.length
      · simpa [bindingsTyped.length] using afterFrame.drop bindings.length
    next missed => exact tailIH environment environmentTyped value valueTyped bindings body selected

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
  obtain ⟨value, after, run, valueTyped, afterTyped, framed⟩ := admitted.executes environmentTyped
  exact ⟨value, after, run, valueTyped, afterTyped, framed, fun _ _ other => run.unique other⟩

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
  have same : value = .unit := (Evaluates.unique evaluated Evaluates.unit).1.symm
  refine ⟨.unit, fun other => ⟨?_, ?_⟩⟩
  · intro evaluation
    exact (unique other [] evaluation).1.trans same
  · intro equal
    subst other
    exact .unit

end Grounded
