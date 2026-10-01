import Grounded.ConfigurationTyping
import Grounded.Termination

/-! General recursive safety follows from checked declarations, expression
checking and current entry values. Termination is a separate optional contract. -/
namespace Grounded

variable {program : Program} {home : Module}

/-- Preservation and progress hold at every actual execution prefix; they are
not assumptions attached to source admission. Recursive calls are permitted. -/
theorem HasType.soundness (checkedProgram : program.Checked) {context : StaticContext} {expression : Expr} {type : Ty}
    (checked : HasType program home context expression type) {environment : Environment}
    (store : EnvironmentTyped program environment context) {state : Configuration}
    (run : Run program ⟨environment, .expression expression, []⟩ state) :
    ConfigurationTyped program context (.one type) state ∧
      (Terminal state ∨ ∃ next, Step program state next) ∧
      EnvironmentFrame context environment state.outerEnvironment ∧
      (state.environment.map Prod.fst).Nodup := by
  have entry := ConfigurationTyped.entry checked store
  have current := entry.run checkedProgram run
  exact ⟨current, current.progress, entry.frame_run checkedProgram run, current.bindings_distinct⟩

/-- Any completed recursive execution has the declared result and a framed
successor store. Unlike existence of such an execution, this requires no
well-founded call expansion. -/
theorem HasType.evaluation_soundness (checkedProgram : program.Checked)
    {context : StaticContext} {expression : Expr} {type : Ty}
    (checked : HasType program home context expression type) {environment after : Environment} {value : Value}
    (store : EnvironmentTyped program environment context)
    (evaluated : Evaluates program environment expression value after) :
    ValueHasType program value type ∧ EnvironmentTyped program after context ∧
      EnvironmentFrame context environment after := by
  have entry := ConfigurationTyped.entry checked store
  have current := entry.run checkedProgram evaluated
  have framed := entry.frame_run checkedProgram evaluated
  cases current with
  | intro residents code continuation =>
    cases continuation
    cases code with
    | result resident => exact ⟨resident, residents, framed⟩


/-- Optional finite-call correctness retains actual result/store construction,
immutable framing and uniqueness. FiniteCalls is not required for general safety. -/
theorem correctness (checkedProgram : program.Checked) {context : List (BindingId × BindingType)}
    {expression : Expr} {type : Ty} (admitted : HasType program home context expression type)
    (finite : FiniteCalls program expression) {environment : Environment}
    (environmentTyped : EnvironmentTyped program environment context) :
    ∃ value after, Evaluates program environment expression value after ∧ ValueHasType program value type ∧
      EnvironmentTyped program after context ∧ EnvironmentFrame context environment after ∧
      ∀ other otherAfter, Evaluates program environment expression other otherAfter → other = value ∧ otherAfter = after := by
  obtain ⟨value, after, run, valueTyped, afterTyped, framed⟩ := admitted.executes checkedProgram finite environmentTyped
  exact ⟨value, after, run, valueTyped, afterTyped, framed, fun _ _ other => run.unique other⟩

theorem closed_correctness (checkedProgram : program.Checked) {expression : Expr} {type : Ty}
    (admitted : HasType program home [] expression type) (finite : FiniteCalls program expression) :
    ∃ value, Evaluates program [] expression value [] ∧ ValueHasType program value type ∧
      ∀ other after, Evaluates program [] expression other after → other = value ∧ after = [] := by
  obtain ⟨value, after, evaluated, typed, afterTyped, afterFrame, unique⟩ := correctness checkedProgram admitted finite .nil
  cases afterTyped
  exact ⟨value, evaluated, typed, unique⟩

/-- Exact admission boundary, in every lexical context and at every width. -/
theorem integer_admission (context : List (BindingId × BindingType)) (type : IntegerType) (magnitude : Nat) :
    (∃ result, HasType program home context (.integer type magnitude) result) ↔ type.Contains program.target magnitude := by
  constructor
  · rintro ⟨_, admitted⟩
    cases admitted with
    | integer fits => exact fits
  · intro fits
    exact ⟨_, .integer fits⟩

theorem character_admission (context : List (BindingId × BindingType)) (number : Nat) :
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
  refine ⟨.unit, fun value => ⟨?_, ?_⟩⟩
  · intro evaluation
    exact (Evaluates.unique Evaluates.unit evaluation).1
  · intro equal
    subst value
    exact .unit

end Grounded
