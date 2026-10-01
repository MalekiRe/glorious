import Grounded.Checking
import Grounded.Evaluation

/-! Termination is separate from general checking and machine safety. Structural
constants terminate from their checking derivation, independently of function-body
checking; source pattern normalization therefore has no declaration-checking cycle. -/
namespace Grounded

variable {program : Program} {home : Module}

theorem HasType.structural_value {context : List (BindingId × BindingType)} {expression : Expr} {type : Ty}
    (typed : HasType program home context expression type) :
    Structural expression → ∃ value, Evaluates program [] expression value [] ∧ ValueHasType program value type := by
  induction typed using HasType.rec
    (motive_2 := fun home context expressions types _ =>
      (∀ expression ∈ expressions, Structural expression) →
        ∃ values, EvaluatesMany program [] expressions values [] ∧ ValuesHaveTypes program values types)
    (motive_3 := fun _ _ _ _ _ _ _ => True) with
  | unit => intro closed; exact ⟨_, .unit, .unit⟩
  | integer fits => intro closed; exact ⟨_, .integer fits, .integer fits⟩
  | character valid => intro closed; exact ⟨_, .character valid, .character valid⟩
  | group body ih =>
    intro closed
    cases closed with | group inner =>
      obtain ⟨value, run, resident⟩ := ih inner
      exact ⟨value, .group run, resident⟩
  | read selected copyable => intro closed; cases closed
  | sequence head discard tail headIH tailIH => intro closed; cases closed
  | bind initial discard body fresh initialIH bodyIH => intro closed; cases closed
  | tuple head tail headIH tailIH =>
    intro closed
    cases closed with | tuple first rest =>
      obtain ⟨value, run, resident⟩ := headIH first
      obtain ⟨values, runs, residents⟩ := tailIH rest
      exact ⟨_, .tuple run runs, .tuple resident residents⟩
  | project source discard selected ih =>
    intro closed
    cases closed with | project inner =>
      obtain ⟨aggregate, run, resident⟩ := ih inner
      obtain ⟨value, found, valueTyped, _⟩ := selected.access resident
      exact ⟨value, .project run found, valueTyped⟩
  | array residents finite size ih =>
    intro closed
    cases closed with | array elements =>
      obtain ⟨values, runs, residents⟩ := ih elements
      exact ⟨_, .array runs, .array residents finite size⟩
  | constant declared visible resolved structural initialized ih =>
    intro closed
    obtain ⟨value, run, resident⟩ := ih structural
    exact ⟨value, .constant declared run, resident⟩
  | construct declared chosen finite copyable visible access residents ih =>
    intro closed
    cases closed with | construct identity tag fields =>
      obtain ⟨values, runs, residents⟩ := ih fields
      exact ⟨_, .construct runs, .nominal declared chosen finite residents⟩
  | call declared visible inputs ih => intro closed; cases closed
  | assign selected discard resident rest residentIH restIH => intro closed; cases closed
  | applyPatterns arguments nonempty covered bodies argumentsIH bodiesIH => intro closed; cases closed
  | nil => exact ⟨[], .nil, .nil⟩
  | @cons home context head tail first rest headTyped tailTyped headIH tailIH =>
    rename_i closed
    obtain ⟨value, run, resident⟩ := headIH (closed head (by simp))
    obtain ⟨values, runs, residents⟩ := tailIH (fun expression member => closed expression (by simp [member]))
    exact ⟨_, .cons run runs, .cons resident residents⟩
  | empty => trivial
  | clause patternTyped distinct useful bodyTyped tailTyped bodyIH tailIH => trivial

theorem constant_correctness {name : String} {type : Ty}
    (checked : HasType program home [] (.constant name) type) :
    ∃ value, Evaluates program [] (.constant name) value [] ∧ ValueHasType program value type ∧
      ∀ other after, Evaluates program [] (.constant name) other after → other = value ∧ after = [] := by
  obtain ⟨value, run, resident⟩ := checked.structural_value (.constant name)
  exact ⟨value, run, resident, fun _ _ other => run.unique other⟩

/-- Static expansion of function calls and proper subexpressions. All candidate
arm bodies are included. Constants need no expansion here: structural checking
already proves their termination. This relation asserts no runtime success. -/
inductive EvaluationDependency (program : Program) : Expr → Expr → Prop where
  | group {body : Expr} : EvaluationDependency program body (.group body)
  | sequenceFirst {first rest : Expr} : EvaluationDependency program first (.sequence first rest)
  | sequenceRest {first rest : Expr} : EvaluationDependency program rest (.sequence first rest)
  | bindInitial {mutable : Bool} {name : BindingId} {localType : Ty} {initial body : Expr} :
      EvaluationDependency program initial (.bind mutable name localType initial body)
  | bindBody {mutable : Bool} {name : BindingId} {localType : Ty} {initial body : Expr} :
      EvaluationDependency program body (.bind mutable name localType initial body)
  | tupleHead {head : Expr} {tail : List Expr} : EvaluationDependency program head (.tuple head tail)
  | tupleTail {head expression : Expr} {tail : List Expr} (member : expression ∈ tail) :
      EvaluationDependency program expression (.tuple head tail)
  | project {body : Expr} {key : FieldKey} : EvaluationDependency program body (.project body key)
  | array {expression : Expr} {elements : List Expr} (member : expression ∈ elements) :
      EvaluationDependency program expression (.array elements)
  | construct {identity : Nat} {tag : Option Nat} {expression : Expr} {fields : List Expr}
      (member : expression ∈ fields) : EvaluationDependency program expression (.construct identity tag fields)
  | callInput {identity : Nat} {expression : Expr} {arguments : List Expr} (member : expression ∈ arguments) :
      EvaluationDependency program expression (.call identity arguments)
  | callBody {identity : Nat} {arguments : List Expr} {declaration : FunctionDecl}
      (declared : program.functions identity = some declaration) :
      EvaluationDependency program declaration.body (.call identity arguments)
  | assignValue {place : Place} {value rest : Expr} : EvaluationDependency program value (.assign place value rest)
  | assignRest {place : Place} {value rest : Expr} : EvaluationDependency program rest (.assign place value rest)
  | patternInput {inputs : List Ty} {expression : Expr} {arguments : List Expr} {arms : List (Pattern × Expr)}
      (member : expression ∈ arguments) : EvaluationDependency program expression (.applyPatterns inputs arguments arms)
  | patternBody {inputs : List Ty} {arguments : List Expr} {arms : List (Pattern × Expr)} {pattern : Pattern} {body : Expr}
      (member : (pattern, body) ∈ arms) : EvaluationDependency program body (.applyPatterns inputs arguments arms)

/-- Optional well-founded call expansion, not a premise of ordinary checking or
progress. Recursive programs may be checked without possessing this certificate. -/
def FiniteCalls (program : Program) (expression : Expr) : Prop := Acc (EvaluationDependency program) expression

/-- Well-founded static call expansion recovers the terminating-fragment
contract. General recursive safety does not require this optional hypothesis. -/
theorem HasType.executes (checkedProgram : program.Checked) {context : List (BindingId × BindingType)}
    {expression : Expr} {type : Ty} (checked : HasType program home context expression type)
    (finite : FiniteCalls program expression) {environment : Environment}
    (store : EnvironmentTyped program environment context) :
    ∃ value after, Evaluates program environment expression value after ∧ ValueHasType program value type ∧
      EnvironmentTyped program after context ∧ EnvironmentFrame context environment after := by
  induction finite generalizing home context type environment with
  | intro expression children ih =>
    have many {home : Module} {context : List (BindingId × BindingType)} {expressions : List Expr} {types : List Ty}
        (checked : HasTypes program home context expressions types)
        (dependencies : ∀ child ∈ expressions, EvaluationDependency program child expression)
        {environment : Environment} (store : EnvironmentTyped program environment context) :
        ∃ values after, EvaluatesMany program environment expressions values after ∧ ValuesHaveTypes program values types ∧
          EnvironmentTyped program after context ∧ EnvironmentFrame context environment after := by
      induction expressions generalizing types environment with
      | nil => cases checked; exact ⟨[], environment, .nil, .nil, store, store.frame_refl⟩
      | cons head tail tailIH =>
        cases checked with | cons headTyped tailTyped =>
          obtain ⟨value, middle, headRun, resident, middleTyped, middleFrame⟩ :=
            ih head (dependencies head (by simp)) headTyped store
          obtain ⟨values, after, tailRun, residents, afterTyped, afterFrame⟩ :=
            tailIH tailTyped (fun child member => dependencies child (by simp [member])) middleTyped
          exact ⟨_, after, .cons headRun tailRun, .cons resident residents, afterTyped, middleFrame.trans afterFrame⟩
    cases checked with
    | unit => exact ⟨_, environment, .unit, .unit, store, store.frame_refl⟩
    | integer fits => exact ⟨_, environment, .integer fits, .integer fits, store, store.frame_refl⟩
    | character valid => exact ⟨_, environment, .character valid, .character valid, store, store.frame_refl⟩
    | group body =>
      obtain ⟨value, after, run, resident, afterTyped, frame⟩ := ih _ .group body store
      exact ⟨value, after, .group run, resident, afterTyped, frame⟩
    | read selected copyable =>
      obtain ⟨value, found, resident⟩ := store.readPlace selected
      exact ⟨value, environment, .read found, resident, store, store.frame_refl⟩
    | sequence head discard tail =>
      obtain ⟨value, middle, headRun, _, middleTyped, middleFrame⟩ := ih _ .sequenceFirst head store
      obtain ⟨result, after, tailRun, resident, afterTyped, afterFrame⟩ := ih _ .sequenceRest tail middleTyped
      exact ⟨result, after, .sequence headRun tailRun, resident, afterTyped, middleFrame.trans afterFrame⟩
    | bind initial discard body fresh =>
      obtain ⟨value, middle, initialRun, resident, middleTyped, middleFrame⟩ := ih _ .bindInitial initial store
      obtain ⟨result, after, bodyRun, resultTyped, afterTyped, afterFrame⟩ := ih _ .bindBody body (.cons resident middleTyped fresh)
      exact ⟨result, after.drop 1, .bind initialRun bodyRun, resultTyped,
        afterTyped.drop 1, middleFrame.trans (afterFrame.drop 1)⟩
    | tuple head tail =>
      obtain ⟨value, middle, headRun, resident, middleTyped, middleFrame⟩ := ih _ .tupleHead head store
      obtain ⟨values, after, tailRun, residents, afterTyped, afterFrame⟩ := many tail (fun _ member => .tupleTail member) middleTyped
      exact ⟨_, after, .tuple headRun tailRun, .tuple resident residents, afterTyped, middleFrame.trans afterFrame⟩
    | project source discard selected =>
      obtain ⟨aggregate, after, run, resident, afterTyped, frame⟩ := ih _ .project source store
      obtain ⟨value, found, valueTyped, _⟩ := selected.access resident
      exact ⟨value, after, .project run found, valueTyped, afterTyped, frame⟩
    | array residents finite size =>
      obtain ⟨values, after, run, typed, afterTyped, frame⟩ := many residents (fun _ member => .array member) store
      exact ⟨_, after, .array run, .array typed finite size, afterTyped, frame⟩
    | constant declared visible resolved structural initialized =>
      obtain ⟨value, run, resident⟩ := initialized.structural_value structural
      exact ⟨value, environment, .constant declared run, resident, store, store.frame_refl⟩
    | construct declared chosen finite copyable visible access residents =>
      obtain ⟨values, after, run, typed, afterTyped, frame⟩ := many residents (fun _ member => .construct member) store
      exact ⟨_, after, .construct run, .nominal declared chosen finite typed, afterTyped, frame⟩
    | @call home context identity arguments declaration declared visible inputs =>
      obtain ⟨values, middle, inputRun, residents, middleTyped, middleFrame⟩ := many inputs (fun _ member => .callInput member) store
      obtain ⟨bindings, prepared, bindingsTyped⟩ :=
        EnvironmentTyped.parameters _ _ residents (checkedProgram _ _ declared).distinct
      obtain ⟨value, after, bodyRun, resident, _, _⟩ :=
        ih _ (.callBody declared) (checkedProgram _ _ declared).body
          bindingsTyped
      exact ⟨value, middle, .call declared prepared inputRun bodyRun, resident, middleTyped, middleFrame⟩
    | assign selected discard resident rest =>
      obtain ⟨value, middle, valueRun, valueTyped, middleTyped, middleFrame⟩ := ih _ .assignValue resident store
      obtain ⟨updated, written, updatedTyped, updatedFrame, _⟩ := middleTyped.writePlace selected valueTyped
      obtain ⟨result, after, restRun, resultTyped, afterTyped, afterFrame⟩ := ih _ .assignRest rest updatedTyped
      exact ⟨result, after, .assign valueRun written restRun, resultTyped, afterTyped,
        middleFrame.trans (updatedFrame.trans afterFrame)⟩
    | applyPatterns arguments nonempty covered bodies =>
      obtain ⟨values, middle, argumentsRun, residents, middleTyped, middleFrame⟩ := many arguments (fun _ member => .patternInput member) store
      obtain ⟨bindings, body, selected⟩ := covered.selectArm residents.argument
      obtain ⟨locals, pattern, member, inputsTyped, slots, discard, bodyTyped, distinct⟩ := bodies.selected residents.argument selected
      have bindingsTyped := inputsTyped.environment
      rw [slots] at bindingsTyped
      obtain ⟨value, after, bodyRun, resident, afterTyped, afterFrame⟩ :=
        ih _ (.patternBody member) bodyTyped (bindingsTyped.append middleTyped distinct)
      refine ⟨value, after.drop bindings.length, .applyPatterns argumentsRun selected bodyRun, resident, ?_, middleFrame.trans ?_⟩
      · have length := bindingsTyped.length
        simp only [List.length_map] at length
        simpa [length] using afterTyped.drop bindings.length
      · have length := bindingsTyped.length
        simp only [List.length_map] at length
        simpa [length] using afterFrame.drop bindings.length


end Grounded
