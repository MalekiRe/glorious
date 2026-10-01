import Grounded.Checking
import Grounded.Evaluation
import Grounded.ConfigurationTyping

/-! Termination is separate from general checking and machine safety. Structural
constants terminate from their checking derivation, independently of function-body
checking; source pattern normalization therefore has no declaration-checking cycle. -/
namespace Grounded

variable {program : Program} {home : Module}

theorem HasType.structural_value {context : List (BindingId × BindingType)} {expression : Expr} {type : Ty}
    (typed : HasType program home context expression type) :
    Structural expression → ∃ value, ValueHasType program value type ∧
      ∀ environment : Environment, ∃ after, Evaluates program environment expression value after ∧
        after.scope = environment.scope ∧ after.heap = environment.heap := by
  induction typed using HasType.rec
    (motive_2 := fun home context expressions types _ =>
      (∀ expression ∈ expressions, Structural expression) →
        ∃ values, ValuesHaveTypes program values types ∧
          ∀ environment : Environment, ∃ after, EvaluatesMany program environment expressions values after ∧
            after.scope = environment.scope ∧ after.heap = environment.heap)
    (motive_3 := fun _ _ _ _ _ _ _ => True) with
  | unit => intro _; exact ⟨_, .unit, fun environment => ⟨environment, .unit, rfl, rfl⟩⟩
  | integer fits => intro _; exact ⟨_, .integer fits, fun environment => ⟨environment, .integer fits, rfl, rfl⟩⟩
  | character valid => intro _; exact ⟨_, .character valid, fun environment => ⟨environment, .character valid, rfl, rfl⟩⟩
  | group body ih =>
    intro closed
    cases closed with | group inner =>
      obtain ⟨value, resident, runs⟩ := ih inner
      refine ⟨value, resident, ?_⟩
      intro environment
      obtain ⟨after, run, scope, heap⟩ := runs environment
      exact ⟨after, .group run, scope, heap⟩
  | read selected copyable => intro closed; cases closed
  | sequence head discard tail headIH tailIH => intro closed; cases closed
  | bind initial discard body fresh initialIH bodyIH => intro closed; cases closed
  | tuple head tail headIH tailIH =>
    intro closed
    cases closed with | tuple first rest =>
      obtain ⟨value, resident, heads⟩ := headIH first
      obtain ⟨values, residents, tails⟩ := tailIH rest
      refine ⟨_, .tuple resident residents, ?_⟩
      intro environment
      obtain ⟨middle, headRun, headScope, headHeap⟩ := heads environment
      obtain ⟨after, tailRun, tailScope, tailHeap⟩ := tails middle
      exact ⟨after, .tuple headRun tailRun, tailScope.trans headScope, tailHeap.trans headHeap⟩
  | project source discard selected ih =>
    intro closed
    cases closed with | project inner =>
      obtain ⟨aggregate, resident, runs⟩ := ih inner
      obtain ⟨value, found, valueTyped, _⟩ := selected.access resident
      refine ⟨value, valueTyped, ?_⟩
      intro environment
      obtain ⟨after, run, scope, heap⟩ := runs environment
      exact ⟨after, .project run found, scope, heap⟩
  | array residents finite size ih =>
    intro closed
    cases closed with | array elements =>
      obtain ⟨values, residents, runs⟩ := ih elements
      refine ⟨_, .array residents finite size, ?_⟩
      intro environment
      obtain ⟨after, run, scope, heap⟩ := runs environment
      exact ⟨after, .array run, scope, heap⟩
  | constant declared visible resolved structural initialized ih =>
    intro _
    obtain ⟨value, resident, runs⟩ := ih structural
    refine ⟨value, resident, ?_⟩
    intro environment
    obtain ⟨localAfter, run, scope, heap⟩ := runs (enterBindings environment.heap environment.supply [])
    have empty : localAfter.bindings = [] := congrArg AddressedScope.bindings scope
    let after : Environment := { localAfter with activation := environment.activation, bindings := environment.bindings }
    have restored : localAfter.restore environment.scope = some after := by
      simp [AddressedEnvironment.restore, releaseBindings, RuntimeHeap.retireMany, empty, after, AddressedEnvironment.scope]
    exact ⟨after, .constant declared run restored, rfl, heap⟩
  | construct declared chosen finite copyable visible access residents ih =>
    intro closed
    cases closed with | construct identity tag fields =>
      obtain ⟨values, residents, runs⟩ := ih fields
      refine ⟨_, .nominal declared chosen finite residents, ?_⟩
      intro environment
      obtain ⟨after, run, scope, heap⟩ := runs environment
      exact ⟨after, .construct run, scope, heap⟩
  | call declared visible inputs ih => intro closed; cases closed
  | assign selected discard resident rest residentIH restIH => intro closed; cases closed
  | applyPatterns arguments nonempty covered bodies argumentsIH bodiesIH => intro closed; cases closed
  | nil => exact ⟨[], .nil, fun environment => ⟨environment, .nil, rfl, rfl⟩⟩
  | @cons home context head tail first rest headTyped tailTyped headIH tailIH =>
    rename_i closed
    obtain ⟨value, resident, heads⟩ := headIH (closed head (by simp))
    obtain ⟨values, residents, tails⟩ := tailIH (fun expression member => closed expression (by simp [member]))
    refine ⟨_, .cons resident residents, ?_⟩
    intro environment
    obtain ⟨middle, headRun, headScope, headHeap⟩ := heads environment
    obtain ⟨after, tailRun, tailScope, tailHeap⟩ := tails middle
    exact ⟨after, .cons headRun tailRun, tailScope.trans headScope, tailHeap.trans headHeap⟩
  | empty => trivial
  | clause patternTyped distinct useful bodyTyped tailTyped bodyIH tailIH => trivial

theorem constant_correctness {name : String} {type : Ty}
    (checked : HasType program home [] (.constant name) type) :
    ∃ value after, Evaluates program AddressedEnvironment.empty (.constant name) value after ∧ ValueHasType program value type ∧
      ∀ other otherAfter, Evaluates program AddressedEnvironment.empty (.constant name) other otherAfter →
        other = value ∧ otherAfter = after := by
  obtain ⟨value, resident, runs⟩ := checked.structural_value (.constant name)
  obtain ⟨after, run, _, _⟩ := runs AddressedEnvironment.empty
  exact ⟨value, after, run, resident, fun _ _ other => run.unique other⟩


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

/-- Finite static call expansion constructs actual allocation, body execution
and retirement. Postconditions come from the general machine theorem. -/
theorem HasType.executes (checkedProgram : program.Checked) {context : StaticContext}
    {expression : Expr} {type : Ty} (checked : HasType program home context expression type)
    (finite : FiniteCalls program expression) {environment : Environment}
    (store : environment.Realizes program context) :
    ∃ value after, Evaluates program environment expression value after ∧ ValueHasType program value type ∧
      after.Realizes program context ∧ AddressedEnvironment.Frames context environment after := by
  induction finite generalizing home context type environment with
  | intro expression children ih =>
    have many {home : Module} {context : StaticContext} {expressions : List Expr} {types : List Ty}
        (checked : HasTypes program home context expressions types)
        (dependencies : ∀ child ∈ expressions, EvaluationDependency program child expression)
        {environment : Environment} (store : environment.Realizes program context) :
        ∃ values after, EvaluatesMany program environment expressions values after ∧ ValuesHaveTypes program values types ∧
          after.Realizes program context ∧ AddressedEnvironment.Frames context environment after := by
      induction expressions generalizing types environment with
      | nil => cases checked; exact ⟨[], environment, .nil, .nil, store, .refl _ _⟩
      | cons head tail tailIH =>
        cases checked with | cons headTyped tailTyped =>
          obtain ⟨value, middle, headRun, resident, middleTyped, middleFrame⟩ :=
            ih head (dependencies head (by simp)) headTyped store
          obtain ⟨values, after, tailRun, residents, afterTyped, afterFrame⟩ :=
            tailIH tailTyped (fun child member => dependencies child (by simp [member])) middleTyped
          exact ⟨_, after, .cons headRun tailRun, .cons resident residents, afterTyped, middleFrame.trans afterFrame⟩
    suffices ∃ value after, Evaluates program environment expression value after by
      obtain ⟨value, after, run⟩ := this
      have entry := ConfigurationTyped.entry checked store
      have current := entry.run checkedProgram run
      have framed := entry.frame_run checkedProgram run
      cases current with | intro realized code continuation =>
        cases continuation
        cases code with | result resident => exact ⟨value, after, run, resident, realized, framed⟩
    have whole := checked
    cases checked with
    | unit => exact ⟨_, environment, .unit⟩
    | integer fits => exact ⟨_, environment, .integer fits⟩
    | character valid => exact ⟨_, environment, .character valid⟩
    | group body =>
      obtain ⟨value, after, run, _⟩ := ih _ .group body store
      exact ⟨value, after, .group run⟩
    | read selected copyable =>
      cases selected with | root resolved path =>
        obtain ⟨value, found, _⟩ := store.read (place := ⟨_, _⟩) (slot := ⟨_, _⟩) resolved path
        exact ⟨value, environment, .read found⟩
    | sequence head discard tail =>
      obtain ⟨value, middle, headRun, _, middleTyped, _⟩ := ih _ .sequenceFirst head store
      obtain ⟨result, after, tailRun, _⟩ := ih _ .sequenceRest tail middleTyped
      exact ⟨result, after, .sequence headRun tailRun⟩
    | @bind home context mutable name initial body localType type initialTyped discard bodyTyped fresh =>
      obtain ⟨value, middle, initialRun, resident, middleTyped, _⟩ := ih _ .bindInitial initialTyped store
      obtain ⟨entered, _⟩ := middleTyped.extend (inputs := [⟨name, ⟨localType, mutable⟩, value⟩])
        (.cons resident .nil (by simp)) (by simpa using List.nodup_cons.mpr ⟨fresh, middleTyped.distinct⟩)
      obtain ⟨result, localAfter, bodyRun, _, localTyped, _⟩ := ih _ .bindBody bodyTyped entered
      obtain ⟨after, exited, _⟩ := localTyped.exitScope 1
      exact ⟨result, after, .bind initialRun bodyRun exited⟩
    | tuple head tail =>
      obtain ⟨value, middle, headRun, _, middleTyped, _⟩ := ih _ .tupleHead head store
      obtain ⟨values, after, tailRun, _⟩ := many tail (fun _ member => .tupleTail member) middleTyped
      exact ⟨_, after, .tuple headRun tailRun⟩
    | project source discard selected =>
      obtain ⟨aggregate, after, run, resident, _⟩ := ih _ .project source store
      obtain ⟨value, found, _⟩ := selected.access resident
      exact ⟨value, after, .project run found⟩
    | array residents finite size =>
      obtain ⟨values, after, run, _⟩ := many residents (fun _ member => .array member) store
      exact ⟨_, after, .array run⟩
    | constant declared visible resolved structural initialized =>
      obtain ⟨value, _, runs⟩ := whole.structural_value (.constant _)
      obtain ⟨after, run, _⟩ := runs environment
      exact ⟨value, after, run⟩
    | construct declared chosen finite copyable visible access residents =>
      obtain ⟨values, after, run, _⟩ := many residents (fun _ member => .construct member) store
      exact ⟨_, after, .construct run⟩
    | @call home context identity arguments declaration declared visible inputs =>
      obtain ⟨values, middle, inputRun, residents, middleTyped, _⟩ := many inputs (fun _ member => .callInput member) store
      have declarationChecked := checkedProgram _ _ declared
      obtain ⟨bindings, prepared, inputsTyped, slots⟩ := prepareBindings.progress residents declarationChecked.distinct
      have bodyTyped : HasType program declaration.home (bindings.map fun input => (input.name, input.slot))
          declaration.body declaration.result := by rw [slots]; exact declarationChecked.body
      obtain ⟨entered, _⟩ := inputsTyped.enter middle.heap middle.supply
      obtain ⟨value, localAfter, bodyRun, _⟩ := ih _ (.callBody declared) bodyTyped entered
      have invocation := ConfigurationTyped.invoke middleTyped .nil inputsTyped bodyTyped
        (by rw [slots]; exact declarationChecked.disposable)
      have returned := invocation.run checkedProgram (Run.extend bodyRun [.restore middle.scope])
      obtain done | ⟨next, stepped⟩ := returned.progress
      · cases done
      · cases stepped with | restore restored => exact ⟨value, _, .call declared prepared inputRun bodyRun restored⟩
    | assign selected discard resident rest =>
      obtain ⟨value, middle, valueRun, valueTyped, middleTyped, _⟩ := ih _ .assignValue resident store
      cases selected with | root resolved path =>
        obtain ⟨updated, written, updatedTyped, _⟩ := middleTyped.write (place := ⟨_, _⟩)
          (slot := ⟨_, true⟩) resolved path rfl valueTyped
        obtain ⟨result, after, restRun, _⟩ := ih _ .assignRest rest updatedTyped
        exact ⟨result, after, .assign valueRun written restRun⟩
    | applyPatterns arguments nonempty covered bodies =>
      obtain ⟨values, middle, argumentsRun, residents, middleTyped, _⟩ := many arguments (fun _ member => .patternInput member) store
      obtain ⟨bindings, body, selected⟩ := covered.selectArm residents.argument
      obtain ⟨locals, pattern, member, inputsTyped, slots, discard, bodyTyped, distinct⟩ := bodies.selected residents.argument selected
      obtain ⟨entered, _⟩ := middleTyped.extend inputsTyped (by
        rw [← slots] at distinct
        simpa only [List.map_append, List.map_map, Function.comp_def] using distinct)
      rw [slots] at entered
      obtain ⟨value, localAfter, bodyRun, _, localTyped, _⟩ := ih _ (.patternBody member) bodyTyped entered
      obtain ⟨after, exited, _⟩ := localTyped.exitScope bindings.length
      exact ⟨value, after, .applyPatterns argumentsRun selected bodyRun exited⟩


end Grounded
