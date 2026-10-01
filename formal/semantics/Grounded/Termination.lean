import Grounded.Checking
import Grounded.Evaluation
import Grounded.ConfigurationTyping

/-! Termination is separate from general checking and machine safety. Structural
constants terminate from their checking derivation, independently of function-body
checking; source pattern normalization therefore has no declaration-checking cycle. -/
namespace Grounded

variable {program : Program} {home : Module}

theorem HasType.structural_value {context final : FlowContext} {expression : Expr} {type : Ty}
    (typed : HasType program home context expression type final) :
    Structural expression → ∃ value, ValueHasType program value type ∧
      ∀ environment : Environment, ∃ after, Evaluates program environment expression value after ∧
        after.scope = environment.scope ∧ after.heap = environment.heap := by
  induction typed using HasType.rec
    (motive_2 := fun home context expressions types final _ =>
      (∀ expression ∈ expressions, Structural expression) →
        ∃ values, ValuesHaveTypes program values types ∧
          ∀ environment : Environment, ∃ after, EvaluatesMany program environment expressions values after ∧
            after.scope = environment.scope ∧ after.heap = environment.heap)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True) with
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
  | read selected path selection ready copyable => intro closed; cases closed
  | move selected path selection ready mask context => intro closed; cases closed
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
  | construct declared chosen finite visible access residents ih =>
    intro closed
    cases closed with | construct identity tag fields =>
      obtain ⟨values, residents, runs⟩ := ih fields
      refine ⟨_, .nominal declared chosen finite residents, ?_⟩
      intro environment
      obtain ⟨after, run, scope, heap⟩ := runs environment
      exact ⟨after, .construct run, scope, heap⟩
  | call declared visible inputs ih => intro closed; cases closed
  | assign resident selected path writable selection discard mask context rest residentIH restIH => intro closed; cases closed
  | applyPatterns arguments nonempty covered bodies argumentsIH bodiesIH => intro closed; cases closed
  | nil => exact ⟨[], .nil, fun environment => ⟨environment, .nil, rfl, rfl⟩⟩
  | @cons home before middle after head tail first rest headTyped tailTyped headIH tailIH =>
    rename_i closed
    obtain ⟨value, resident, heads⟩ := headIH (closed head (by simp))
    obtain ⟨values, residents, tails⟩ := tailIH (fun expression member => closed expression (by simp [member]))
    refine ⟨_, .cons resident residents, ?_⟩
    intro environment
    obtain ⟨middle, headRun, headScope, headHeap⟩ := heads environment
    obtain ⟨after, tailRun, tailScope, tailHeap⟩ := tails middle
    exact ⟨after, .cons headRun tailRun, tailScope.trans headScope, tailHeap.trans headHeap⟩
  | empty => trivial
  | clause patternTyped distinct useful bodyTyped localSlots disposable tailTyped bodyIH tailIH => trivial

theorem constant_correctness {name : String} {type : Ty}
    (checked : HasType program home [] (.constant name) type []) :
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

/-- Finite static call expansion constructs actual allocation, moves,
restoration and retirement. Post-state typing is general machine preservation. -/
theorem HasType.executes (checkedProgram : program.Checked) {context final : FlowContext}
    {expression : Expr} {type : Ty} (checked : HasType program home context expression type final)
    (finite : FiniteCalls program expression) {environment : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
    (issued : environment.supply.Issued environment.activation) :
    ∃ value after, Evaluates program environment expression value after ∧ ValueHasType program value type ∧
      BindingMap.Typed program after.heap after.activation after.bindings final ∧
      after.supply.Issued after.activation ∧ after.scope = environment.scope := by
  induction finite generalizing home context final type environment with
  | intro expression children ih =>
    have many {home : Module} {context final : FlowContext} {expressions : List Expr} {types : List Ty}
        (checked : HasTypes program home context expressions types final)
        (dependencies : ∀ child ∈ expressions, EvaluationDependency program child expression)
        {environment : Environment}
        (store : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
        (issued : environment.supply.Issued environment.activation) :
        ∃ values after, EvaluatesMany program environment expressions values after ∧ ValuesHaveTypes program values types ∧
          BindingMap.Typed program after.heap after.activation after.bindings final ∧
          after.supply.Issued after.activation := by
      induction expressions generalizing context final types environment with
      | nil => cases checked; exact ⟨[], environment, .nil, .nil, store, issued⟩
      | cons head tail tailIH =>
        cases checked with | cons headTyped tailTyped =>
          obtain ⟨value, middle, headRun, resident, middleTyped, middleIssued, _⟩ :=
            ih head (dependencies head (by simp)) headTyped store issued
          obtain ⟨values, after, tailRun, residents, afterTyped, afterIssued⟩ :=
            tailIH tailTyped (fun child member => dependencies child (by simp [member])) middleTyped middleIssued
          exact ⟨_, after, .cons headRun tailRun, .cons resident residents, afterTyped, afterIssued⟩
    suffices ∃ value after, Evaluates program environment expression value after by
      obtain ⟨value, after, run⟩ := this
      have current := (ConfigurationTyped.entry checked store issued).run checkedProgram run
      have scope := run.outer_scope
      cases current with | intro realized afterIssued code continuation =>
        cases continuation
        cases code with | result resident => exact ⟨value, after, run, resident, realized, afterIssued, scope⟩
    have whole := checked
    cases checked with
    | unit => exact ⟨_, environment, .unit⟩
    | integer fits => exact ⟨_, environment, .integer fits⟩
    | character valid => exact ⟨_, environment, .character valid⟩
    | group body =>
      obtain ⟨value, after, run, _⟩ := ih _ .group body store issued
      exact ⟨value, after, .group run⟩
    | read selected path selection ready copyable =>
      obtain ⟨value, found, _⟩ := AddressedEnvironment.read.progress store selected path selection ready
      exact ⟨value, environment, .read found⟩
    | move selected path selection ready mask context =>
      obtain ⟨value, after, _, _, taken, _⟩ := AddressedEnvironment.take.progress store selected path selection ready
      exact ⟨value, after, .move taken⟩
    | sequence head discard tail =>
      obtain ⟨value, middle, headRun, _, middleTyped, middleIssued, _⟩ := ih _ .sequenceFirst head store issued
      obtain ⟨result, after, tailRun, _⟩ := ih _ .sequenceRest tail middleTyped middleIssued
      exact ⟨result, after, .sequence headRun tailRun⟩
    | @bind home before middleContext afterContext mutable name initial body localType type finalMask initialTyped discard bodyTyped fresh =>
      obtain ⟨value, middle, initialRun, resident, middleTyped, middleIssued, _⟩ := ih _ .bindInitial initialTyped store issued
      obtain ⟨entered, _, _, _⟩ := AddressedEnvironment.extend.typed middleTyped
        (inputs := [⟨name, ⟨localType, mutable⟩, value⟩]) (.cons resident .nil (by simp))
        (by simpa using List.nodup_cons.mpr ⟨fresh, middleTyped.context_distinct⟩)
      obtain ⟨result, localAfter, bodyRun, _, localTyped, _, _⟩ := ih _ .bindBody bodyTyped entered middleIssued
      obtain ⟨after, exited, _⟩ := AddressedEnvironment.exitScope.progress localTyped 1
      exact ⟨result, after, .bind initialRun bodyRun exited⟩
    | tuple head tail =>
      obtain ⟨value, middle, headRun, _, middleTyped, middleIssued, _⟩ := ih _ .tupleHead head store issued
      obtain ⟨values, after, tailRun, _⟩ := many tail (fun _ member => .tupleTail member) middleTyped middleIssued
      exact ⟨_, after, .tuple headRun tailRun⟩
    | project source discard selected =>
      obtain ⟨aggregate, after, run, resident, _⟩ := ih _ .project source store issued
      obtain ⟨value, found, _⟩ := selected.access resident
      exact ⟨value, after, .project run found⟩
    | array residents finite size =>
      obtain ⟨values, after, run, _⟩ := many residents (fun _ member => .array member) store issued
      exact ⟨_, after, .array run⟩
    | constant declared visible resolved structural initialized =>
      obtain ⟨value, _, runs⟩ := whole.structural_value (.constant _)
      obtain ⟨after, run, _⟩ := runs environment
      exact ⟨value, after, run⟩
    | construct declared chosen finite visible access residents =>
      obtain ⟨values, after, run, _⟩ := many residents (fun _ member => .construct member) store issued
      exact ⟨_, after, .construct run⟩
    | @call home before afterContext identity arguments declaration declared visible inputs =>
      obtain ⟨values, middle, inputRun, residents, middleTyped, middleIssued⟩ :=
        many inputs (fun _ member => .callInput member) store issued
      have declarationChecked := checkedProgram _ _ declared
      obtain ⟨bindings, prepared, inputsTyped, slots⟩ := prepareBindings.progress residents declarationChecked.distinct
      obtain ⟨locals, checkedBody, discard⟩ := declarationChecked.body
      have bodyTyped : HasType program declaration.home (bindings.map BindingInput.state)
          declaration.body declaration.result locals := by
        rw [← slots] at checkedBody
        simp only [initializedContext, List.map_map, Function.comp_def] at checkedBody
        exact checkedBody
      have entered := enterBindings.typed inputsTyped middle.heap middle.supply
      obtain ⟨value, localAfter, bodyRun, _⟩ := ih _ (.callBody declared) bodyTyped entered middle.supply.allocate_issued
      have invocation := ConfigurationTyped.invoke middleTyped middleIssued .nil inputsTyped bodyTyped discard
      have returned := invocation.run checkedProgram (Run.extend bodyRun [.restore middle.scope])
      obtain done | ⟨next, stepped⟩ := returned.progress
      · cases done
      · cases stepped with | restore restored => exact ⟨value, _, .call declared prepared inputRun bodyRun restored⟩
    | assign resident selected path writable selection discard mask context rest =>
      obtain ⟨value, middle, valueRun, valueTyped, middleTyped, middleIssued, _⟩ := ih _ .assignValue resident store issued
      obtain ⟨updated, updatedMask, updatedContext, written, maskWritten, contextWritten, updatedTyped,
        _, scope, supply, _, _, _⟩ := AddressedEnvironment.write.progress middleTyped selected path valueTyped
      cases Option.some.inj (mask.symm.trans maskWritten)
      cases Option.some.inj (context.symm.trans contextWritten)
      have activation := congrArg AddressedScope.activation scope
      simp only [AddressedEnvironment.scope] at activation
      have updatedIssued : updated.supply.Issued updated.activation := by rw [supply, activation]; exact middleIssued
      obtain ⟨result, after, restRun, _⟩ := ih _ .assignRest rest updatedTyped updatedIssued
      exact ⟨result, after, .assign valueRun written restRun⟩
    | applyPatterns arguments nonempty covered bodies =>
      obtain ⟨values, middle, argumentsRun, residents, middleTyped, middleIssued⟩ :=
        many arguments (fun _ member => .patternInput member) store issued
      obtain ⟨bindings, body, selected⟩ := covered.selectArm residents.argument
      obtain ⟨locals, localsAfter, pattern, member, inputsTyped, slots, discard, bodyTyped, localSlots, distinct⟩ :=
        bodies.selected residents.argument selected
      obtain ⟨entered, _, _, _⟩ := AddressedEnvironment.extend.typed middleTyped inputsTyped (by
        rw [← slots] at distinct
        simpa only [FlowContext.slots, List.map_append, List.map_map, Function.comp_def] using distinct)
      have states := congrArg initializedContext slots
      simp only [initializedContext, List.map_map, Function.comp_def] at states
      change List.map BindingInput.state _ = initializedContext locals at states
      rw [states] at entered
      obtain ⟨value, localAfter, bodyRun, _, localTyped, _, _⟩ := ih _ (.patternBody member) bodyTyped entered middleIssued
      obtain ⟨after, exited, _⟩ := AddressedEnvironment.exitScope.progress localTyped bindings.length
      exact ⟨value, after, .applyPatterns argumentsRun selected bodyRun exited⟩

end Grounded

