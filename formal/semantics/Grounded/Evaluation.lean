import Grounded.Execution

/-! Terminating evaluation is finite execution of the machine, not a second
set of operational rules. Composition runs subcomputations under actual frames. -/
namespace Grounded

def Evaluates (program : Program) (environment : Environment) (expression : Expr)
    (value : Value) (after : Environment) : Prop :=
  Run program ⟨environment, .expression expression, []⟩ ⟨after, .result value, []⟩

def EvaluatesMany (program : Program) (environment : Environment) (expressions : List Expr)
    (values : List Value) (after : Environment) : Prop :=
  Run program ⟨environment, .arguments expressions, []⟩ ⟨after, .results values, []⟩

variable {program : Program}

theorem Evaluates.unit {environment : Environment} : Evaluates program environment .unit .unit environment :=
  .step .unit (.refl _)

theorem Evaluates.integer {environment : Environment} {type : IntegerType} {magnitude : Int}
      (fits : type.Contains program.target magnitude) :
      Evaluates program environment (.integer type magnitude) (.integer type magnitude) environment :=
  .step (.integer fits) (.refl _)

theorem Evaluates.character {environment : Environment} {number : Nat} (valid : UnicodeScalar number) :
      Evaluates program environment (.character number) (.character number) environment :=
  .step (.character valid) (.refl _)

theorem Evaluates.group {environment after : Environment} {body : Expr} {value : Value}
      (evaluated : Evaluates program environment body value after) :
      Evaluates program environment (.group body) value after :=
  .step .group evaluated

theorem Evaluates.read {environment : Environment} {place : Place} {value : Value}
      (selected : environment.read program place = some value) :
      Evaluates program environment (.read place) value environment :=
  .step (.read selected) (.refl _)

theorem Evaluates.move {environment after : Environment} {place : Place} {value : Value}
    (taken : environment.take program place = some (value, after)) :
    Evaluates program environment (.move place) value after :=
  .step (.move taken) (.refl _)

theorem Evaluates.sequence {environment middle after : Environment} {first rest : Expr}
      {discarded value : Value} (head : Evaluates program environment first discarded middle)
      (tail : Evaluates program middle rest value after) :
      Evaluates program environment (.sequence first rest) value after :=
  .step .sequence ((Run.extend head [.sequence rest]).trans
    (.step .sequenceResult ((Run.cleanup_value middle (.expression rest) [] discarded []).trans (.step .cleanupDone tail))))

theorem Evaluates.bind {environment middle localAfter after : Environment} {mutable : Bool} {name : BindingId}
      {localType : Ty} {initial body : Expr} {resident value : Value}
      (initialized : Evaluates program environment initial resident middle)
      (continued : Evaluates program (middle.extend [⟨name, ⟨localType, mutable⟩, resident⟩]) body value localAfter)
      (exited : localAfter.exitScope 1 = some after) :
      Evaluates program environment (.bind mutable name localType initial body) value after :=
  .step .bind ((Run.extend initialized [.bind name ⟨localType, mutable⟩ body]).trans
    (.step .bindResult ((Run.extend continued [.scope 1]).trans (Run.scope exited))))

theorem Evaluates.assign {home : Module} {environment middle updated after : Environment} {place : Place}
      {expression rest : Expr} {resident value : Value} {old : PartialValue}
      (evaluated : Evaluates program environment expression resident middle)
      (written : middle.write program place resident = some updated)
      (selected : middle.bindings.selectPartial program middle.heap place = some old)
      (continued : Evaluates program updated rest value after) :
      Evaluates program environment (.assign home place expression rest) value after :=
  .step .assign ((Run.extend evaluated [.assign home place rest]).trans
    (.step (.assignResult selected)
      ((Run.cleanup middle (.install home place resident rest) [] old.disposalTasks).trans
        (.step (.install written) continued))))

theorem Evaluates.tuple {environment middle after : Environment} {head : Expr} {tail : List Expr}
      {first : Value} {rest : List Value} (headEval : Evaluates program environment head first middle)
      (tailEval : EvaluatesMany program middle tail rest after) :
      Evaluates program environment (.tuple head tail) (.tuple first rest) after :=
  .step .tuple ((Run.extend headEval [.tupleHead tail]).trans
    (.step .tupleHead ((Run.extend tailEval [.tupleTail first]).trans (.step .tupleTail (.refl _)))))

theorem Evaluates.project {home : Module} {environment after : Environment} {body : Expr} {key : FieldKey} {index : Nat}
      {aggregate value : Value} {remainder : PartialValue}
      (source : Evaluates program environment body aggregate after)
      (selected : aggregate.takeField program key = some (index, value, remainder)) :
      Evaluates program environment (.project home body key) value after :=
  .step .project ((Run.extend source [.project home key]).trans
    (.step (.projectResult selected) (Run.cleanup after (.result value) [] remainder.disposalTasks)))

theorem Evaluates.array {environment after : Environment} {elements : List Expr} {values : List Value}
      (residents : EvaluatesMany program environment elements values after) :
      Evaluates program environment (.array elements) (.array values) after :=
  .step .array ((Run.extend residents [.array]).trans (.step .arrayResult (.refl _)))

theorem Evaluates.constant {environment localAfter after : Environment} {name : Nat} {declaration : ConstantDecl}
      {value : Value} (declared : program.constants name = some declaration)
      (initialized : Evaluates program (enterBindings environment.heap environment.supply []) declaration.body value localAfter)
      (restored : localAfter.restore environment.scope = some after) :
      Evaluates program environment (.constant name) value after :=
  .step (.constant declared) ((Run.extend initialized [.restore environment.scope]).trans
    (Run.restore restored))

theorem Evaluates.construct {environment after : Environment} {identity : Nat} {tag : Option Nat}
      {fields : List Expr} {values : List Value} (residents : EvaluatesMany program environment fields values after) :
      Evaluates program environment (.construct identity tag fields) (.nominal identity tag values) after :=
  .step .construct ((Run.extend residents [.construct identity tag]).trans (.step .constructResult (.refl _)))

theorem Evaluates.call {environment middle localAfter after : Environment} {identity : Nat} {arguments : List Expr}
      {declaration : FunctionDecl} {values : List Value} {value : Value} {bindings : List BindingInput}
      (declared : program.functions identity = some declaration)
      (prepared : prepareBindings declaration.parameters values = some bindings)
      (inputs : EvaluatesMany program environment arguments values middle)
      (body : Evaluates program (enterBindings middle.heap middle.supply bindings) declaration.body value localAfter)
      (restored : localAfter.restore middle.scope = some after) :
      Evaluates program environment (.call identity arguments) value after :=
  .step (.call declared) ((Run.extend inputs [.call declaration]).trans
    (.step (.callInputs prepared) ((Run.extend body [.restore middle.scope]).trans (Run.restore restored))))

theorem Evaluates.applyPatterns {environment middle localAfter after : Environment} {inputs : List Ty} {arguments : List Expr}
      {home : Module} {arms : List (Pattern × Expr)} {values : List Value}
      {bindings : PatternMatch} {body : Expr} {value : Value}
      (argumentsEval : EvaluatesMany program environment arguments values middle)
      (selected : selectArm (argumentValue values) arms = some (bindings, body))
      (bodyEval : Evaluates program (middle.extend bindings.bindings) body value localAfter)
      (exited : localAfter.exitScope bindings.bindings.length = some after) :
      Evaluates program environment (.applyPatterns home inputs arguments arms) value after :=
  .step .applyPatterns ((Run.extend argumentsEval [.patterns home arms]).trans
    (.step (.selectedPattern selected) ((Run.cleanup _ _ _ _).trans ((Run.extend bodyEval [.scope bindings.bindings.length]).trans
      (Run.scope exited)))))

theorem EvaluatesMany.nil {environment : Environment} : EvaluatesMany program environment [] [] environment :=
  .step .nil (.refl _)

theorem EvaluatesMany.cons {environment middle after : Environment} {head : Expr} {tail : List Expr}
      {first : Value} {rest : List Value} (headEval : Evaluates program environment head first middle)
      (tailEval : EvaluatesMany program middle tail rest after) :
      EvaluatesMany program environment (head :: tail) (first :: rest) after :=
  .step .cons ((Run.extend headEval [.argumentHead tail]).trans
    (.step .argumentHead ((Run.extend tailEval [.argumentTail first]).trans (.step .argumentTail (.refl _)))))


/-- A completed direct invocation necessarily ran the ordered argument list,
then the selected body in fresh parameter storage, then caller restoration.
This extracts executions; it never asserts that a recursive body terminates. -/
theorem Evaluates.call_iff {environment after : Environment} {identity : Nat}
    {arguments : List Expr} {value : Value} :
    Evaluates program environment (.call identity arguments) value after ↔
      ∃ declaration values middle bindings localAfter,
        program.functions identity = some declaration ∧
        EvaluatesMany program environment arguments values middle ∧
        prepareBindings declaration.parameters values = some bindings ∧
        Evaluates program (enterBindings middle.heap middle.supply bindings) declaration.body value localAfter ∧
        localAfter.restore middle.scope = some after := by
  constructor
  · intro evaluated
    cases evaluated with
    | step head rest =>
      cases head with
      | call declared =>
        obtain ⟨done, terminal, inputs, continued⟩ := rest.unextend
          ⟨environment, .arguments arguments, []⟩ [_] rfl (by simp)
        cases terminal with
        | result middle argument =>
          cases continued with
          | step head rest => cases head
        | results middle values =>
          cases continued with
          | step head rest =>
            cases head with
            | callInputs prepared =>
              obtain ⟨done, terminal, body, returned⟩ := rest.unextend
                ⟨_, .expression _, []⟩ [_] rfl (by simp)
              cases terminal with
              | results localAfter results =>
                cases returned with
                | step head rest => cases head
              | result localAfter result =>
                obtain ⟨same, restored⟩ := Run.restore_result returned
                subst result
                exact ⟨_, _, _, _, _, declared, inputs, prepared, body, restored⟩
  · rintro ⟨declaration, values, middle, bindings, localAfter, declared, inputs, prepared, body, restored⟩
    exact .call declared prepared inputs body restored

/-- The first argument completes before the tail starts, in its actual output
heap. The result pack has exactly that first value followed by the tail pack. -/
theorem EvaluatesMany.cons_iff {environment after : Environment} {head : Expr}
    {tail : List Expr} {values : List Value} :
    EvaluatesMany program environment (head :: tail) values after ↔
      ∃ first rest middle, values = first :: rest ∧
        Evaluates program environment head first middle ∧
        EvaluatesMany program middle tail rest after := by
  constructor
  · intro evaluated
    cases evaluated with
    | step first remaining =>
      cases first with
      | cons =>
        obtain ⟨done, terminal, headRun, continued⟩ := remaining.unextend
          ⟨environment, .expression head, []⟩ [_] rfl (by simp)
        cases terminal with
        | results middle values =>
          cases continued with
          | step first remaining => cases first
        | result middle value =>
          cases continued with
          | step first remaining =>
            cases first with
            | argumentHead =>
              obtain ⟨done, terminal, tailRun, continued⟩ := remaining.unextend
                ⟨middle, .arguments tail, []⟩ [_] rfl (by simp)
              cases terminal with
              | result last value =>
                cases continued with
                | step first remaining => cases first
              | results last values =>
                cases continued with
                | step first remaining =>
                  cases first with
                  | argumentTail =>
                    cases remaining with
                    | refl => exact ⟨_, _, _, rfl, headRun, tailRun⟩
                    | step first remaining => cases first
  · rintro ⟨first, rest, middle, rfl, headRun, tailRun⟩
    exact .cons headRun tailRun

/-- Determinism is an operational property, independent of admission. -/
theorem Evaluates.unique {environment firstAfter secondAfter : Environment} {expression : Expr}
    {first second : Value} (left : Evaluates program environment expression first firstAfter)
    (right : Evaluates program environment expression second secondAfter) :
    second = first ∧ secondAfter = firstAfter := by
  have same := Run.unique left right (fun _ step => by cases step) (fun _ step => by cases step)
  cases same
  exact ⟨rfl, rfl⟩

theorem EvaluatesMany.unique {environment firstAfter secondAfter : Environment} {expressions : List Expr}
    {first second : List Value} (left : EvaluatesMany program environment expressions first firstAfter)
    (right : EvaluatesMany program environment expressions second secondAfter) :
    second = first ∧ secondAfter = firstAfter := by
  have same := Run.unique left right (fun _ step => by cases step) (fun _ step => by cases step)
  cases same
  exact ⟨rfl, rfl⟩


/-- Every argument-list cut is an actual sequential execution cut. In
particular, a later argument cannot run before the complete preceding prefix. -/
theorem EvaluatesMany.append_iff {environment after : Environment}
    {front back : List Expr} {values : List Value} :
    EvaluatesMany program environment (front ++ back) values after ↔
      ∃ first rest middle, values = first ++ rest ∧
        EvaluatesMany program environment front first middle ∧
        EvaluatesMany program middle back rest after := by
  induction front generalizing environment values with
  | nil =>
    constructor
    · intro run
      exact ⟨[], values, environment, rfl, .nil, run⟩
    · rintro ⟨first, rest, middle, rfl, initial, final⟩
      have same := EvaluatesMany.unique EvaluatesMany.nil initial
      rcases same with ⟨rfl, rfl⟩
      exact final
  | cons head tail ih =>
    constructor
    · intro run
      obtain ⟨value, rest, middle, rfl, headRun, tailRun⟩ := EvaluatesMany.cons_iff.mp run
      obtain ⟨first, last, next, rfl, frontRun, backRun⟩ := ih.mp tailRun
      exact ⟨value :: first, last, next, rfl, .cons headRun frontRun, backRun⟩
    · rintro ⟨first, rest, middle, rfl, initial, final⟩
      obtain ⟨value, front, next, rfl, headRun, tailRun⟩ := EvaluatesMany.cons_iff.mp initial
      exact .cons headRun (ih.mpr ⟨front, rest, middle, rfl, tailRun, final⟩)


/-- Noncompletion of the body selected after the actual arguments implies
noncompletion of its invocation. This raw theorem does not conflate absence
of a completed run with progress; admitted-prefix safety supplies progress. -/
theorem Evaluates.call_body_noncompletion {environment middle : Environment}
    {identity : Nat} {arguments : List Expr} {declaration : FunctionDecl}
    {values : List Value} {bindings : List BindingInput}
    (declared : program.functions identity = some declaration)
    (inputs : EvaluatesMany program environment arguments values middle)
    (prepared : prepareBindings declaration.parameters values = some bindings)
    (noncompletion : ∀ value after,
      ¬ Evaluates program (enterBindings middle.heap middle.supply bindings) declaration.body value after) :
    ∀ value after, ¬ Evaluates program environment (.call identity arguments) value after := by
  intro value after completed
  obtain ⟨actual, actualValues, actualMiddle, actualBindings, localAfter,
    selected, inputRun, preparation, body, _⟩ := Evaluates.call_iff.mp completed
  cases Option.some.inj (declared.symm.trans selected)
  obtain ⟨rfl, rfl⟩ := inputs.unique inputRun
  cases Option.some.inj (prepared.symm.trans preparation)
  exact noncompletion _ _ body

/-- A completed pattern invocation executes its ordered arguments, the actual
first selected arm, and that arm's scope retirement, in precisely that order. -/
theorem Evaluates.applyPatterns_iff {environment after : Environment} {inputs : List Ty}
    {home : Module} {arguments : List Expr} {arms : List (Pattern × Expr)} {value : Value} :
    Evaluates program environment (.applyPatterns home inputs arguments arms) value after ↔
      ∃ values middle bindings body localAfter,
        EvaluatesMany program environment arguments values middle ∧
        selectArm (argumentValue values) arms = some (bindings, body) ∧
        Evaluates program (middle.extend bindings.bindings) body value localAfter ∧
        localAfter.exitScope bindings.bindings.length = some after := by
  constructor
  · intro evaluated
    cases evaluated with
    | step head rest =>
      cases head with
      | applyPatterns =>
        obtain ⟨done, terminal, argumentsRun, continued⟩ := rest.unextend
          ⟨environment, .arguments arguments, []⟩ [_] rfl (by simp)
        cases terminal with
        | result middle argument =>
          cases continued with
          | step head rest => cases head
        | results middle values =>
          cases continued with
          | step head rest =>
            cases head with
            | selectedPattern selected =>
              rcases Run.cleanup_decompose rest _ _ _ _ rfl with ⟨remaining, impossible⟩ | rest
              · cases impossible
              obtain ⟨done, terminal, bodyRun, exited⟩ := rest.unextend
                ⟨_, .expression _, []⟩ [_] rfl (by simp)
              cases terminal with
              | results localAfter results =>
                cases exited with
                | step head rest => cases head
              | result localAfter result =>
                obtain ⟨same, retired⟩ := Run.scope_result exited
                subst result
                exact ⟨_, _, _, _, _, argumentsRun, selected, bodyRun, retired⟩
  · rintro ⟨values, middle, bindings, body, localAfter, argumentsRun, selected, bodyRun, retired⟩
    exact .applyPatterns argumentsRun selected bodyRun retired


end Grounded
