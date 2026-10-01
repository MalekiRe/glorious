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

theorem Evaluates.integer {environment : Environment} {type : IntegerType} {magnitude : Nat}
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
  .step .sequence ((Run.extend head [.sequence rest]).trans (.step .sequenceResult tail))

theorem Evaluates.bind {environment middle localAfter after : Environment} {mutable : Bool} {name : BindingId}
      {localType : Ty} {initial body : Expr} {resident value : Value}
      (initialized : Evaluates program environment initial resident middle)
      (continued : Evaluates program (middle.extend [⟨name, ⟨localType, mutable⟩, resident⟩]) body value localAfter)
      (exited : localAfter.exitScope 1 = some after) :
      Evaluates program environment (.bind mutable name localType initial body) value after :=
  .step .bind ((Run.extend initialized [.bind name ⟨localType, mutable⟩ body]).trans
    (.step .bindResult ((Run.extend continued [.scope 1]).trans (.step (.scope exited) (.refl _)))))

theorem Evaluates.assign {environment middle updated after : Environment} {place : Place}
      {expression rest : Expr} {resident value : Value}
      (evaluated : Evaluates program environment expression resident middle)
      (written : middle.write program place resident = some updated)
      (continued : Evaluates program updated rest value after) :
      Evaluates program environment (.assign place expression rest) value after :=
  .step .assign ((Run.extend evaluated [.assign place rest]).trans
    (.step (.assignResult written) continued))

theorem Evaluates.tuple {environment middle after : Environment} {head : Expr} {tail : List Expr}
      {first : Value} {rest : List Value} (headEval : Evaluates program environment head first middle)
      (tailEval : EvaluatesMany program middle tail rest after) :
      Evaluates program environment (.tuple head tail) (.tuple first rest) after :=
  .step .tuple ((Run.extend headEval [.tupleHead tail]).trans
    (.step .tupleHead ((Run.extend tailEval [.tupleTail first]).trans (.step .tupleTail (.refl _)))))

theorem Evaluates.project {environment after : Environment} {body : Expr} {key : FieldKey} {index : Nat}
      {aggregate value : Value}
      (source : Evaluates program environment body aggregate after)
      (selected : aggregate.projectField program key = some (index, value)) :
      Evaluates program environment (.project body key) value after :=
  .step .project ((Run.extend source [.project key]).trans (.step (.projectResult selected) (.refl _)))

theorem Evaluates.array {environment after : Environment} {elements : List Expr} {values : List Value}
      (residents : EvaluatesMany program environment elements values after) :
      Evaluates program environment (.array elements) (.array values) after :=
  .step .array ((Run.extend residents [.array]).trans (.step .arrayResult (.refl _)))

theorem Evaluates.constant {environment localAfter after : Environment} {name : String} {declaration : ConstantDecl}
      {value : Value} (declared : program.constants name = some declaration)
      (initialized : Evaluates program (enterBindings environment.heap environment.supply []) declaration.body value localAfter)
      (restored : localAfter.restore environment.scope = some after) :
      Evaluates program environment (.constant name) value after :=
  .step (.constant declared) ((Run.extend initialized [.restore environment.scope]).trans
    (.step (.restore restored) (.refl _)))

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
    (.step (.callInputs prepared) ((Run.extend body [.restore middle.scope]).trans (.step (.restore restored) (.refl _)))))

theorem Evaluates.applyPatterns {environment middle localAfter after : Environment} {inputs : List Ty} {arguments : List Expr}
      {arms : List (Pattern × Expr)} {values : List Value}
      {bindings : List BindingInput} {body : Expr} {value : Value}
      (argumentsEval : EvaluatesMany program environment arguments values middle)
      (selected : selectArm (argumentValue values) arms = some (bindings, body))
      (bodyEval : Evaluates program (middle.extend bindings) body value localAfter)
      (exited : localAfter.exitScope bindings.length = some after) :
      Evaluates program environment (.applyPatterns inputs arguments arms) value after :=
  .step .applyPatterns ((Run.extend argumentsEval [.patterns arms]).trans
    (.step (.selectedPattern selected) ((Run.extend bodyEval [.scope bindings.length]).trans
      (.step (.scope exited) (.refl _)))))

theorem EvaluatesMany.nil {environment : Environment} : EvaluatesMany program environment [] [] environment :=
  .step .nil (.refl _)

theorem EvaluatesMany.cons {environment middle after : Environment} {head : Expr} {tail : List Expr}
      {first : Value} {rest : List Value} (headEval : Evaluates program environment head first middle)
      (tailEval : EvaluatesMany program middle tail rest after) :
      EvaluatesMany program environment (head :: tail) (first :: rest) after :=
  .step .cons ((Run.extend headEval [.argumentHead tail]).trans
    (.step .argumentHead ((Run.extend tailEval [.argumentTail first]).trans (.step .argumentTail (.refl _)))))

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

end Grounded
