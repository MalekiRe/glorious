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

theorem Evaluates.unit {environment : List (BindingId × Value)} : Evaluates program environment .unit .unit environment :=
  .step .unit (.refl _)

theorem Evaluates.integer {environment : List (BindingId × Value)} {type : IntegerType} {magnitude : Nat}
      (fits : type.Contains program.target magnitude) :
      Evaluates program environment (.integer type magnitude) (.integer type magnitude) environment :=
  .step (.integer fits) (.refl _)

theorem Evaluates.character {environment : List (BindingId × Value)} {number : Nat} (valid : UnicodeScalar number) :
      Evaluates program environment (.character number) (.character number) environment :=
  .step (.character valid) (.refl _)

theorem Evaluates.group {environment after : List (BindingId × Value)} {body : Expr} {value : Value}
      (evaluated : Evaluates program environment body value after) :
      Evaluates program environment (.group body) value after :=
  .step .group evaluated

theorem Evaluates.read {environment : List (BindingId × Value)} {place : Place} {value : Value}
      (selected : readPlace program place environment = some value) :
      Evaluates program environment (.read place) value environment :=
  .step (.read selected) (.refl _)

theorem Evaluates.sequence {environment middle after : List (BindingId × Value)} {first rest : Expr}
      {discarded value : Value} (head : Evaluates program environment first discarded middle)
      (tail : Evaluates program middle rest value after) :
      Evaluates program environment (.sequence first rest) value after :=
  .step .sequence ((Run.extend head [.sequence rest]).trans (.step .sequenceResult tail))

theorem Evaluates.bind {environment middle after : List (BindingId × Value)} {mutable : Bool} {name : BindingId}
      {localType : Ty} {initial body : Expr} {resident value : Value}
      (initialized : Evaluates program environment initial resident middle)
      (continued : Evaluates program ((name, resident) :: middle) body value after) :
      Evaluates program environment (.bind mutable name localType initial body) value (after.drop 1) :=
  .step .bind ((Run.extend initialized [.bind name localType body]).trans
    (.step .bindResult ((Run.extend continued [.scope 1]).trans (.step .scope (.refl _)))))

theorem Evaluates.assign {environment middle updated after : List (BindingId × Value)} {place : Place}
      {expression rest : Expr} {resident value : Value}
      (evaluated : Evaluates program environment expression resident middle)
      (written : writePlace program place resident middle = some updated)
      (continued : Evaluates program updated rest value after) :
      Evaluates program environment (.assign place expression rest) value after :=
  .step .assign ((Run.extend evaluated [.assign place rest]).trans
    (.step (.assignResult written) continued))

theorem Evaluates.tuple {environment middle after : List (BindingId × Value)} {head : Expr} {tail : List Expr}
      {first : Value} {rest : List Value} (headEval : Evaluates program environment head first middle)
      (tailEval : EvaluatesMany program middle tail rest after) :
      Evaluates program environment (.tuple head tail) (.tuple first rest) after :=
  .step .tuple ((Run.extend headEval [.tupleHead tail]).trans
    (.step .tupleHead ((Run.extend tailEval [.tupleTail first]).trans (.step .tupleTail (.refl _)))))

theorem Evaluates.project {environment after : List (BindingId × Value)} {body : Expr} {key : FieldKey} {index : Nat}
      {aggregate value : Value}
      (source : Evaluates program environment body aggregate after)
      (selected : aggregate.projectField program key = some (index, value)) :
      Evaluates program environment (.project body key) value after :=
  .step .project ((Run.extend source [.project key]).trans (.step (.projectResult selected) (.refl _)))

theorem Evaluates.array {environment after : List (BindingId × Value)} {elements : List Expr} {values : List Value}
      (residents : EvaluatesMany program environment elements values after) :
      Evaluates program environment (.array elements) (.array values) after :=
  .step .array ((Run.extend residents [.array]).trans (.step .arrayResult (.refl _)))

theorem Evaluates.constant {environment : List (BindingId × Value)} {name : String} {declaration : ConstantDecl}
      {value : Value} (declared : program.constants name = some declaration)
      (initialized : Evaluates program [] declaration.body value []) :
      Evaluates program environment (.constant name) value environment :=
  .step (.constant declared) ((Run.extend initialized [.restore environment]).trans
    (.step .restore (.refl _)))

theorem Evaluates.construct {environment after : List (BindingId × Value)} {identity : Nat} {tag : Option Nat}
      {fields : List Expr} {values : List Value} (residents : EvaluatesMany program environment fields values after) :
      Evaluates program environment (.construct identity tag fields) (.nominal identity tag values) after :=
  .step .construct ((Run.extend residents [.construct identity tag]).trans (.step .constructResult (.refl _)))

theorem Evaluates.call {environment middle localAfter : List (BindingId × Value)} {identity : Nat} {arguments : List Expr}
      {declaration : FunctionDecl} {values : List Value} {value : Value} {bindings : List BindingInput}
      (declared : program.functions identity = some declaration)
      (prepared : prepareBindings declaration.parameters values = some bindings)
      (inputs : EvaluatesMany program environment arguments values middle)
      (body : Evaluates program (bindings.map fun input => (input.name, input.value)) declaration.body value localAfter) :
      Evaluates program environment (.call identity arguments) value middle :=
  .step (.call declared) ((Run.extend inputs [.call declaration]).trans
    (.step (.callInputs prepared) ((Run.extend body [.restore middle]).trans (.step .restore (.refl _)))))

theorem Evaluates.applyPatterns {environment middle after : List (BindingId × Value)} {inputs : List Ty} {arguments : List Expr}
      {arms : List (Pattern × Expr)} {values : List Value}
      {bindings : List (BindingId × Value)} {body : Expr} {value : Value}
      (argumentsEval : EvaluatesMany program environment arguments values middle)
      (selected : selectArm (argumentValue values) arms = some (bindings, body))
      (bodyEval : Evaluates program (bindings ++ middle) body value after) :
      Evaluates program environment (.applyPatterns inputs arguments arms) value (after.drop bindings.length) :=
  .step .applyPatterns ((Run.extend argumentsEval [.patterns arms]).trans
    (.step (.selectedPattern selected) ((Run.extend bodyEval [.scope bindings.length]).trans
      (.step .scope (.refl _)))))

theorem EvaluatesMany.nil {environment : List (BindingId × Value)} : EvaluatesMany program environment [] [] environment :=
  .step .nil (.refl _)

theorem EvaluatesMany.cons {environment middle after : List (BindingId × Value)} {head : Expr} {tail : List Expr}
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
