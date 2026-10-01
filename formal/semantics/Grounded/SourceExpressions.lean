import Grounded.NamedPatterns

/-! Recursive elaboration of named expressions in the initialized, duplicable
fragment. Named calls use the source declaration environment; core calls use IDs.
Named patterns and bodies share the same allocated lexical scope. -/
namespace Grounded

inductive NamedExpr where
  | unit
  | integer (type : IntegerType) (magnitude : Nat)
  | character (number : Nat)
  | group (body : NamedExpr)
  | read (name : String) (fields : List FieldKey)
  | sequence (first rest : NamedExpr)
  | bind (mutable : Bool) (name : String) (annotation : Option TypeExpr) (initial body : NamedExpr)
  | tuple (head : NamedExpr) (tail : List NamedExpr)
  | project (body : NamedExpr) (key : FieldKey)
  | array (elements : List NamedExpr)
  | constant (name : String)
  | construct (identity : Nat) (tag : Option Nat) (fields : List NamedExpr)
  | call (name : String) (arguments : List NamedExpr)
  | assign (name : String) (fields : List FieldKey) (value rest : NamedExpr)
  | applyPatterns (arguments : List NamedExpr) (arms : List (NamedPattern × NamedExpr))

mutual
/-- Source admission records the chosen elaboration. No runtime state, run,
future readiness or termination certificate is an elaboration premise. -/
inductive NamedExpr.Elaborates (program : Program) (names : String → Option Nat) (home : Module) :
    SourceScope → NamedExpr → Expr → Ty → Prop where
  | unit {scope} : NamedExpr.Elaborates program names home scope .unit .unit .unit
  | integer {scope type magnitude} (fits : type.Contains program.target magnitude) :
      NamedExpr.Elaborates program names home scope (.integer type magnitude) (.integer type magnitude) (.integer type)
  | character {scope number} (valid : UnicodeScalar number) :
      NamedExpr.Elaborates program names home scope (.character number) (.character number) .character
  | group {scope source core type} (body : NamedExpr.Elaborates program names home scope source core type) :
      NamedExpr.Elaborates program names home scope (.group source) (.group core) type
  | read {scope name fields binding type}
      (resolved : scope.resolve name = some binding)
      (path : PathType program home binding.slot.type fields type)
      (copyable : Duplicable program.data type) :
      NamedExpr.Elaborates program names home scope (.read name fields) (.read ⟨binding.identity, fields⟩) type
  | sequence {scope first rest head tail discarded type}
      (initial : NamedExpr.Elaborates program names home scope first head discarded)
      (discard : Duplicable program.data discarded)
      (continued : NamedExpr.Elaborates program names home scope rest tail type) :
      NamedExpr.Elaborates program names home scope (.sequence first rest) (.sequence head tail) type
  | bind {scope mutable name annotation initial body first rest localType type}
      (initialized : NamedExpr.Elaborates program names home scope initial first localType)
      (discard : Duplicable program.data localType)
      (annotated : Annotation program.aliases annotation localType)
      (continued : NamedExpr.Elaborates program names home (scope.enter name ⟨localType, mutable⟩) body rest type) :
      NamedExpr.Elaborates program names home scope (.bind mutable name annotation initial body)
        (.bind mutable ⟨scope.next⟩ annotation first rest) type
  | tuple {scope head tail first rest type types}
      (initial : NamedExpr.Elaborates program names home scope head first type)
      (continued : NamedExprsElaborate program names home scope tail rest types) :
      NamedExpr.Elaborates program names home scope (.tuple head tail) (.tuple first rest) (.tuple type types)
  | project {scope source core key parent type index}
      (body : NamedExpr.Elaborates program names home scope source core parent)
      (discard : Duplicable program.data parent)
      (selected : ProjectionType program home parent key index type) :
      NamedExpr.Elaborates program names home scope (.project source key) (.project core key) type
  | array {scope source core element length}
      (residents : NamedExprsElaborate program names home scope source core (List.replicate length element))
      (finite : FiniteLayout program.target program.data element)
      (size : length < 2 ^ program.target.pointerBits) :
      NamedExpr.Elaborates program names home scope (.array source) (.array core) (.array element length)
  | constant {scope name type} (checked : HasType program home [] (.constant name) type) :
      NamedExpr.Elaborates program names home scope (.constant name) (.constant name) type
  | construct {scope identity tag declaration schema source core}
      (declared : program.data identity = some declaration)
      (chosen : declaration.constructor tag = some schema)
      (finite : FiniteLayout program.target program.data (.nominal identity))
      (copyable : Duplicable program.data (.nominal identity))
      (visible : declaration.visibility.Allows declaration.home home)
      (access : ∀ field ∈ schema.residents, field.visibility.Allows declaration.home home)
      (residents : NamedExprsElaborate program names home scope source core (schema.residents.map Field.type)) :
      NamedExpr.Elaborates program names home scope (.construct identity tag source) (.construct identity tag core) (.nominal identity)
  | call {scope name identity declaration source core}
      (resolved : names name = some identity)
      (declared : program.functions identity = some declaration)
      (visible : declaration.visibility.Allows declaration.home home)
      (inputs : NamedExprsElaborate program names home scope source core
        (declaration.parameters.map fun parameter => parameter.2.type)) :
      NamedExpr.Elaborates program names home scope (.call name source) (.call identity core) declaration.result
  | assign {scope name fields binding type result value rest coreValue coreRest}
      (resolved : scope.resolve name = some binding)
      (path : PathType program home binding.slot.type fields type)
      (writable : binding.slot.mutable = true) (discard : Duplicable program.data type)
      (resident : NamedExpr.Elaborates program names home scope value coreValue type)
      (continued : NamedExpr.Elaborates program names home scope rest coreRest result) :
      NamedExpr.Elaborates program names home scope (.assign name fields value rest)
        (.assign ⟨binding.identity, fields⟩ coreValue coreRest) result
  | applyPatterns {scope arguments coreArguments inputs arms coreArms result}
      (inputsTyped : NamedExprsElaborate program names home scope arguments coreArguments inputs)
      (nonempty : coreArms ≠ [])
      (covered : Covers program [argumentType inputs] (coreArms.map fun arm => [arm.1]))
      (bodies : NamedArmsElaborate program names home scope (argumentType inputs) result [] arms coreArms) :
      NamedExpr.Elaborates program names home scope (.applyPatterns arguments arms)
        (.applyPatterns inputs coreArguments coreArms) result

inductive NamedExprsElaborate (program : Program) (names : String → Option Nat) (home : Module) :
    SourceScope → List NamedExpr → List Expr → List Ty → Prop where
  | nil {scope} : NamedExprsElaborate program names home scope [] [] []
  | cons {scope head tail first rest type types}
      (initial : NamedExpr.Elaborates program names home scope head first type)
      (continued : NamedExprsElaborate program names home scope tail rest types) :
      NamedExprsElaborate program names home scope (head :: tail) (first :: rest) (type :: types)
inductive NamedArmsElaborate (program : Program) (names : String → Option Nat) (home : Module) :
    SourceScope → Ty → Ty → List Pattern → List (NamedPattern × NamedExpr) → List (Pattern × Expr) → Prop where
  | empty {scope subject result previous} : NamedArmsElaborate program names home scope subject result previous [] []
  | clause {scope after subject result previous source pattern bindings body coreBody tail coreTail}
      (allocated : NamedPattern.Elaborates program home scope source subject pattern bindings after)
      (namesDistinct : source.binders.Nodup)
      (useful : Useful program subject previous pattern)
      (bodyTyped : NamedExpr.Elaborates program names home after body coreBody result)
      (tailTyped : NamedArmsElaborate program names home scope subject result (previous ++ [pattern]) tail coreTail) :
      NamedArmsElaborate program names home scope subject result previous ((source, body) :: tail) ((pattern, coreBody) :: coreTail)

end

/-- Recursive source checking feeds the existing core admission, including the
same local resolver, field judgments and declaration signatures. -/
theorem NamedExpr.Elaborates.checked {program : Program} {home : Module}
    {names : String → Option Nat}
    {scope : SourceScope} {source : NamedExpr} {core : Expr} {type : Ty}
    (elaborated : NamedExpr.Elaborates program names home scope source core type) :
    HasType program home scope.context core type := by
  induction elaborated using NamedExpr.Elaborates.rec
    (motive_2 := fun scope _ core types _ => HasTypes program home scope.context core types)
    (motive_3 := fun scope subject result previous _ arms _ =>
      ArmsType program home scope.context subject result previous arms) with
  | unit => exact .unit
  | integer fits => exact .integer fits
  | character valid => exact .character valid
  | group _ ih => exact .group ih
  | read resolved path copyable => exact SourceScope.read_checked resolved path copyable
  | sequence _ discard _ head tail => exact .sequence head discard tail
  | bind _ discard annotated _ first rest => exact SourceScope.bind_checked _ _ _ first discard annotated rest
  | tuple _ _ head tail => exact .tuple head tail
  | project _ discard selected ih => exact .project ih discard selected
  | array _ finite size ih => exact .array ih finite size
  | constant checked => cases checked with
    | constant declared visible resolved structural initialized =>
      exact .constant declared visible resolved structural initialized
  | construct declared chosen finite copyable visible access _ ih =>
    exact .construct declared chosen finite copyable visible access ih
  | call _ declared visible _ ih => exact .call declared visible ih
  | assign resolved path writable discard _ _ first rest =>
    exact SourceScope.assign_checked resolved path writable discard first rest
  | applyPatterns _ nonempty covered _ inputs bodies => exact .applyPatterns inputs nonempty covered bodies
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head tail
  | empty => exact .empty
  | clause allocated _ useful _ _ body tail =>
    rw [allocated.checked.2] at body
    exact .clause allocated.checked.1 allocated.fresh useful body tail

theorem NamedExprsElaborate.checked {program : Program} {home : Module}
    {names : String → Option Nat}
    {scope : SourceScope} {source : List NamedExpr} {core : List Expr} {types : List Ty}
    (elaborated : NamedExprsElaborate program names home scope source core types) :
    HasTypes program home scope.context core types := by
  induction source generalizing core types with
  | nil => cases elaborated; exact .nil
  | cons head tail ih =>
    cases elaborated with
    | cons first rest => exact .cons first.checked (ih rest)

/-- Every prefix of the selected elaboration is safe, including recursive calls.
The only dynamic input evidence describes the actual incoming environment. -/
theorem NamedExpr.Elaborates.soundness {program : Program} {home : Module}
    {names : String → Option Nat}
    {scope : SourceScope} {source : NamedExpr} {core : Expr} {type : Ty}
    (elaborated : NamedExpr.Elaborates program names home scope source core type)
    (checkedProgram : program.Checked) {environment : Environment}
    (store : EnvironmentTyped program environment scope.context) {state : Configuration}
    (run : Run program ⟨environment, .expression core, []⟩ state) :
    ConfigurationTyped program scope.context (.one type) state ∧
      (Terminal state ∨ ∃ next, Step program state next) ∧
      EnvironmentFrame scope.context environment state.outerEnvironment ∧
      (state.environment.map Prod.fst).Nodup :=
  elaborated.checked.soundness checkedProgram store run

/-- Completed executions preserve the declared result and caller environment;
termination is not assumed by source admission. -/
theorem NamedExpr.Elaborates.evaluation_soundness {program : Program} {home : Module}
    {names : String → Option Nat}
    {scope : SourceScope} {source : NamedExpr} {core : Expr} {type : Ty}
    (elaborated : NamedExpr.Elaborates program names home scope source core type)
    (checkedProgram : program.Checked) {environment after : Environment} {value : Value}
    (store : EnvironmentTyped program environment scope.context)
    (evaluated : Evaluates program environment core value after) :
    ValueHasType program value type ∧ EnvironmentTyped program after scope.context ∧
      EnvironmentFrame scope.context environment after :=
  elaborated.checked.evaluation_soundness checkedProgram store evaluated

/-- Finite-call termination remains an optional theorem about the same selected
core, not a restriction on recursive source safety. -/
theorem NamedExpr.Elaborates.correctness {program : Program} {home : Module}
    {names : String → Option Nat}
    {scope : SourceScope} {source : NamedExpr} {core : Expr} {type : Ty}
    (elaborated : NamedExpr.Elaborates program names home scope source core type)
    (checkedProgram : program.Checked) (finite : FiniteCalls program core)
    {environment : Environment} (store : EnvironmentTyped program environment scope.context) :
    ∃ value after, Evaluates program environment core value after ∧ ValueHasType program value type ∧
      EnvironmentTyped program after scope.context ∧ EnvironmentFrame scope.context environment after ∧
      ∀ other otherAfter, Evaluates program environment core other otherAfter →
        other = value ∧ otherAfter = after :=
  Grounded.correctness checkedProgram elaborated.checked finite store


end Grounded
