import Grounded.SourceExpressions
import Grounded.BindingStorage

/-! Named direct-function declarations supply Program.Checked. Signatures are
available to recursive calls independently of body elaboration. Names here are
qualified declaration keys; import/path expansion remains a decoding boundary. -/
namespace Grounded

structure NamedParameter where
  name : String
  type : TypeExpr
  mutable : Bool := false

structure NamedFunction where
  name : String
  home : Module
  visibility : Visibility := .private
  parameters : List NamedParameter
  result : Option TypeExpr := none
  body : NamedExpr

/-- Parameter order is preserved in the emitted invocation interface. Static
allocation runs tail-first, exactly as pattern allocation does. -/
inductive NamedParametersElaborate (program : Program) : List NamedParameter → SourceScope → Prop where
  | nil : NamedParametersElaborate program [] .empty
  | cons {parameter rest scope type}
      (tail : NamedParametersElaborate program rest scope)
      (resolved : ResolvesType program.aliases parameter.type type)
      (disposable : Duplicable program.data type) :
      NamedParametersElaborate program (parameter :: rest) (scope.enter parameter.name ⟨type, parameter.mutable⟩)

theorem NamedParametersElaborate.disposable {program : Program} {parameters : List NamedParameter}
    {scope : SourceScope} (elaborated : NamedParametersElaborate program parameters scope) :
    ∀ parameter ∈ scope.context, Duplicable program.data parameter.2.type := by
  induction elaborated with
  | nil => simp [SourceScope.empty, SourceScope.context]
  | cons tail resolved disposable ih =>
    intro parameter member
    cases member with
    | head => exact disposable
    | tail _ member => exact ih parameter member

/-- Source parameter names, omitted-unit result semantics and the actual named
body determine the same declaration consumed by runtime invocation. -/
inductive NamedFunction.Elaborates (program : Program) (names : String → Option Nat) :
    NamedFunction → FunctionDecl → Prop where
  | intro {source scope result body}
      (parameters : NamedParametersElaborate program source.parameters scope)
      (distinct : (source.parameters.map NamedParameter.name).Nodup)
      (resultType : ResolvesType program.aliases (source.result.getD (.concrete .unit)) result)
      (elaborated : NamedExpr.Elaborates program names source.home scope source.body body result) :
      NamedFunction.Elaborates program names source
        ⟨source.home, source.visibility, scope.context, result, body⟩

theorem NamedFunction.Elaborates.checked {program : Program} {names : String → Option Nat}
    {source : NamedFunction} {core : FunctionDecl}
    (elaborated : NamedFunction.Elaborates program names source core) : FunctionChecked program core := by
  cases elaborated with
  | intro parameters distinct resultType body =>
    exact ⟨SourceScope.context_distinct _, parameters.disposable, body.checked⟩

/-- Declaration identities are the source-list positions. Duplicate qualified
names are rejected by program admission rather than resolved by first-wins. -/
def functionNames (source : List NamedFunction) (name : String) : Option Nat :=
  source.findIdx? (fun declaration => declaration.name == name)

inductive NamedFunctionsElaborate (program : Program) (names : String → Option Nat) :
    List NamedFunction → List FunctionDecl → Prop where
  | nil : NamedFunctionsElaborate program names [] []
  | cons {source sources core cores}
      (head : NamedFunction.Elaborates program names source core)
      (tail : NamedFunctionsElaborate program names sources cores) :
      NamedFunctionsElaborate program names (source :: sources) (core :: cores)

theorem NamedFunctionsElaborate.checked {program : Program} {names : String → Option Nat}
    {source : List NamedFunction} {core : List FunctionDecl}
    (elaborated : NamedFunctionsElaborate program names source core) :
    ∀ declaration ∈ core, FunctionChecked program declaration := by
  induction elaborated with
  | nil => simp
  | cons head tail ih =>
    intro declaration member
    cases member with
    | head => exact head.checked
    | tail _ member => exact ih declaration member

/-- Every executable function is an emitted source declaration: no hidden
unchecked functions, assumed successful runs or progress certificates. -/
def NamedFunctionsAdmitted (source : List NamedFunction) (program : Program) : Prop :=
  (source.map NamedFunction.name).Nodup ∧ ∃ core,
    NamedFunctionsElaborate program (functionNames source) source core ∧
    program.functions = fun identity => core[identity]?

theorem NamedFunctionsAdmitted.checked {source : List NamedFunction} {program : Program}
    (admitted : NamedFunctionsAdmitted source program) : program.Checked := by
  obtain ⟨_, core, elaborated, functions⟩ := admitted
  intro identity declaration selected
  rw [functions] at selected
  exact elaborated.checked declaration (List.mem_of_getElem? selected)

/-- Public source safety obtains declaration-body correctness from named source
admission, rather than accepting Program.Checked from the caller. -/
theorem NamedFunctionsAdmitted.soundness {source : List NamedFunction} {program : Program}
    (admitted : NamedFunctionsAdmitted source program) {home : Module} {scope : SourceScope}
    {expression : NamedExpr} {core : Expr} {type : Ty}
    (elaborated : NamedExpr.Elaborates program (functionNames source) home scope expression core type)
    {environment : Environment} (store : EnvironmentTyped program environment scope.context)
    {state : Configuration} (run : Run program ⟨environment, .expression core, []⟩ state) :
    ConfigurationTyped program scope.context (.one type) state ∧
      (Terminal state ∨ ∃ next, Step program state next) ∧
      EnvironmentFrame scope.context environment state.outerEnvironment ∧
      (state.environment.map Prod.fst).Nodup :=
  elaborated.soundness admitted.checked store run

/-- A resolved source name selects the same list position used for the emitted
runtime declaration, including forward references and mutually recursive calls. -/
theorem functionNames.selected {source : List NamedFunction} {name : String} {identity : Nat}
    (resolved : functionNames source name = some identity) :
    ∃ declaration, source[identity]? = some declaration ∧ declaration.name = name := by
  obtain ⟨bound, equal, _⟩ := List.findIdx?_eq_some_iff_getElem.mp resolved
  exact ⟨source[identity], List.getElem?_eq_some_iff.mpr ⟨bound, rfl⟩, by simpa using equal⟩

theorem functionNames.missing (source : List NamedFunction) (name : String) :
    functionNames source name = none ↔ ∀ declaration ∈ source, declaration.name ≠ name := by
  simp [functionNames, List.findIdx?_eq_none_iff]

theorem NamedFunctionsElaborate.selected {program : Program} {names : String → Option Nat}
    {sources : List NamedFunction} {cores : List FunctionDecl}
    (elaborated : NamedFunctionsElaborate program names sources cores)
    {identity : Nat} {source : NamedFunction} (selected : sources[identity]? = some source) :
    ∃ core, cores[identity]? = some core ∧ NamedFunction.Elaborates program names source core := by
  induction elaborated generalizing identity with
  | nil => simp at selected
  | cons head tail ih =>
    cases identity with
    | zero => cases selected; exact ⟨_, rfl, head⟩
    | succ identity => exact ih selected

theorem NamedFunctionsAdmitted.resolves {sources : List NamedFunction} {program : Program}
    (admitted : NamedFunctionsAdmitted sources program) {name : String} {identity : Nat}
    (resolved : functionNames sources name = some identity) :
    ∃ source core, source.name = name ∧ sources[identity]? = some source ∧
      program.functions identity = some core ∧
      NamedFunction.Elaborates program (functionNames sources) source core := by
  obtain ⟨_, cores, elaborated, functions⟩ := admitted
  obtain ⟨source, selected, named⟩ := functionNames.selected resolved
  obtain ⟨core, emitted, checked⟩ := elaborated.selected selected
  exact ⟨source, core, named, selected, by rw [functions]; exact emitted, checked⟩


theorem NamedFunctionsAdmitted.evaluation_soundness {source : List NamedFunction} {program : Program}
    (admitted : NamedFunctionsAdmitted source program) {home : Module} {scope : SourceScope}
    {expression : NamedExpr} {core : Expr} {type : Ty}
    (elaborated : NamedExpr.Elaborates program (functionNames source) home scope expression core type)
    {environment after : Environment} {value : Value}
    (store : EnvironmentTyped program environment scope.context)
    (evaluated : Evaluates program environment core value after) :
    ValueHasType program value type ∧ EnvironmentTyped program after scope.context ∧
      EnvironmentFrame scope.context environment after :=
  elaborated.evaluation_soundness admitted.checked store evaluated

theorem NamedFunctionsAdmitted.correctness {source : List NamedFunction} {program : Program}
    (admitted : NamedFunctionsAdmitted source program) {home : Module} {scope : SourceScope}
    {expression : NamedExpr} {core : Expr} {type : Ty}
    (elaborated : NamedExpr.Elaborates program (functionNames source) home scope expression core type)
    (finite : FiniteCalls program core) {environment : Environment}
    (store : EnvironmentTyped program environment scope.context) :
    ∃ value after, Evaluates program environment core value after ∧ ValueHasType program value type ∧
      EnvironmentTyped program after scope.context ∧ EnvironmentFrame scope.context environment after ∧
      ∀ other otherAfter, Evaluates program environment core other otherAfter →
        other = value ∧ otherAfter = after :=
  elaborated.correctness admitted.checked finite store


/-- Source admission derives both body checking and actual addressed invocation
entry. This is the storage-entry boundary, not execution of the body. -/
theorem NamedFunctionsAdmitted.enter {sources : List NamedFunction} {program : Program}
    (admitted : NamedFunctionsAdmitted sources program) {identity : Nat} {declaration : FunctionDecl}
    (declared : program.functions identity = some declaration) {values : List Value}
    (arguments : ValuesHaveTypes program values (declaration.parameters.map (fun parameter => parameter.2.type)))
    (heap : RuntimeHeap StorageCell) (supply : ActivationSupply) :
    HasType program declaration.home declaration.parameters declaration.body declaration.result ∧
    ∃ entry, enterFunction heap supply declaration values = some entry ∧
      BindingMap.Typed program entry.heap entry.activation entry.bindings (initializedContext declaration.parameters) ∧
      entry.activation.index = supply.next ∧ entry.supply.next = supply.next + 1 ∧
      (¬supply.Issued entry.activation) ∧ entry.supply.Issued entry.activation ∧
      (∀ previous, supply.Issued previous → entry.supply.Issued previous ∧ previous ≠ entry.activation) ∧
      (∀ caller callerContext owner, BindingMap.Typed program heap owner caller callerContext →
        BindingMap.Typed program entry.heap owner caller callerContext ∧
        ∀ identity ∈ entry.bindings.map Prod.snd, identity ∉ caller.map Prod.snd) := by
  have checked := admitted.checked identity declaration declared
  exact ⟨checked.body, enterFunction.progress arguments checked.distinct heap supply⟩


end Grounded
