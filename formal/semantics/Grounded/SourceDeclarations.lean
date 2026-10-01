import Grounded.SourceExpressions
import Grounded.BindingAccess

/-! Named direct-function declarations supply Program.Checked. Signatures are
available to recursive calls independently of body elaboration. Names are indexed
by declaring module; textual import/path expansion remains a decoding boundary. -/
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
inductive NamedFunction.Elaborates (program : Program) (names : Module → String → Option Nat) :
    NamedFunction → FunctionDecl → Prop where
  | intro {source scope result body after}
      (parameters : NamedParametersElaborate program source.parameters scope)
      (distinct : (source.parameters.map NamedParameter.name).Nodup)
      (resultType : ResolvesType program.aliases (source.result.getD (.concrete .unit)) result)
      (elaborated : NamedExpr.Elaborates program names source.home scope (initializedContext scope.context) source.body body result after) :
      NamedFunction.Elaborates program names source
        ⟨source.home, source.visibility, scope.context, result, body⟩

theorem NamedFunction.Elaborates.checked {program : Program} {names : Module → String → Option Nat}
    {source : NamedFunction} {core : FunctionDecl}
    (elaborated : NamedFunction.Elaborates program names source core) : FunctionChecked program core := by
  cases elaborated with
  | intro parameters distinct resultType body =>
    exact ⟨SourceScope.context_distinct _, parameters.disposable, _, body.checked (by
      simp [FlowContext.slots, initializedContext, List.map_map, Function.comp_def])⟩

/-- Declaration identities are the source-list positions. Duplicate qualified
names are rejected by program admission rather than resolved by first-wins. -/
def functionNames (source : List NamedFunction) (home : Module) (name : String) : Option Nat :=
  source.findIdx? (fun declaration => decide (declaration.home = home ∧ declaration.name = name))

inductive NamedFunctionsElaborate (program : Program) (names : Module → String → Option Nat) :
    List NamedFunction → List FunctionDecl → Prop where
  | nil : NamedFunctionsElaborate program names [] []
  | cons {source sources core cores}
      (head : NamedFunction.Elaborates program names source core)
      (tail : NamedFunctionsElaborate program names sources cores) :
      NamedFunctionsElaborate program names (source :: sources) (core :: cores)

theorem NamedFunctionsElaborate.checked {program : Program} {names : Module → String → Option Nat}
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
  (source.map fun declaration => (declaration.home, declaration.name)).Nodup ∧ ∃ core,
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
    {expression : NamedExpr} {core : Expr} {type : Ty} {before final : FlowContext}
    (elaborated : NamedExpr.Elaborates program (functionNames source) home scope before expression core type final)
    (slots : before.slots = scope.context)
    {environment : Environment} (store : BindingMap.Typed program environment.heap environment.activation environment.bindings before)
    (issued : environment.supply.Issued environment.activation)
    {state : Configuration} (run : Run program ⟨environment, .expression core, []⟩ state) :
    ConfigurationTyped program final (.one type) state ∧
      (Terminal state ∨ ∃ next, Step program state next) ∧
      AddressedEnvironment.ConsumptionFrame program final.slots environment state.outerEnvironment ∧
      (state.environment.bindings.map Prod.fst).Nodup :=
  elaborated.soundness slots admitted.checked store issued run

/-- A resolved source name selects the same list position used for the emitted
runtime declaration, including forward references and mutually recursive calls. -/
theorem functionNames.selected {source : List NamedFunction} {home : Module} {name : String} {identity : Nat}
    (resolved : functionNames source home name = some identity) :
    ∃ declaration, source[identity]? = some declaration ∧ declaration.home = home ∧ declaration.name = name := by
  obtain ⟨bound, equal, _⟩ := List.findIdx?_eq_some_iff_getElem.mp resolved
  exact ⟨source[identity], List.getElem?_eq_some_iff.mpr ⟨bound, rfl⟩, by simpa using equal⟩

theorem functionNames.missing (source : List NamedFunction) (home : Module) (name : String) :
    functionNames source home name = none ↔
      ∀ declaration ∈ source, declaration.home = home → declaration.name ≠ name := by
  simp [functionNames, List.findIdx?_eq_none_iff]

theorem NamedFunctionsElaborate.selected {program : Program} {names : Module → String → Option Nat}
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
    (admitted : NamedFunctionsAdmitted sources program) {home : Module} {name : String} {identity : Nat}
    (resolved : functionNames sources home name = some identity) :
    ∃ source core, source.home = home ∧ source.name = name ∧ sources[identity]? = some source ∧
      program.functions identity = some core ∧
      NamedFunction.Elaborates program (functionNames sources) source core := by
  obtain ⟨_, cores, elaborated, functions⟩ := admitted
  obtain ⟨source, selected, owner, named⟩ := functionNames.selected resolved
  obtain ⟨core, emitted, checked⟩ := elaborated.selected selected
  exact ⟨source, core, owner, named, selected, by rw [functions]; exact emitted, checked⟩

/-- Source resolution and runtime invocation select one declaration with the
requested module identity. Qualification never bypasses its visibility. -/
theorem NamedFunctionsAdmitted.call_resolution {sources : List NamedFunction} {program : Program}
    (admitted : NamedFunctionsAdmitted sources program) {home : Module} {scope : SourceScope}
    {before after : FlowContext} {name : FunctionName} {arguments : List NamedExpr}
    {core : Expr} {type : Ty}
    (elaborated : NamedExpr.Elaborates program (functionNames sources) home scope before
      (.call name arguments) core type after) :
    ∃ identity declaration inputs, core = .call identity inputs ∧
      program.functions identity = some declaration ∧ declaration.home = name.owner home ∧
      declaration.visibility.Allows declaration.home home := by
  cases elaborated with
  | call _ resolved declared visible _ =>
    obtain ⟨source, emitted, owner, _, _, found, body⟩ := admitted.resolves resolved
    have same := Option.some.inj (declared.symm.trans found)
    subst emitted
    refine ⟨_, _, _, rfl, declared, ?_, visible⟩
    calc
      _ = source.home := by cases body; rfl
      _ = _ := owner



theorem NamedFunctionsAdmitted.evaluation_soundness {source : List NamedFunction} {program : Program}
    (admitted : NamedFunctionsAdmitted source program) {home : Module} {scope : SourceScope}
    {expression : NamedExpr} {core : Expr} {type : Ty} {before final : FlowContext}
    (elaborated : NamedExpr.Elaborates program (functionNames source) home scope before expression core type final)
    (slots : before.slots = scope.context)
    {environment after : Environment} {value : Value}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings before)
    (issued : environment.supply.Issued environment.activation)
    (evaluated : Evaluates program environment core value after) :
    ValueHasType program value type ∧ BindingMap.Typed program after.heap after.activation after.bindings final ∧
      after.supply.Issued after.activation ∧
      AddressedEnvironment.ConsumptionFrame program final.slots environment after :=
  elaborated.evaluation_soundness slots admitted.checked store issued evaluated

theorem NamedFunctionsAdmitted.correctness {source : List NamedFunction} {program : Program}
    (admitted : NamedFunctionsAdmitted source program) {home : Module} {scope : SourceScope}
    {expression : NamedExpr} {core : Expr} {type : Ty} {before final : FlowContext}
    (elaborated : NamedExpr.Elaborates program (functionNames source) home scope before expression core type final)
    (slots : before.slots = scope.context)
    (finite : FiniteCalls program core) {environment : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings before)
    (issued : environment.supply.Issued environment.activation) :
    ∃ value after, Evaluates program environment core value after ∧ ValueHasType program value type ∧
      BindingMap.Typed program after.heap after.activation after.bindings final ∧
      after.supply.Issued after.activation ∧ AddressedEnvironment.ConsumptionFrame program final.slots environment after ∧
      ∀ other otherAfter, Evaluates program environment core other otherAfter →
        other = value ∧ otherAfter = after :=
  elaborated.correctness slots admitted.checked finite store issued


/-- Source admission derives both body checking and actual addressed invocation
entry. This is the storage-entry boundary, not execution of the body. -/
theorem NamedFunctionsAdmitted.enter {sources : List NamedFunction} {program : Program}
    (admitted : NamedFunctionsAdmitted sources program) {identity : Nat} {declaration : FunctionDecl}
    (declared : program.functions identity = some declaration) {values : List Value}
    (arguments : ValuesHaveTypes program values (declaration.parameters.map (fun parameter => parameter.2.type)))
    (heap : RuntimeHeap StorageCell) (supply : ActivationSupply) :
    (∃ final, HasType program declaration.home (initializedContext declaration.parameters) declaration.body declaration.result final) ∧
    ∃ entry, enterFunction heap supply declaration values = some entry ∧
      entry.Realizes program declaration.parameters ∧
      entry.activation.index = supply.next ∧ entry.supply.next = supply.next + 1 ∧
      (¬supply.Issued entry.activation) ∧
      (∀ previous, supply.Issued previous → entry.supply.Issued previous ∧ previous ≠ entry.activation) ∧
      (∀ caller callerContext owner, BindingMap.Typed program heap owner caller callerContext →
        BindingMap.Typed program entry.heap owner caller callerContext ∧
        (∀ identity ∈ entry.bindings.map Prod.snd, identity ∉ caller.map Prod.snd) ∧
        (∀ identity ∈ caller.map Prod.snd, entry.heap.read identity = heap.read identity)) := by
  have checked := admitted.checked identity declaration declared
  obtain ⟨entry, entered, typed, activation, supplyNext, fresh, issued, older, callers⟩ :=
    enterFunction.progress arguments checked.distinct heap supply
  exact ⟨checked.body, entry, entered, .initialized typed issued, activation, supplyNext, fresh, older, callers⟩


end Grounded
