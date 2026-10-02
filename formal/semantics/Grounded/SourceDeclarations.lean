import Grounded.FunctionResolution
import Grounded.BindingAccess

/-! Named direct-function declarations supply Program.Checked. Signatures are
available to recursive calls independently of body elaboration. Names are indexed
by declaring module; textual import/path expansion remains a decoding boundary. -/
namespace Grounded

variable {modules : List Module} {imports : List FunctionImport}


/-- Parameter order is preserved in the emitted invocation interface. Static
allocation runs tail-first, exactly as pattern allocation does. -/
inductive NamedParametersElaborate (program : Program) : List NamedParameter → SourceScope → Prop where
  | nil : NamedParametersElaborate program [] .empty
  | cons {parameter rest scope type}
      (tail : NamedParametersElaborate program rest scope)
      (resolved : ResolvesType program.aliases parameter.type type)
      (finite : FiniteLayout program.target program.data type) :
      NamedParametersElaborate program (parameter :: rest) (scope.enter parameter.name ⟨type, parameter.mutable⟩)

theorem NamedParametersElaborate.finite {program : Program} {source : List NamedParameter} {scope : SourceScope}
    (elaborated : NamedParametersElaborate program source scope) :
    ∀ parameter ∈ scope.context, FiniteLayout program.target program.data parameter.2.type := by
  induction elaborated with
  | nil => intro parameter member; simp [SourceScope.context, SourceScope.empty] at member
  | cons tail resolved finite ih =>
    intro parameter member
    simp only [SourceScope.context, SourceScope.enter, List.map_cons, List.mem_cons] at member
    rcases member with rfl | member
    · exact finite
    · exact ih _ member



/-- Source parameter names, omitted-unit result semantics and the actual named
body determine the emitted declaration and final masks before cleanup admission. -/
inductive NamedFunction.BodyElaborates (program : Program) (names : Module → FunctionName → Option Nat) :
    NamedFunction → FunctionDecl → FlowContext → Prop where
  | intro {source scope result body after}
      (parameters : NamedParametersElaborate program source.parameters scope)
      (distinct : (source.parameters.map NamedParameter.name).Nodup)
      (resultType : ResolvesType program.aliases (source.result.getD (.concrete .unit)) result)
      (resultFinite : FiniteLayout program.target program.data result)
      (elaborated : NamedExpr.Elaborates program names source.home scope
        (initializedContext scope.context) source.body body result after) :
      NamedFunction.BodyElaborates program names source
        ⟨source.home, source.visibility, scope.context, result, body⟩ after

/-- Cleanup certification consumes the same body product; it does not elaborate
or select another body to satisfy the ownership obligation. -/
inductive NamedFunction.Elaborates (program : Program) (names : Module → FunctionName → Option Nat) :
    NamedFunction → FunctionDecl → Prop where
  | intro {source core after}
      (body : NamedFunction.BodyElaborates program names source core after)
      (disposable : ∀ binding ∈ after, binding.2.Disposable program.data) :
      NamedFunction.Elaborates program names source core

theorem NamedFunction.Elaborates.checked {program : Program} {names : Module → FunctionName → Option Nat}
    {source : NamedFunction} {core : FunctionDecl}
    (elaborated : NamedFunction.Elaborates program names source core) : FunctionChecked program core := by
  cases elaborated with
  | intro body disposable =>
    cases body with
    | intro parameters distinct resultType resultFinite body =>
      exact ⟨SourceScope.context_distinct _, parameters.finite, resultFinite, _, body.checked (by
        simp [FlowContext.slots, initializedContext, List.map_map, Function.comp_def]), disposable⟩

theorem NamedFunction.Elaborates.origin {program : Program} {names : Module → FunctionName → Option Nat}
    {source : NamedFunction} {core : FunctionDecl}
    (elaborated : NamedFunction.Elaborates program names source core) :
    core.home = source.home ∧ core.visibility = source.visibility := by
  cases elaborated with
  | intro body _ => cases body; exact ⟨rfl, rfl⟩

/-- Finite signature evidence and preserved slots decide all final masks.
Failure is about this supplied elaboration, not all alternative elaborations. -/
theorem NamedFunction.BodyElaborates.disposition_cases {program : Program}
    {names : Module → FunctionName → Option Nat} {source : NamedFunction}
    {core : FunctionDecl} {after : FlowContext}
    (body : NamedFunction.BodyElaborates program names source core after) :
    (∀ binding ∈ after, binding.2.Disposable program.data) ∨
      ∃ binding ∈ after, ¬ binding.2.Disposable program.data := by
  cases body with
  | intro parameters distinct resultType resultFinite elaborated =>
    have checked := elaborated.checked (by
      simp [FlowContext.slots, initializedContext, List.map_map, Function.comp_def])
    apply BindingState.disposable_context_cases
    intro binding member
    have selected : (binding.1, binding.2.slot) ∈ after.slots := List.mem_map.mpr ⟨binding, member, rfl⟩
    rw [checked.slots] at selected
    apply parameters.finite (binding.1, binding.2.slot)
    simpa [FlowContext.slots, initializedContext, List.map_map, Function.comp_def] using selected

inductive NamedFunctionsElaborate (program : Program) (names : Module → FunctionName → Option Nat) :
    List NamedFunction → List FunctionDecl → Prop where
  | nil : NamedFunctionsElaborate program names [] []
  | cons {source sources core cores}
      (head : NamedFunction.Elaborates program names source core)
      (tail : NamedFunctionsElaborate program names sources cores) :
      NamedFunctionsElaborate program names (source :: sources) (core :: cores)

theorem NamedFunctionsElaborate.checked {program : Program} {names : Module → FunctionName → Option Nat}
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

/-- A failed cleanup obligation is attached to the same source/emitted function
index and the actual final mask from body elaboration. -/
def NamedCleanupRejected (program : Program) (names : Module → FunctionName → Option Nat)
    (sources : List NamedFunction) (outputs : List (FunctionDecl × FlowContext)) : Prop :=
  ∃ (identity : Nat), ∃ source core after binding,
    sources[identity]? = some source ∧ outputs[identity]? = some (core, after) ∧
    NamedFunction.BodyElaborates program names source core after ∧
    binding ∈ after ∧ ¬ binding.2.Disposable program.data


/-- Body products retain their final masks in source/emission order, before
any residual cleanup obligation is certified. -/
inductive NamedFunctionBodiesElaborate (program : Program) (names : Module → FunctionName → Option Nat) :
    List NamedFunction → List (FunctionDecl × FlowContext) → Prop where
  | nil : NamedFunctionBodiesElaborate program names [] []
  | cons {source sources core after outputs}
      (body : NamedFunction.BodyElaborates program names source core after)
      (tail : NamedFunctionBodiesElaborate program names sources outputs) :
      NamedFunctionBodiesElaborate program names (source :: sources) ((core, after) :: outputs)

/-- Ordered declaration admission preserves emission indices. Recursion uses
checked signatures; this decision does not require finite call expansion. -/
theorem NamedFunctionsElaborate.disposition_cases {program : Program}
    {names : Module → FunctionName → Option Nat} {sources : List NamedFunction}
    {outputs : List (FunctionDecl × FlowContext)}
    (bodies : NamedFunctionBodiesElaborate program names sources outputs) :
    NamedFunctionsElaborate program names sources (outputs.map Prod.fst) ∨
      NamedCleanupRejected program names sources outputs := by
  induction bodies with
  | nil => exact .inl .nil
  | @cons source sources core after outputs body tail ih =>
    rcases body.disposition_cases with allowed | denied
    · rcases ih with admitted | rejected
      · exact .inl (.cons (.intro body allowed) admitted)
      · obtain ⟨identity, selectedSource, core, after, binding, foundSource, foundOutput, checked, member, denied⟩ := rejected
        exact .inr ⟨identity + 1, selectedSource, core, after, binding,
          by simpa using foundSource, by simpa using foundOutput, checked, member, denied⟩
    · obtain ⟨binding, member, denied⟩ := denied
      exact .inr ⟨0, source, core, after, binding, rfl, rfl, body, member, denied⟩


/-- Declaration elaboration is independent of how the source namespace is
produced. Both decoded imports and package-authorized closure use this same
body-checking and exact-emission contract. -/
def NamedProgramAdmitted (names : Module → FunctionName → Option Nat)
    (source : List NamedFunction) (program : Program) : Prop :=
  (source.map fun declaration => (declaration.home, declaration.name)).Nodup ∧ ∃ core,
    NamedFunctionsElaborate program names source core ∧
    program.functions = (fun identity => core[identity]?) ∧ program.data.Valid program.target ∧
      program.aliases.Valid program.target program.data ∧ program.ConstantsChecked

theorem NamedProgramAdmitted.checked {names : Module → FunctionName → Option Nat}
    {source : List NamedFunction} {program : Program}
    (admitted : NamedProgramAdmitted names source program) : program.Checked := by
  obtain ⟨_, core, elaborated, functions, data, aliases, constants⟩ := admitted
  refine ⟨data, aliases, constants, ?_⟩
  intro identity declaration selected
  rw [functions] at selected
  exact elaborated.checked declaration (List.mem_of_getElem? selected)

/-- Whole-program admission discharges residual cleanup from body products,
without assuming final disposal permission for each function. -/
theorem NamedProgramAdmitted.disposition_cases {program : Program}
    {names : Module → FunctionName → Option Nat} {sources : List NamedFunction}
    {outputs : List (FunctionDecl × FlowContext)}
    (distinct : (sources.map fun declaration => (declaration.home, declaration.name)).Nodup)
    (bodies : NamedFunctionBodiesElaborate program names sources outputs)
    (functions : program.functions = fun identity => (outputs.map Prod.fst)[identity]?)
    (data : program.data.Valid program.target)
    (aliases : program.aliases.Valid program.target program.data)
    (constants : program.ConstantsChecked) :
    (NamedProgramAdmitted names sources program ∧ program.Checked) ∨
      NamedCleanupRejected program names sources outputs := by
  rcases NamedFunctionsElaborate.disposition_cases bodies with admitted | rejected
  · have result : NamedProgramAdmitted names sources program :=
      ⟨distinct, outputs.map Prod.fst, admitted, functions, data, aliases, constants⟩
    exact .inl ⟨result, result.checked⟩
  · exact .inr rejected



/-- Import order preserves the shared declaration-elaboration contract. The
closure layer separately enforces package authorization and module inclusion. -/
theorem NamedProgramAdmitted.imports_congr {source : List NamedFunction} {program : Program}
    (namespaceOf : Module → FunctionName → Option Module)
    {first second : List FunctionImport} (same : ∀ edge, edge ∈ first ↔ edge ∈ second) :
    NamedProgramAdmitted (resolveFunctionNames namespaceOf (functionNames source first)) source program ↔
      NamedProgramAdmitted (resolveFunctionNames namespaceOf (functionNames source second)) source program := by
  have names : functionNames source first = functionNames source second := by
    funext caller home name
    exact functionNames.imports_congr same caller home name
  rw [names]

/-- Public source safety obtains declaration-body correctness from named source
admission, rather than accepting Program.Checked from the caller. -/
theorem NamedProgramAdmitted.soundness {source : List NamedFunction} {program : Program}
    {names : Module → FunctionName → Option Nat}
    (admitted : NamedProgramAdmitted names source program) {home : Module} {scope : SourceScope}
    {expression : NamedExpr} {core : Expr} {type : Ty} {before final : FlowContext}
    (elaborated : NamedExpr.Elaborates program names home scope before expression core type final)
    (slots : before.slots = scope.context)
    {environment : Environment} (store : BindingMap.Typed program environment.heap environment.activation environment.bindings before)
    (issued : environment.supply.Issued environment.activation)
    {state : Configuration} (run : Run program ⟨environment, .expression core, []⟩ state) :
    ConfigurationTyped program final (.one type) state ∧
      (Terminal state ∨ ∃ next, Step program state next) ∧
      AddressedEnvironment.ConsumptionFrame program final.slots environment state.outerEnvironment ∧
      (state.environment.bindings.map Prod.fst).Nodup ∧ state.OwnershipSafe program :=
  elaborated.soundness slots admitted.checked store issued run



theorem NamedFunctionsElaborate.selected {program : Program} {names : Module → FunctionName → Option Nat}
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

theorem NamedFunctionsElaborate.selected_core {program : Program} {names : Module → FunctionName → Option Nat}
    {sources : List NamedFunction} {cores : List FunctionDecl}
    (elaborated : NamedFunctionsElaborate program names sources cores)
    {identity : Nat} {core : FunctionDecl} (selected : cores[identity]? = some core) :
    ∃ source, sources[identity]? = some source ∧ NamedFunction.Elaborates program names source core := by
  induction elaborated generalizing identity with
  | nil => simp at selected
  | cons head tail ih =>
    cases identity with
    | zero => cases selected; exact ⟨_, rfl, head⟩
    | succ identity => exact ih selected


theorem NamedProgramAdmitted.evaluation_soundness {source : List NamedFunction} {program : Program}
    {names : Module → FunctionName → Option Nat}
    (admitted : NamedProgramAdmitted names source program) {home : Module} {scope : SourceScope}
    {expression : NamedExpr} {core : Expr} {type : Ty} {before final : FlowContext}
    (elaborated : NamedExpr.Elaborates program names home scope before expression core type final)
    (slots : before.slots = scope.context)
    {environment after : Environment} {value : Value}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings before)
    (issued : environment.supply.Issued environment.activation)
    (evaluated : Evaluates program environment core value after) :
    ValueHasType program value type ∧ BindingMap.Typed program after.heap after.activation after.bindings final ∧
      after.supply.Issued after.activation ∧
      AddressedEnvironment.ConsumptionFrame program final.slots environment after ∧
      ∀ originalType principal, ValueHasType program value originalType →
        originalType.HasPrincipal program.data principal → type.HasPrincipal program.data principal :=
  elaborated.evaluation_soundness slots admitted.checked store issued evaluated

theorem NamedProgramAdmitted.correctness {source : List NamedFunction} {program : Program}
    {names : Module → FunctionName → Option Nat}
    (admitted : NamedProgramAdmitted names source program) {home : Module} {scope : SourceScope}
    {expression : NamedExpr} {core : Expr} {type : Ty} {before final : FlowContext}
    (elaborated : NamedExpr.Elaborates program names home scope before expression core type final)
    (slots : before.slots = scope.context)
    (finite : FiniteCalls program core) {environment : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings before)
    (issued : environment.supply.Issued environment.activation) :
    ∃ value after, Evaluates program environment core value after ∧ ValueHasType program value type ∧
      BindingMap.Typed program after.heap after.activation after.bindings final ∧
      after.supply.Issued after.activation ∧ AddressedEnvironment.ConsumptionFrame program final.slots environment after ∧
      (∃ principal, type.HasPrincipal program.data principal ∧
        ∀ originalType originalPrincipal, ValueHasType program value originalType →
          originalType.HasPrincipal program.data originalPrincipal → originalPrincipal = principal) ∧
      ∀ other otherAfter, Evaluates program environment core other otherAfter →
        other = value ∧ otherAfter = after :=
  elaborated.correctness slots admitted.checked finite store issued


/-- Source admission derives both body checking and actual addressed invocation
entry. This is the storage-entry boundary, not execution of the body. -/
theorem NamedProgramAdmitted.enter {sources : List NamedFunction} {program : Program}
    {names : Module → FunctionName → Option Nat}
    (admitted : NamedProgramAdmitted names sources program) {identity : Nat} {declaration : FunctionDecl}
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
  have checked := admitted.checked.functions identity declaration declared
  obtain ⟨entry, entered, typed, activation, supplyNext, fresh, issued, older, callers⟩ :=
    enterFunction.progress arguments checked.distinct heap supply
  exact ⟨⟨_, checked.body.choose_spec.1⟩, entry, entered, .initialized typed issued, activation, supplyNext, fresh, older, callers⟩


end Grounded
