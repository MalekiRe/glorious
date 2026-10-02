import Grounded.NamedPatterns

/-! Recursive elaboration of named expressions in the flow-sensitive logical
fragment. Named calls use the source declaration environment; core calls use IDs.
Named patterns and bodies share the same allocated lexical scope. -/
namespace Grounded

/-- Decoded module-path anchors. Parent depth counts additional `super`
components: zero selects the immediate parent. Byte/token parsing is separate. -/
inductive ModulePath where
  | «self» (children : List Identifier)
  | «crate» (children : List Identifier)
  | «super» (additional : Nat) (children : List Identifier)
  | dependency (name : Identifier) (children : List Identifier)

/-- Path interpretation produces an identity, not visibility or authority.
Climbing beyond the root fails; an absent dependency never becomes a package. -/
def ModulePath.resolve (dependencies : Identifier → Option Nat) (caller : Module) : ModulePath → Option Module
  | .self children => some ⟨caller.package, caller.path ++ children⟩
  | .crate children => some ⟨caller.package, children⟩
  | .super additional children =>
      if additional + 1 ≤ caller.path.length then
        some ⟨caller.package, caller.path.take (caller.path.length - (additional + 1)) ++ children⟩
      else none
  | .dependency name children => (dependencies name).map fun package => ⟨package, children⟩

theorem ModulePath.resolve_super {dependencies : Identifier → Option Nat} {caller : Module}
    {ancestor suffix : List Identifier} {additional : Nat} (children : List Identifier)
    (path : caller.path = ancestor ++ suffix) (depth : suffix.length = additional + 1) :
    ModulePath.resolve dependencies caller (.super additional children) =
      some ⟨caller.package, ancestor ++ children⟩ := by
  simp [ModulePath.resolve, path, ← depth]

theorem ModulePath.resolve_super_none (dependencies : Identifier → Option Nat) (caller : Module)
    (additional : Nat) (children : List Identifier) :
    ModulePath.resolve dependencies caller (.super additional children) = none ↔
      caller.path.length < additional + 1 := by
  simp [ModulePath.resolve]


inductive FunctionName where
  | unqualified (spelling : Identifier)
  | qualified (path : ModulePath) (spelling : Identifier)

def FunctionName.namespace (dependencies : Identifier → Option Nat) (caller : Module) : FunctionName → Option Module
  | .unqualified _ => some caller
  | .qualified path _ => path.resolve dependencies caller


def FunctionName.spelling : FunctionName → Identifier
  | .unqualified spelling | .qualified _ spelling => spelling

/-- Compose source namespace interpretation with the shared binding resolver. -/
def resolveFunctionNames (namespaceOf : Module → FunctionName → Option Module)
    (bindings : Module → Module → Identifier → Option Nat) (caller : Module) (name : FunctionName) : Option Nat :=
  (namespaceOf caller name).bind fun home => bindings caller home name.spelling

def FunctionName.Unshadowed (scope : SourceScope) : FunctionName → Prop
  | .unqualified spelling => scope.resolve spelling = none
  | .qualified _ _ => True

inductive NamedExpr where
  | unit
  | integer (type : IntegerType) (magnitude : Nat)
  | character (number : Nat)
  | group (body : NamedExpr)
  | read (name : Identifier) (fields : List FieldKey)
  | move (name : Identifier) (fields : List FieldKey)
  | sequence (first rest : NamedExpr)
  | bind (mutable : Bool) (name : Identifier) (annotation : Option TypeExpr) (initial body : NamedExpr)
  | tuple (head : NamedExpr) (tail : List NamedExpr)
  | project (body : NamedExpr) (key : FieldKey)
  | array (elements : List NamedExpr)
  | constant (name : String)
  | construct (identity : Nat) (tag : Option Nat) (fields : List NamedExpr)
  | call (name : FunctionName) (arguments : List NamedExpr)
  | assign (name : Identifier) (fields : List FieldKey) (value rest : NamedExpr)
  | applyPatterns (arguments : List NamedExpr) (arms : List (NamedPattern × NamedExpr))

mutual
/-- Name resolution and static availability are composed in evaluation order.
No operational success or successor heap is an admission premise. -/
inductive NamedExpr.Elaborates (program : Program) (names : Module → FunctionName → Option Nat) (home : Module) :
    SourceScope → FlowContext → NamedExpr → Expr → Ty → FlowContext → Prop where
  | unit {scope context} : NamedExpr.Elaborates program names home scope context .unit .unit .unit context
  | integer {scope context type magnitude} (fits : type.Contains program.target magnitude) :
      NamedExpr.Elaborates program names home scope context (.integer type magnitude) (.integer type magnitude) (.integer type) context
  | character {scope context number} (valid : UnicodeScalar number) :
      NamedExpr.Elaborates program names home scope context (.character number) (.character number) .character context
  | group {scope before after source core type}
      (body : NamedExpr.Elaborates program names home scope before source core type after) :
      NamedExpr.Elaborates program names home scope before (.group source) (.group core) type after
  | read {scope context name fields binding type state available}
      (resolved : scope.resolve name = some binding)
      (selected : lookup binding.identity context = some state)
      (path : PathType program home binding.slot.type fields type)
      (selection : state.initialization.selectFields program binding.slot.type fields = some available)
      (ready : available.Ready) (copyable : UsePermitted program.data .copy type) :
      NamedExpr.Elaborates program names home scope context (.read name fields) (.read ⟨binding.identity, fields⟩) type context
  | readMove {scope before after name fields binding type state available updated}
      (resolved : scope.resolve name = some binding)
      (selected : lookup binding.identity before = some state)
      (path : PathType program home binding.slot.type fields type)
      (selection : state.initialization.selectFields program binding.slot.type fields = some available)
      (ready : available.Ready) (noncopyable : ¬ UsePermitted program.data .copy type)
      (mask : state.initialization.writeFields program binding.slot.type fields .absent = some updated)
      (context : replaceBinding binding.identity { state with initialization := updated } before = some after) :
      NamedExpr.Elaborates program names home scope before (.read name fields) (.move ⟨binding.identity, fields⟩) type after
  | move {scope before after name fields binding type state available updated}
      (resolved : scope.resolve name = some binding)
      (selected : lookup binding.identity before = some state)
      (path : PathType program home binding.slot.type fields type)
      (selection : state.initialization.selectFields program binding.slot.type fields = some available)
      (ready : available.Ready)
      (mask : state.initialization.writeFields program binding.slot.type fields .absent = some updated)
      (context : replaceBinding binding.identity { state with initialization := updated } before = some after) :
      NamedExpr.Elaborates program names home scope before (.move name fields) (.move ⟨binding.identity, fields⟩) type after
  | sequence {scope before middle after first rest head tail discarded type}
      (initial : NamedExpr.Elaborates program names home scope before first head discarded middle)
      (discard : UsePermitted program.data .discard discarded)
      (continued : NamedExpr.Elaborates program names home scope middle rest tail type after) :
      NamedExpr.Elaborates program names home scope before (.sequence first rest) (.sequence head tail) type after
  | bind {scope before middle after mutable name annotation initial body first rest localType type finalMask}
      (initialized : NamedExpr.Elaborates program names home scope before initial first localType middle)
      (discard : finalMask.Disposable program.data localType)
      (annotated : Annotation program.aliases annotation localType)
      (continued : NamedExpr.Elaborates program names home (scope.enter name ⟨localType, mutable⟩)
        ((⟨scope.next⟩, ⟨⟨localType, mutable⟩, .present⟩) :: middle) body rest type
        ((⟨scope.next⟩, ⟨⟨localType, mutable⟩, finalMask⟩) :: after)) :
      NamedExpr.Elaborates program names home scope before (.bind mutable name annotation initial body)
        (.bind mutable ⟨scope.next⟩ localType first rest) type after
  | tuple {scope before middle after head tail first rest type types}
      (initial : NamedExpr.Elaborates program names home scope before head first type middle)
      (continued : NamedExprsElaborate program names home scope middle tail rest types after) :
      NamedExpr.Elaborates program names home scope before (.tuple head tail) (.tuple first rest) (.tuple type types) after
  | project {scope before after source core key parent type index residual}
      (body : NamedExpr.Elaborates program names home scope before source core parent after)
      (discard : residual.Disposable program.data parent)
      (mask : Initialization.present.writeFields program parent [key] .absent = some residual)
      (selected : ProjectionType program home parent key index type) :
      NamedExpr.Elaborates program names home scope before (.project source key) (.project home core key) type after
  | array {scope before after source core element length}
      (residents : NamedExprsElaborate program names home scope before source core (List.replicate length element) after)
      (finite : FiniteLayout program.target program.data element) (size : length < 2 ^ program.target.pointerBits) :
      NamedExpr.Elaborates program names home scope before (.array source) (.array core) (.array element length) after
  | constant {scope context name type} (checked : HasType program home [] (.constant name) type []) :
      NamedExpr.Elaborates program names home scope context (.constant name) (.constant name) type context
  | construct {scope before after identity tag declaration schema source core}
      (declared : program.data identity = some declaration) (chosen : declaration.constructor tag = some schema)
      (finite : FiniteLayout program.target program.data (.nominal identity))
      (visible : declaration.visibility.Allows declaration.home home)
      (access : ∀ field ∈ schema.residents, field.visibility.Allows declaration.home home)
      (residents : NamedExprsElaborate program names home scope before source core (schema.residents.map Field.type) after) :
      NamedExpr.Elaborates program names home scope before (.construct identity tag source) (.construct identity tag core) (.nominal identity) after
  | call {scope before after name identity declaration source core}
      (unshadowed : name.Unshadowed scope)
      (resolved : names home name = some identity)
      (declared : program.functions identity = some declaration)
      (visible : declaration.visibility.Allows declaration.home home)
      (inputs : NamedExprsElaborate program names home scope before source core
        (declaration.parameters.map fun parameter => parameter.2.type) after) :
      NamedExpr.Elaborates program names home scope before (.call name source) (.call identity core) declaration.result after
  | assign {scope before evaluated restored after name fields binding type result value rest coreValue coreRest state updated available}
      (resolved : scope.resolve name = some binding)
      (resident : NamedExpr.Elaborates program names home scope before value coreValue type evaluated)
      (selected : lookup binding.identity evaluated = some state)
      (path : PathType program home binding.slot.type fields type)
      (writable : binding.slot.mutable = true)
      (selection : state.initialization.selectFields program binding.slot.type fields = some available)
      (discard : available.Disposable program.data type)
      (mask : state.initialization.writeFields program binding.slot.type fields .present = some updated)
      (context : replaceBinding binding.identity { state with initialization := updated } evaluated = some restored)
      (continued : NamedExpr.Elaborates program names home scope restored rest coreRest result after) :
      NamedExpr.Elaborates program names home scope before (.assign name fields value rest)
        (.assign home ⟨binding.identity, fields⟩ coreValue coreRest) result after
  | applyPatterns {scope before evaluated after arguments coreArguments inputs arms coreArms result}
      (inputsTyped : NamedExprsElaborate program names home scope before arguments coreArguments inputs evaluated)
      (nonempty : coreArms ≠ []) (covered : Covers program home [argumentType inputs] (coreArms.map fun arm => [arm.1]))
      (bodies : NamedArmsElaborate program names home scope evaluated (argumentType inputs) result [] arms coreArms after) :
      NamedExpr.Elaborates program names home scope before (.applyPatterns arguments arms)
        (.applyPatterns home inputs coreArguments coreArms) result after
inductive NamedExprsElaborate (program : Program) (names : Module → FunctionName → Option Nat) (home : Module) :
    SourceScope → FlowContext → List NamedExpr → List Expr → List Ty → FlowContext → Prop where
  | nil {scope context} : NamedExprsElaborate program names home scope context [] [] [] context
  | cons {scope before middle after head tail first rest type types}
      (initial : NamedExpr.Elaborates program names home scope before head first type middle)
      (continued : NamedExprsElaborate program names home scope middle tail rest types after) :
      NamedExprsElaborate program names home scope before (head :: tail) (first :: rest) (type :: types) after
inductive NamedArmsElaborate (program : Program) (names : Module → FunctionName → Option Nat) (home : Module) :
    SourceScope → FlowContext → Ty → Ty → List Pattern → List (NamedPattern × NamedExpr) → List (Pattern × Expr) → FlowContext → Prop where
  | empty {scope before after subject result previous} : NamedArmsElaborate program names home scope before subject result previous [] [] after
  | clause {scope localScope before after branchAfter subject result previous source pattern bindings localsAfter body coreBody tail coreTail}
      (allocated : NamedPattern.Elaborates program home scope source subject pattern bindings localScope)
      (namesDistinct : source.binders.Nodup) (useful : Useful program subject previous pattern)
      (bodyTyped : NamedExpr.Elaborates program names home localScope (initializedContext bindings ++ before)
        body coreBody result (localsAfter ++ branchAfter))
      (localSlots : localsAfter.slots = bindings)
      (disposable : ∀ binding ∈ localsAfter, binding.2.Disposable program.data)
      (joined : BindingContextApprox program.data branchAfter after)
      (tailTyped : NamedArmsElaborate program names home scope before subject result (previous ++ [pattern]) tail coreTail after) :
      NamedArmsElaborate program names home scope before subject result previous ((source, body) :: tail) ((pattern, coreBody) :: coreTail) after
end

/-- Local value bindings hide direct-function names regardless of the expected
result or argument types. Local callable invocation is a separate language
operation; failure to support it must not expose the hidden declaration. -/
theorem NamedExpr.Elaborates.call_not_shadowed {program : Program}
    {names : Module → FunctionName → Option Nat} {home : Module} {scope : SourceScope}
    {before after : FlowContext} {name : Identifier} {arguments : List NamedExpr}
    {core : Expr} {type : Ty}
    (elaborated : NamedExpr.Elaborates program names home scope before
      (.call (.unqualified name) arguments) core type after) : scope.resolve name = none := by
  cases elaborated with
  | call unshadowed _ _ _ _ => exact unshadowed

/-- Elaboration preserves the authoritative flow checking judgment. The static
name scope and flow context agree on declarations, not on future readiness. -/
theorem NamedExpr.Elaborates.checked {program : Program} {home : Module} {names : Module → FunctionName → Option Nat}
    {scope : SourceScope} {before after : FlowContext} {source : NamedExpr} {core : Expr} {type : Ty}
    (elaborated : NamedExpr.Elaborates program names home scope before source core type after)
    (slots : before.slots = scope.context) : HasType program home before core type after := by
  induction elaborated using NamedExpr.Elaborates.rec
    (motive_2 := fun scope before _ core types after _ => before.slots = scope.context → HasTypes program home before core types after)
    (motive_3 := fun scope before subject result previous _ arms after _ =>
      before.slots = scope.context → ArmsType program home before subject result previous arms after) with
  | unit => exact .unit
  | integer fits => exact .integer fits
  | character valid => exact .character valid
  | group _ ih => exact .group (ih slots)
  | read resolved selected path selection ready copyable =>
    exact SourceScope.read_checked resolved slots selected path selection ready copyable
  | readMove resolved selected path selection ready noncopyable mask context =>
    exact SourceScope.move_checked resolved slots selected path selection ready mask context
  | move resolved selected path selection ready mask context =>
    exact SourceScope.move_checked resolved slots selected path selection ready mask context
  | sequence _ discard _ head tail =>
    have first := head slots
    exact .sequence first discard (tail (first.slots.trans slots))
  | bind _ discard _ _ first rest =>
    have initial := first slots
    apply SourceScope.bind_checked _ _ slots initial discard
    apply rest
    simp only [FlowContext.slots, SourceScope.context, SourceScope.enter, List.map_cons]
    congr 1
    exact initial.slots.trans slots
  | tuple _ _ head tail =>
    have first := head slots
    exact .tuple first (tail (first.slots.trans slots))
  | project _ discard mask selected ih => exact .project (ih slots) discard mask selected
  | array _ finite size ih => exact .array (ih slots) finite size
  | constant checked => cases checked with
    | constant declared visible resolved structural initialized => exact .constant declared visible resolved structural initialized
  | construct declared chosen finite visible access _ ih =>
    exact .construct declared chosen finite visible access (ih slots)
  | call _ _ declared visible _ ih => exact .call declared visible (ih slots)
  | assign resolved _ selected path writable selection discard mask context _ first rest =>
    have resident := first slots
    apply SourceScope.assign_checked resolved slots resident selected path writable selection discard mask context
    apply rest
    exact (replaceBinding.map_same BindingState.slot selected context rfl).trans (resident.slots.trans slots)
  | applyPatterns _ nonempty covered _ inputs bodies =>
    have arguments := inputs slots
    exact .applyPatterns arguments nonempty covered (bodies (arguments.slots.trans slots))
  | nil => exact .nil
  | cons _ _ head tail =>
    rename_i slots
    have first := head slots
    exact .cons first (tail (first.slots.trans slots))
  | empty => exact .empty
  | clause allocated _ useful _ localSlots disposable joined _ body tail =>
    rename_i slots
    apply ArmsType.clause allocated.checked.1 (by rw [slots]; exact allocated.fresh) useful
      (body ?_) localSlots disposable joined (tail slots)
    rw [allocated.checked.2]
    simp [FlowContext.slots, initializedContext, List.map_append, List.map_map, Function.comp_def, ← slots]

theorem NamedExprsElaborate.checked {program : Program} {home : Module} {names : Module → FunctionName → Option Nat}
    {scope : SourceScope} {before after : FlowContext} {source : List NamedExpr} {core : List Expr} {types : List Ty}
    (elaborated : NamedExprsElaborate program names home scope before source core types after)
    (slots : before.slots = scope.context) : HasTypes program home before core types after := by
  induction source generalizing before after core types with
  | nil => cases elaborated; exact .nil
  | cons head tail ih =>
    cases elaborated with
    | cons first rest =>
      have checked := first.checked slots
      exact .cons checked (ih rest (checked.slots.trans slots))

/-- Every prefix of the selected elaboration is safe, including recursive calls.
The only dynamic input evidence describes the actual incoming environment. -/
theorem NamedExpr.Elaborates.soundness {program : Program} {home : Module}
    {names : Module → FunctionName → Option Nat}
    {scope : SourceScope} {before final : FlowContext} {source : NamedExpr} {core : Expr} {type : Ty}
    (elaborated : NamedExpr.Elaborates program names home scope before source core type final)
    (slots : before.slots = scope.context)
    (checkedProgram : program.Checked) {environment : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings before)
    (issued : environment.supply.Issued environment.activation) {state : Configuration}
    (run : Run program ⟨environment, .expression core, []⟩ state) :
    ConfigurationTyped program final (.one type) state ∧
      (Terminal state ∨ ∃ next, Step program state next) ∧
      AddressedEnvironment.ConsumptionFrame program final.slots environment state.outerEnvironment ∧
      (state.environment.bindings.map Prod.fst).Nodup ∧ state.OwnershipSafe program :=
  (elaborated.checked slots).soundness checkedProgram store issued run

/-- Ordinary owned syntax chooses Copy exactly when the selected type permits
it. Otherwise it constructs the same mask update as an explicit move. -/
theorem NamedExpr.Elaborates.ordinary_exists {program : Program} {home : Module}
    {names : Module → FunctionName → Option Nat} {scope : SourceScope} {before : FlowContext}
    {name : Identifier} {fields : List FieldKey} {binding : SourceBinding} {type : Ty}
    {state : BindingState} {available : Initialization}
    (resolved : scope.resolve name = some binding)
    (selected : lookup binding.identity before = some state)
    (path : PathType program home binding.slot.type fields type)
    (selection : state.initialization.selectFields program binding.slot.type fields = some available)
    (ready : available.Ready) :
    ∃ core after, NamedExpr.Elaborates program names home scope before (.read name fields) core type after ∧
      (UsePermitted program.data .copy type → core = .read ⟨binding.identity, fields⟩ ∧ after = before) ∧
      (¬ UsePermitted program.data .copy type → core = .move ⟨binding.identity, fields⟩) := by
  classical
  by_cases copyable : UsePermitted program.data .copy type
  · exact ⟨_, before, .read resolved selected path selection ready copyable,
      fun _ => ⟨rfl, rfl⟩, fun denied => False.elim (denied copyable)⟩
  · obtain ⟨updated, mask⟩ := Initialization.write_exists selection .absent
    obtain ⟨after, context⟩ := replaceBinding.exists selected { state with initialization := updated }
    exact ⟨_, after, .readMove resolved selected path selection ready copyable mask context,
      fun allowed => False.elim (copyable allowed), fun _ => rfl⟩

/-- Construct source acquisition and its actual typed successor from incoming
readiness. Neither a future mask, successful move, nor executable realization
is an admission premise. Explicit move remains independent of Copy capability. -/
theorem NamedExpr.Elaborates.ordinary_progress {program : Program} {home : Module}
    {names : Module → FunctionName → Option Nat} {scope : SourceScope} {before : FlowContext}
    {name : Identifier} {fields : List FieldKey} {binding : SourceBinding} {type : Ty}
    {state : BindingState} {available : Initialization}
    (resolved : scope.resolve name = some binding)
    (selected : lookup binding.identity before = some state)
    (path : PathType program home binding.slot.type fields type)
    (selection : state.initialization.selectFields program binding.slot.type fields = some available)
    (ready : available.Ready) (slots : before.slots = scope.context)
    (checkedProgram : program.Checked) {environment : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings before)
    (issued : environment.supply.Issued environment.activation) :
    ∃ core after next,
      NamedExpr.Elaborates program names home scope before (.read name fields) core type after ∧
      (UsePermitted program.data .copy type → core = .read ⟨binding.identity, fields⟩ ∧ after = before) ∧
      (¬ UsePermitted program.data .copy type → core = .move ⟨binding.identity, fields⟩) ∧
      Step program ⟨environment, .expression core, []⟩ next ∧
      ConfigurationTyped program after (.one type) next := by
  obtain ⟨core, after, elaborated, copies, moves⟩ :=
    NamedExpr.Elaborates.ordinary_exists (names := names) resolved selected path selection ready
  have initial := elaborated.soundness slots checkedProgram store issued (.refl _)
  rcases initial.2.1 with terminal | ⟨next, stepped⟩
  · cases terminal
  · exact ⟨core, after, next, elaborated, copies, moves, stepped,
      initial.1.preservation checkedProgram stepped⟩
/-- Completed executions preserve the declared result and caller environment;
termination is not assumed by source admission. -/
theorem NamedExpr.Elaborates.evaluation_soundness {program : Program} {home : Module}
    {names : Module → FunctionName → Option Nat}
    {scope : SourceScope} {before final : FlowContext} {source : NamedExpr} {core : Expr} {type : Ty}
    (elaborated : NamedExpr.Elaborates program names home scope before source core type final)
    (slots : before.slots = scope.context)
    (checkedProgram : program.Checked) {environment after : Environment} {value : Value}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings before)
    (issued : environment.supply.Issued environment.activation)
    (evaluated : Evaluates program environment core value after) :
    ValueHasType program value type ∧ BindingMap.Typed program after.heap after.activation after.bindings final ∧
      after.supply.Issued after.activation ∧
      AddressedEnvironment.ConsumptionFrame program final.slots environment after :=
  (elaborated.checked slots).evaluation_soundness checkedProgram store issued evaluated

/-- Finite-call termination remains an optional theorem about the same selected
core, not a restriction on recursive source safety. -/
theorem NamedExpr.Elaborates.correctness {program : Program} {home : Module}
    {names : Module → FunctionName → Option Nat}
    {scope : SourceScope} {before final : FlowContext} {source : NamedExpr} {core : Expr} {type : Ty}
    (elaborated : NamedExpr.Elaborates program names home scope before source core type final)
    (slots : before.slots = scope.context)
    (checkedProgram : program.Checked) (finite : FiniteCalls program core)
    {environment : Environment} (store : BindingMap.Typed program environment.heap environment.activation environment.bindings before)
    (issued : environment.supply.Issued environment.activation) :
    ∃ value after, Evaluates program environment core value after ∧ ValueHasType program value type ∧
      BindingMap.Typed program after.heap after.activation after.bindings final ∧
      after.supply.Issued after.activation ∧ AddressedEnvironment.ConsumptionFrame program final.slots environment after ∧
      ∀ other otherAfter, Evaluates program environment core other otherAfter →
        other = value ∧ otherAfter = after :=
  Grounded.correctness checkedProgram (elaborated.checked slots) finite store issued


end Grounded
