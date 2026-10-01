import Grounded.NamedPatterns

/-! Recursive elaboration of named expressions in the flow-sensitive logical
fragment. Named calls use the source declaration environment; core calls use IDs.
Named patterns and bodies share the same allocated lexical scope. -/
namespace Grounded

/-- Explicit qualification carries a module identity, not authority encoded in
a flattened string. Textual path/import expansion remains a source boundary. -/
inductive FunctionName where
  | unqualified (spelling : String)
  | qualified (owner : Module) (spelling : String)

def FunctionName.owner (caller : Module) : FunctionName → Module
  | .unqualified _ => caller
  | .qualified owner _ => owner

def FunctionName.spelling : FunctionName → String
  | .unqualified spelling | .qualified _ spelling => spelling

def FunctionName.Unshadowed (scope : SourceScope) : FunctionName → Prop
  | .unqualified spelling => scope.resolve spelling = none
  | .qualified _ _ => True

inductive NamedExpr where
  | unit
  | integer (type : IntegerType) (magnitude : Nat)
  | character (number : Nat)
  | group (body : NamedExpr)
  | read (name : String) (fields : List FieldKey)
  | move (name : String) (fields : List FieldKey)
  | sequence (first rest : NamedExpr)
  | bind (mutable : Bool) (name : String) (annotation : Option TypeExpr) (initial body : NamedExpr)
  | tuple (head : NamedExpr) (tail : List NamedExpr)
  | project (body : NamedExpr) (key : FieldKey)
  | array (elements : List NamedExpr)
  | constant (name : String)
  | construct (identity : Nat) (tag : Option Nat) (fields : List NamedExpr)
  | call (name : FunctionName) (arguments : List NamedExpr)
  | assign (name : String) (fields : List FieldKey) (value rest : NamedExpr)
  | applyPatterns (arguments : List NamedExpr) (arms : List (NamedPattern × NamedExpr))

mutual
/-- Name resolution and static availability are composed in evaluation order.
No operational success or successor heap is an admission premise. -/
inductive NamedExpr.Elaborates (program : Program) (names : Module → Module → String → Option Nat) (home : Module) :
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
      (ready : available.Ready) (copyable : Duplicable program.data type) :
      NamedExpr.Elaborates program names home scope context (.read name fields) (.read ⟨binding.identity, fields⟩) type context
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
      (discard : Duplicable program.data discarded)
      (continued : NamedExpr.Elaborates program names home scope middle rest tail type after) :
      NamedExpr.Elaborates program names home scope before (.sequence first rest) (.sequence head tail) type after
  | bind {scope before middle after mutable name annotation initial body first rest localType type finalMask}
      (initialized : NamedExpr.Elaborates program names home scope before initial first localType middle)
      (discard : Duplicable program.data localType)
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
  | project {scope before after source core key parent type index}
      (body : NamedExpr.Elaborates program names home scope before source core parent after)
      (discard : Duplicable program.data parent) (selected : ProjectionType program home parent key index type) :
      NamedExpr.Elaborates program names home scope before (.project source key) (.project core key) type after
  | array {scope before after source core element length}
      (residents : NamedExprsElaborate program names home scope before source core (List.replicate length element) after)
      (finite : FiniteLayout program.target program.data element) (size : length < 2 ^ program.target.pointerBits) :
      NamedExpr.Elaborates program names home scope before (.array source) (.array core) (.array element length) after
  | constant {scope context name type} (checked : HasType program home [] (.constant name) type []) :
      NamedExpr.Elaborates program names home scope context (.constant name) (.constant name) type context
  | construct {scope before after identity tag declaration schema source core}
      (declared : program.data identity = some declaration) (chosen : declaration.constructor tag = some schema)
      (finite : FiniteLayout program.target program.data (.nominal identity))
      (copyable : Duplicable program.data (.nominal identity))
      (visible : declaration.visibility.Allows declaration.home home)
      (access : ∀ field ∈ schema.residents, field.visibility.Allows declaration.home home)
      (residents : NamedExprsElaborate program names home scope before source core (schema.residents.map Field.type) after) :
      NamedExpr.Elaborates program names home scope before (.construct identity tag source) (.construct identity tag core) (.nominal identity) after
  | call {scope before after name identity declaration source core}
      (unshadowed : name.Unshadowed scope)
      (resolved : names home (name.owner home) name.spelling = some identity)
      (declared : program.functions identity = some declaration)
      (visible : declaration.visibility.Allows declaration.home home)
      (inputs : NamedExprsElaborate program names home scope before source core
        (declaration.parameters.map fun parameter => parameter.2.type) after) :
      NamedExpr.Elaborates program names home scope before (.call name source) (.call identity core) declaration.result after
  | assign {scope before evaluated restored after name fields binding type result value rest coreValue coreRest state updated}
      (resolved : scope.resolve name = some binding)
      (resident : NamedExpr.Elaborates program names home scope before value coreValue type evaluated)
      (selected : lookup binding.identity evaluated = some state)
      (path : PathType program home binding.slot.type fields type)
      (writable : binding.slot.mutable = true) (discard : Duplicable program.data type)
      (mask : state.initialization.writeFields program binding.slot.type fields .present = some updated)
      (context : replaceBinding binding.identity { state with initialization := updated } evaluated = some restored)
      (continued : NamedExpr.Elaborates program names home scope restored rest coreRest result after) :
      NamedExpr.Elaborates program names home scope before (.assign name fields value rest)
        (.assign ⟨binding.identity, fields⟩ coreValue coreRest) result after
  | applyPatterns {scope before evaluated after arguments coreArguments inputs arms coreArms result}
      (inputsTyped : NamedExprsElaborate program names home scope before arguments coreArguments inputs evaluated)
      (nonempty : coreArms ≠ []) (covered : Covers program [argumentType inputs] (coreArms.map fun arm => [arm.1]))
      (bodies : NamedArmsElaborate program names home scope evaluated (argumentType inputs) result [] arms coreArms after) :
      NamedExpr.Elaborates program names home scope before (.applyPatterns arguments arms)
        (.applyPatterns inputs coreArguments coreArms) result after
inductive NamedExprsElaborate (program : Program) (names : Module → Module → String → Option Nat) (home : Module) :
    SourceScope → FlowContext → List NamedExpr → List Expr → List Ty → FlowContext → Prop where
  | nil {scope context} : NamedExprsElaborate program names home scope context [] [] [] context
  | cons {scope before middle after head tail first rest type types}
      (initial : NamedExpr.Elaborates program names home scope before head first type middle)
      (continued : NamedExprsElaborate program names home scope middle tail rest types after) :
      NamedExprsElaborate program names home scope before (head :: tail) (first :: rest) (type :: types) after
inductive NamedArmsElaborate (program : Program) (names : Module → Module → String → Option Nat) (home : Module) :
    SourceScope → FlowContext → Ty → Ty → List Pattern → List (NamedPattern × NamedExpr) → List (Pattern × Expr) → FlowContext → Prop where
  | empty {scope before after subject result previous} : NamedArmsElaborate program names home scope before subject result previous [] [] after
  | clause {scope localScope before after subject result previous source pattern bindings localsAfter body coreBody tail coreTail}
      (allocated : NamedPattern.Elaborates program home scope source subject pattern bindings localScope)
      (namesDistinct : source.binders.Nodup) (useful : Useful program subject previous pattern)
      (bodyTyped : NamedExpr.Elaborates program names home localScope (initializedContext bindings ++ before)
        body coreBody result (localsAfter ++ after))
      (localSlots : localsAfter.slots = bindings)
      (tailTyped : NamedArmsElaborate program names home scope before subject result (previous ++ [pattern]) tail coreTail after) :
      NamedArmsElaborate program names home scope before subject result previous ((source, body) :: tail) ((pattern, coreBody) :: coreTail) after
end

/-- Local value bindings hide direct-function names regardless of the expected
result or argument types. Local callable invocation is a separate language
operation; failure to support it must not expose the hidden declaration. -/
theorem NamedExpr.Elaborates.call_not_shadowed {program : Program}
    {names : Module → Module → String → Option Nat} {home : Module} {scope : SourceScope}
    {before after : FlowContext} {name : String} {arguments : List NamedExpr}
    {core : Expr} {type : Ty}
    (elaborated : NamedExpr.Elaborates program names home scope before
      (.call (.unqualified name) arguments) core type after) : scope.resolve name = none := by
  cases elaborated with
  | call unshadowed _ _ _ _ => exact unshadowed

/-- Elaboration preserves the authoritative flow checking judgment. The static
name scope and flow context agree on declarations, not on future readiness. -/
theorem NamedExpr.Elaborates.checked {program : Program} {home : Module} {names : Module → Module → String → Option Nat}
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
  | project _ discard selected ih => exact .project (ih slots) discard selected
  | array _ finite size ih => exact .array (ih slots) finite size
  | constant checked => cases checked with
    | constant declared visible resolved structural initialized => exact .constant declared visible resolved structural initialized
  | construct declared chosen finite copyable visible access _ ih =>
    exact .construct declared chosen finite copyable visible access (ih slots)
  | call _ _ declared visible _ ih => exact .call declared visible (ih slots)
  | assign resolved _ selected path writable discard mask context _ first rest =>
    have resident := first slots
    apply SourceScope.assign_checked resolved slots resident selected path writable discard mask context
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
  | clause allocated _ useful _ localSlots _ body tail =>
    rename_i slots
    apply ArmsType.clause allocated.checked.1 (by rw [slots]; exact allocated.fresh) useful
      (body ?_) localSlots (tail slots)
    rw [allocated.checked.2]
    simp [FlowContext.slots, initializedContext, List.map_append, List.map_map, Function.comp_def, ← slots]

theorem NamedExprsElaborate.checked {program : Program} {home : Module} {names : Module → Module → String → Option Nat}
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
    {names : Module → Module → String → Option Nat}
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
      (state.environment.bindings.map Prod.fst).Nodup :=
  (elaborated.checked slots).soundness checkedProgram store issued run

/-- Completed executions preserve the declared result and caller environment;
termination is not assumed by source admission. -/
theorem NamedExpr.Elaborates.evaluation_soundness {program : Program} {home : Module}
    {names : Module → Module → String → Option Nat}
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
    {names : Module → Module → String → Option Nat}
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
