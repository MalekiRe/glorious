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

/-- Rechecking an already selected ordinary input preserves its source identity
and Copy/move choice. The new availability comes from the shared Core framing
proof, not a separately assumed source post-state. -/
theorem NamedExpr.Elaborates.recheck_input {program : Program} {home : Module}
    {names : Module → FunctionName → Option Nat} {scope : SourceScope}
    {before after current final : FlowContext} {source : NamedExpr} {core : Expr} {type : Ty}
    (elaborated : NamedExpr.Elaborates program names home scope before source core type after)
    (ordinary : ∃ place, core = .read place ∨ core = .move place)
    (checked : HasType program home current core type final)
    (slots : current.slots = scope.context) :
    NamedExpr.Elaborates program names home scope current source core type final := by
  obtain ⟨place, rfl | rfl⟩ := ordinary
  · cases elaborated with
    | read resolved _ _ _ _ _ =>
      cases checked with
      | read selected path selection ready copyable =>
        have same := scope.selected_slot resolved slots selected
        exact .read resolved selected (by simpa only [same] using path)
          (by simpa only [same] using selection) ready copyable
  · cases elaborated with
    | readMove resolved _ _ _ _ noncopyable _ _ =>
      cases checked with
      | move selected path selection ready mask context =>
        have same := scope.selected_slot resolved slots selected
        exact .readMove resolved selected (by simpa only [same] using path)
          (by simpa only [same] using selection) ready noncopyable
          (by simpa only [same] using mask) context
    | move resolved _ _ _ _ _ _ =>
      cases checked with
      | move selected path selection ready mask context =>
        have same := scope.selected_slot resolved slots selected
        exact .move resolved selected (by simpa only [same] using path)
          (by simpa only [same] using selection) ready
          (by simpa only [same] using mask) context

/-- Independent ordinary source admissions compose in execution order under
the same pre-state compatibility used by Core. Every pending source admission
is reconstructed after the actual preceding mask update. -/
theorem NamedExprsElaborate.compatible_inputs {program : Program} {home : Module}
    {names : Module → FunctionName → Option Nat} {scope : SourceScope} {before : FlowContext}
    {inputs : List (NamedExpr × Expr × Ty)}
    (slots : before.slots = scope.context)
    (compatible : inputs.Pairwise (fun left right => InputCompatible program home scope.context left.2.1 right.2.1))
    (ordinary : ∀ input ∈ inputs, ∃ place, input.2.1 = .read place ∨ input.2.1 = .move place)
    (admitted : ∀ input ∈ inputs, ∃ after,
      NamedExpr.Elaborates program names home scope before input.1 input.2.1 input.2.2 after) :
    ∃ after, NamedExprsElaborate program names home scope before
      (inputs.map Prod.fst) (inputs.map fun input => input.2.1) (inputs.map fun input => input.2.2) after := by
  induction inputs generalizing before with
  | nil => exact ⟨before, .nil⟩
  | cons first rest ih =>
    obtain ⟨middle, head⟩ := admitted first (by simp)
    have headChecked := head.checked slots
    have currentSlots := headChecked.slots.trans slots
    have parts := List.pairwise_cons.mp compatible
    obtain ⟨final, tail⟩ := ih currentSlots parts.2
      (fun input member => ordinary input (List.mem_cons_of_mem first member)) (by
        intro input member
        obtain ⟨after, pending⟩ := admitted input (List.mem_cons_of_mem first member)
        have compatible := parts.1 input member
        rw [← slots] at compatible
        obtain ⟨next, checked⟩ := compatible.admit_next headChecked (pending.checked slots)
        exact ⟨next, pending.recheck_input (ordinary input (List.mem_cons_of_mem first member)) checked currentSlots⟩)
    exact ⟨final, .cons head tail⟩
/-- Execute the actual ordered source inputs with their original pre-state
observations. Copy overlap is retained; destructive overlap is excluded only
by the shared, mode-sensitive compatibility relation. -/
theorem NamedExprsElaborate.compatible_inputs_execute {program : Program} {home : Module}
    {names : Module → FunctionName → Option Nat} {scope : SourceScope} {before : FlowContext}
    {inputs : List (NamedExpr × Expr × Ty)}
    (slots : before.slots = scope.context)
    (compatible : inputs.Pairwise (fun left right => InputCompatible program home scope.context left.2.1 right.2.1))
    (ordinary : ∀ input ∈ inputs, ∃ place, input.2.1 = .read place ∨ input.2.1 = .move place)
    (admitted : ∀ input ∈ inputs, ∃ after,
      NamedExpr.Elaborates program names home scope before input.1 input.2.1 input.2.2 after)
    {environment : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings before) :
    ∃ final after values,
      NamedExprsElaborate program names home scope before
        (inputs.map Prod.fst) (inputs.map fun input => input.2.1) (inputs.map fun input => input.2.2) final ∧
      EvaluatesMany program environment (inputs.map fun input => input.2.1) values after ∧
      ValuesHaveTypes program values (inputs.map fun input => input.2.2) ∧
      values.map some = inputs.map (fun input => input.2.1.inputObservation program environment) ∧
      BindingMap.Typed program after.heap after.activation after.bindings final ∧
      after.scope = environment.scope ∧ after.supply = environment.supply := by
  obtain ⟨final, elaborated⟩ := NamedExprsElaborate.compatible_inputs slots compatible ordinary admitted
  have coreCompatible : (inputs.map Prod.snd).Pairwise
      (fun left right => InputCompatible program home before.slots left.1 right.1) := by
    simpa only [List.pairwise_map, slots] using compatible
  have coreOrdinary : ∀ input ∈ inputs.map Prod.snd, ∃ place, input.1 = .read place ∨ input.1 = .move place := by
    intro input member
    obtain ⟨source, included, rfl⟩ := List.mem_map.mp member
    exact ordinary source included
  have checked : HasTypes program home before ((inputs.map Prod.snd).map Prod.fst)
      ((inputs.map Prod.snd).map Prod.snd) final := by
    simpa only [List.map_map, Function.comp_def] using elaborated.checked slots
  obtain ⟨after, values, executed, residents, observed, finalTyped, scopeSame, supplySame⟩ :=
    HasTypes.compatible_inputs_execute coreCompatible coreOrdinary checked store
  exact ⟨final, after, values, elaborated,
    by simpa only [List.map_map, Function.comp_def] using executed,
    by simpa only [List.map_map, Function.comp_def] using residents,
    by simpa only [List.map_map, Function.comp_def] using observed,
    finalTyped, scopeSame, supplySame⟩
/-- Ordered ordinary source inputs construct actual callee entry. Parameter
preparation and fresh activation allocation are conclusions; recursive callee
bodies need no termination assumption. -/
theorem NamedExpr.Elaborates.compatible_call_entry {program : Program} {home : Module}
    {names : Module → FunctionName → Option Nat} {scope : SourceScope} {before : FlowContext}
    {inputs : List (NamedExpr × Expr × Ty)} {name : FunctionName} {identity : Nat} {declaration : FunctionDecl}
    (checkedProgram : program.Checked) (slots : before.slots = scope.context)
    (unshadowed : name.Unshadowed scope) (resolved : names home name = some identity)
    (declared : program.functions identity = some declaration)
    (visible : declaration.visibility.Allows declaration.home home)
    (types : inputs.map (fun input => input.2.2) = declaration.parameters.map (fun parameter => parameter.2.type))
    (compatible : inputs.Pairwise (fun left right => InputCompatible program home scope.context left.2.1 right.2.1))
    (ordinary : ∀ input ∈ inputs, ∃ place, input.2.1 = .read place ∨ input.2.1 = .move place)
    (admitted : ∀ input ∈ inputs, ∃ after,
      NamedExpr.Elaborates program names home scope before input.1 input.2.1 input.2.2 after)
    {environment : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings before)
    (issued : environment.supply.Issued environment.activation) :
    ∃ final values middle bindings,
      NamedExpr.Elaborates program names home scope before (.call name (inputs.map Prod.fst))
        (.call identity (inputs.map fun input => input.2.1)) declaration.result final ∧
      EvaluatesMany program environment (inputs.map fun input => input.2.1) values middle ∧
      values.map some = inputs.map (fun input => input.2.1.inputObservation program environment) ∧
      prepareBindings declaration.parameters values = some bindings ∧ BindingInputsTyped program bindings ∧
      Run program ⟨environment, .expression (.call identity (inputs.map fun input => input.2.1)), []⟩
        ⟨enterBindings middle.heap middle.supply bindings, .expression declaration.body, [.restore middle.scope]⟩ ∧
      (∀ state, Run program
        ⟨enterBindings middle.heap middle.supply bindings, .expression declaration.body, [.restore middle.scope]⟩ state →
        ConfigurationTyped program final (.one declaration.result) state ∧
        (Terminal state ∨ ∃ next, Step program state next) ∧
        AddressedEnvironment.ConsumptionFrame program final.slots environment state.outerEnvironment ∧
        (state.environment.bindings.map Prod.fst).Nodup ∧ state.OwnershipSafe program) := by
  obtain ⟨final, middle, values, arguments, executed, residents, observed, _, _, _⟩ :=
    NamedExprsElaborate.compatible_inputs_execute slots compatible ordinary admitted store
  have invocation : NamedExpr.Elaborates program names home scope before (.call name (inputs.map Prod.fst))
      (.call identity (inputs.map fun input => input.2.1)) declaration.result final :=
    .call unshadowed resolved declared visible (by rw [← types]; exact arguments)
  rw [types] at residents
  obtain ⟨bindings, prepared, inputsTyped, _⟩ :=
    prepareBindings.progress residents (checkedProgram.functions _ _ declared).distinct
  have run : Run program ⟨environment, .expression (.call identity (inputs.map fun input => input.2.1)), []⟩
      ⟨enterBindings middle.heap middle.supply bindings, .expression declaration.body, [.restore middle.scope]⟩ :=
    .step (.call declared) ((Run.extend executed [.call declaration]).trans (.step (.callInputs prepared) (.refl _)))
  exact ⟨final, values, middle, bindings, invocation, executed, observed, prepared, inputsTyped, run,
    fun _ continued => (invocation.checked slots).soundness checkedProgram store issued (run.trans continued)⟩
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
    (ready : available.Ready) (finite : FiniteLayout program.target program.data type) :
    ∃ core after, NamedExpr.Elaborates program names home scope before (.read name fields) core type after ∧
      (UsePermitted program.data .copy type → core = .read ⟨binding.identity, fields⟩ ∧ after = before) ∧
      (¬ UsePermitted program.data .copy type → core = .move ⟨binding.identity, fields⟩) := by
  rcases finite.permission_cases .copy with copyable | copyable
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
    ∃ principal core after current value,
      type.HasPrincipal program.data principal ∧
      (∀ requested, type.SatisfiesUse program.data requested ↔ principal.Satisfies requested) ∧
      NamedExpr.Elaborates program names home scope before (.read name fields) core type after ∧
      (principal = .duplicable → core = .read ⟨binding.identity, fields⟩ ∧ after = before) ∧
      (principal ≠ .duplicable → core = .move ⟨binding.identity, fields⟩) ∧
      Step program ⟨environment, .expression core, []⟩ ⟨current, .result value, []⟩ ∧
      ConfigurationTyped program after (.one type) ⟨current, .result value, []⟩ ∧
      ValueHasType program value type ∧
      environment.read program ⟨binding.identity, fields⟩ = some value ∧
      (principal = .duplicable → current = environment) ∧
      (principal ≠ .duplicable →
        environment.take program ⟨binding.identity, fields⟩ = some (value, current) ∧
        current.take program ⟨binding.identity, fields⟩ = none ∧
        ∃ address old next, environment.bindings.resolve ⟨binding.identity, fields⟩ = some address ∧
          environment.heap.read address.root = some old ∧ current.heap.read address.root = some next ∧
          next.activation = old.activation ∧ next.type = old.type ∧
          next.resident.selectFields program next.type address.fields = some .hole ∧
          old.resident.writeFields program old.type address.fields .hole = some next.resident) := by

  have same := scope.selected_slot resolved slots selected
  have physicalPath : PathType program home state.slot.type fields type := by
    rw [same]; exact path
  have physicalSelection : state.initialization.selectFields program state.slot.type fields = some available := by
    rw [same]; exact selection
  obtain ⟨value, observed, resident⟩ :=
    AddressedEnvironment.read.progress (place := ⟨binding.identity, fields⟩)
      store selected physicalPath physicalSelection ready
  obtain ⟨core, after, elaborated, copies, moves⟩ :=
    NamedExpr.Elaborates.ordinary_exists (names := names) resolved selected path selection ready resident.finite
  obtain ⟨principal, classified, _⟩ := Ty.principal_exists resident.finite
  have copying_iff : UsePermitted program.data .copy type ↔ principal = .duplicable := by
    simpa [UsePermission.Allows] using classified .copy
  have copiesByClass := fun chosen => copies (copying_iff.mpr chosen)
  have movesByClass := fun (denied : principal ≠ .duplicable) =>
    moves (fun allowed => denied (copying_iff.mp allowed))
  rcases resident.finite.permission_cases .copy with copying | copying
  · obtain ⟨rfl, rfl⟩ := copies copying
    have stepped : Step program ⟨environment, .expression (.read ⟨binding.identity, fields⟩), []⟩
        ⟨environment, .result value, []⟩ := .read observed
    exact ⟨principal, _, _, _, _, classified, classified.satisfies, elaborated, copiesByClass, movesByClass, stepped,
      (elaborated.soundness slots checkedProgram store issued (.step stepped (.refl _))).1,
      resident, observed, fun _ => rfl, fun denied => False.elim (denied (copying_iff.mp copying))⟩
  · have coreSelected := moves copying
    subst core
    obtain ⟨value, current, _, _, taken, resident, _, _, _, noRetake, _⟩ :=
      AddressedEnvironment.take.progress (place := ⟨binding.identity, fields⟩)
        store selected physicalPath physicalSelection ready
    have stepped : Step program ⟨environment, .expression (.move ⟨binding.identity, fields⟩), []⟩
        ⟨current, .result value, []⟩ := .move taken
    have observed : environment.read program ⟨binding.identity, fields⟩ = some value := by
      obtain ⟨pair, raw, equal⟩ := Option.map_eq_some_iff.mp taken
      cases equal
      exact BindingMap.take.read_before raw
    exact ⟨principal, _, _, _, _, classified, classified.satisfies, elaborated, copiesByClass, movesByClass, stepped,
      (elaborated.soundness slots checkedProgram store issued (.step stepped (.refl _))).1,
      resident, observed, fun allowed => False.elim (copying (copying_iff.mpr allowed)),
      fun _ => ⟨taken, noRetake, AddressedEnvironment.take.hole taken⟩⟩
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
      AddressedEnvironment.ConsumptionFrame program final.slots environment after ∧
      ∀ originalType principal, ValueHasType program value originalType →
        originalType.HasPrincipal program.data principal → type.HasPrincipal program.data principal := by
  obtain ⟨resident, afterTyped, afterIssued, framed⟩ :=
    (elaborated.checked slots).evaluation_soundness checkedProgram store issued evaluated
  exact ⟨resident, afterTyped, afterIssued, framed, fun _ _ original classified =>
    original.principal resident classified⟩

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
