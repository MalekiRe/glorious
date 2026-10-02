import Grounded.ConfigurationTyping
import Grounded.Termination

/-! General recursive safety consumes exact flow-state checking and current
partial storage. Termination remains a separate optional contract. -/
namespace Grounded

variable {program : Program} {home : Module}

/-- Every actual prefix is safe. Immutable storage may be consumed, but cannot
be replaced; retained callers and lexical storage identities remain protected. -/
theorem HasType.soundness (checkedProgram : program.Checked) {context final : FlowContext}
    {expression : Expr} {type : Ty} (checked : HasType program home context expression type final)
    {environment : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
    (issued : environment.supply.Issued environment.activation) {state : Configuration}
    (run : Run program ⟨environment, .expression expression, []⟩ state) :
    ConfigurationTyped program final (.one type) state ∧
      (Terminal state ∨ ∃ next, Step program state next) ∧
      AddressedEnvironment.ConsumptionFrame program final.slots environment state.outerEnvironment ∧
      (state.environment.bindings.map Prod.fst).Nodup ∧ state.OwnershipSafe program := by
  have entry := ConfigurationTyped.entry checked store issued
  have current := entry.run checkedProgram run
  exact ⟨current, current.progress, entry.consumption_run checkedProgram run, current.bindings_distinct, current.ownership_safe⟩

/-- General checking admits a complete machine behavior, not just a supplied
finite run. Divergence consists of real steps, each preserving the same storage
and ownership contract; the normal alternative carries the actual typed result. -/
theorem HasType.behavior (checkedProgram : program.Checked) {context final : FlowContext}
    {expression : Expr} {type : Ty} (checked : HasType program home context expression type final)
    {environment : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
    (issued : environment.supply.Issued environment.activation) :
    (∃ after value, Evaluates program environment expression value after ∧
      ValueHasType program value type ∧
      BindingMap.Typed program after.heap after.activation after.bindings final ∧
      AddressedEnvironment.ConsumptionFrame program final.slots environment after ∧
      (⟨after, .result value, []⟩ : Configuration).OwnershipSafe program ∧
      Configuration.ExternalFrame ⟨environment, .expression expression, []⟩ ⟨after, .result value, []⟩ ∧
      ∀ identity, environment.heap.next ≤ identity.index → identity.index < after.heap.next →
        after.heap.Retired identity) ∨
    (∃ trace, InfiniteRun program ⟨environment, .expression expression, []⟩ trace ∧
      ∀ index, ConfigurationTyped program final (.one type) (trace index) ∧
        AddressedEnvironment.ConsumptionFrame program final.slots environment (trace index).outerEnvironment ∧
        (trace index).OwnershipSafe program ∧
        Configuration.ExternalFrame ⟨environment, .expression expression, []⟩ (trace index) ∧
        ∀ identity, environment.heap.next ≤ identity.index →
          ∀ cell, (trace index).environment.heap.read identity = some cell →
            ¬ (trace index).Untracked identity) := by
  exact (ConfigurationTyped.entry checked store issued).behavior checkedProgram


/-- Reached scope cleanup constructs its actual retirement and preserved
continuation, then joins retained descendants under their own use classes.
No completed cleanup or future mask realization is assumed. -/
theorem HasType.scope_join_preserves_ownership (checkedProgram : program.Checked)
    {context final : FlowContext} {expression : Expr} {type : Ty}
    (checked : HasType program home context expression type final)
    {environment current : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
    (issued : environment.supply.Issued environment.activation)
    {value : Value} {count : Nat} {stack : List Frame}
    (run : Run program ⟨environment, .expression expression, []⟩
      ⟨current, .result value, .scope count :: stack⟩) :
    ∃ (after : Environment) (branch joined : FlowContext),
      BindingMap.Disposable program current.heap (List.take count current.bindings) ∧
      (BindingMap.releaseOrder (List.take count current.bindings)).Pairwise
        (fun newer older => older.index < newer.index) ∧
      Step program ⟨current, .result value, .scope count :: stack⟩ ⟨after, .result value, stack⟩ ∧
      ConfigurationTyped program final (.one type) ⟨after, .result value, stack⟩ ∧
      (∀ identity ∈ (List.take count current.bindings).map Prod.snd, after.heap.Retired identity) ∧
      BindingMap.Typed program after.heap after.activation after.bindings branch ∧
      BindingMap.Typed program after.heap after.activation after.bindings joined ∧
      BindingContextApprox program.data branch joined ∧
      (∀ address ∈ after.bindings.map Prod.snd, after.heap.read address = current.heap.read address) ∧
      ∀ name state, lookup name branch = some state →
        ∀ selectedHome selectedType fields selectedState,
          PathType program selectedHome state.slot.type fields selectedType →
          state.initialization.selectFields program state.slot.type fields = some selectedState →
          ∃ next nextSelected,
            lookup name joined = some ⟨state.slot, next⟩ ∧
            next.selectFields program state.slot.type fields = some nextSelected ∧
            (¬ UsePermitted program.data .discard selectedType → nextSelected = .maybe → selectedState = .maybe) ∧
            (∀ identity declaration, selectedType = .nominal identity →
              program.data identity = some declaration → declaration.restriction = some .exact →
              (selectedState.Empty ↔ nextSelected.Empty)) := by
  have typed := (checked.soundness checkedProgram store issued run).1
  have original := typed
  cases typed with
  | intro currentStore currentIssued code continuation =>
    cases code with
    | result resident =>
      cases continuation with
      | cons frame tail =>
        cases frame with
        | scope locals discard joined =>
          obtain ⟨after, produced, afterTyped, _, _, _, retired, _, preserved⟩ :=
            AddressedEnvironment.exitScope.progress currentStore locals.length
          have step : Step program ⟨current, .result value, .scope locals.length :: stack⟩
              ⟨after, .result value, stack⟩ := .scope produced
          have branchTyped : BindingMap.Typed program after.heap after.activation after.bindings _ :=
            (by simpa using afterTyped)
          have safe := original.ownership_safe
          refine ⟨after, _, _, safe.1, safe.2, step, original.preservation checkedProgram step, retired,
            branchTyped, branchTyped.approximate joined, joined, preserved, ?_⟩
          intro name state selected selectedHome selectedType fields selectedState path selection
          obtain ⟨next, found, approximation⟩ := joined.lookup selected
          obtain ⟨address, cell, mapped, live, owner, typeEq, cellTyped, member⟩ := branchTyped.lookup selected
          have residentTyped : cell.resident.Typed program state.slot.type state.initialization := by
            simpa only [typeEq] using cellTyped.2
          obtain ⟨nextSelected, selectedAfter, selectedJoined⟩ :=
            path.approximate_initialization residentTyped approximation selection
          refine ⟨next, nextSelected, found, selectedAfter,
            fun required unknown => selectedJoined.no_new_nondiscardable_maybe required unknown, ?_⟩
          intro identity declaration same declared restricted
          subst selectedType
          exact selectedJoined.exact_nominal_consumption declared restricted

/-- Every reached checked assignment can restore its selected place, including
an uncertain one. Its actual module authorizes the write and old-value disposal;
disjoint masks retain their availability. No completed write is assumed. -/
theorem HasType.assignment_restores (checkedProgram : program.Checked)
    {context final : FlowContext} {expression : Expr} {type : Ty}
    (checked : HasType program home context expression type final)
    {environment current : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
    (issued : environment.supply.Issued environment.activation)
    {assignmentHome : Module} {place : Place} {value : Value} {rest : Expr} {stack : List Frame}
    (run : Run program ⟨environment, .expression expression, []⟩
      ⟨current, .result value, .assign assignmentHome place rest :: stack⟩) :
    ∃ after before next state updated assignedType,
      Step program ⟨current, .result value, .assign assignmentHome place rest :: stack⟩
        ⟨after, .expression rest, stack⟩ ∧
      BindingMap.Typed program current.heap current.activation current.bindings before ∧
      lookup place.root before = some state ∧ state.slot.mutable = true ∧
      PathType program assignmentHome state.slot.type place.fields assignedType ∧
      ValueHasType program value assignedType ∧
      BindingMap.ReplacementSafe program assignmentHome current.heap current.bindings place ∧
      state.initialization.writeFields program state.slot.type place.fields .present = some updated ∧
      replaceBinding place.root { state with initialization := updated } before = some next ∧
      BindingMap.Typed program after.heap after.activation after.bindings next ∧
      after.read program place = some value ∧
      updated.selectFields program state.slot.type place.fields = some .present ∧
      (∀ observed, PathDisjoint program assignmentHome state.slot.type place.fields observed →
        updated.selectFields program state.slot.type observed =
          state.initialization.selectFields program state.slot.type observed) := by
  have typed := (checked.soundness checkedProgram store issued run).1
  cases typed with
  | intro currentStore currentIssued code continuation =>
    cases code with
    | result resident =>
      cases continuation with
      | cons frame tail =>
        cases frame with
        | assign selected path writable selection discard mask context restTyped =>
          obtain ⟨actual, updated, next, produced, maskWritten, contextWritten, nextTyped,
            readback, _⟩ := AddressedEnvironment.write.progress currentStore selected path resident
          exact ⟨actual, _, _, _, _, _, .assignResult produced, currentStore, selected, writable, path, resident,
            currentStore.replacement_safe selected path selection discard, maskWritten, contextWritten,
            nextTyped, readback, Initialization.write_select maskWritten,
            fun _ apart => apart.initialization_frame maskWritten⟩


/-- Pre-state observation of an ordinary place input. This uses the same
addressed read as execution; it is not a second storage or alias analysis. -/
def Expr.inputObservation (expression : Expr) (program : Program) (environment : Environment) : Option Value :=
  match expression with
  | .read place | .move place => environment.read program place
  | _ => none

/-- Ordered compatible Copy/move inputs finish with their original pre-state
values. Copy permits overlap; only a preceding move needs separation. -/
theorem HasTypes.compatible_inputs_execute {before final : FlowContext} {inputs : List (Expr × Ty)}
    (compatible : inputs.Pairwise (fun left right => InputCompatible program home before.slots left.1 right.1))
    (ordinary : ∀ input ∈ inputs, ∃ place, input.1 = .read place ∨ input.1 = .move place)
    (checked : HasTypes program home before (inputs.map Prod.fst) (inputs.map Prod.snd) final)
    {environment : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings before) :
    ∃ after values,
      EvaluatesMany program environment (inputs.map Prod.fst) values after ∧
      ValuesHaveTypes program values (inputs.map Prod.snd) ∧
      values.map some = inputs.map (fun input => input.1.inputObservation program environment) ∧
      BindingMap.Typed program after.heap after.activation after.bindings final ∧
      after.scope = environment.scope ∧ after.supply = environment.supply := by
  induction inputs generalizing before final environment with
  | nil =>
    cases checked
    exact ⟨environment, [], .nil, .nil, rfl, store, rfl, rfl⟩
  | cons input rest ih =>
    have parts := List.pairwise_cons.mp compatible
    have tailOrdinary : ∀ input ∈ rest, ∃ place, input.1 = .read place ∨ input.1 = .move place :=
      fun input member => ordinary input (List.mem_cons_of_mem _ member)
    cases input with
    | mk expression type =>
      obtain ⟨place, form⟩ := ordinary (expression, type) (by simp)
      cases checked with
      | cons head tail =>
        have slots := head.slots
        have tailCompatible := parts.2
        rw [← slots] at tailCompatible
        rcases form with rfl | rfl
        · cases head with
          | read selected path selection ready copyable =>
            obtain ⟨value, read, valueTyped⟩ := AddressedEnvironment.read.progress store selected path selection ready
            obtain ⟨after, values, evaluated, valuesTyped, observed, afterTyped, scope, supply⟩ :=
              ih tailCompatible tailOrdinary tail store
            refine ⟨after, value :: values, .cons (.read read) evaluated,
              .cons valueTyped valuesTyped, ?_, afterTyped, scope, supply⟩
            change some value :: values.map some = environment.read program place ::
              rest.map (fun input => input.1.inputObservation program environment)
            rw [read, observed]
        · cases head with
          | move selected path selection ready mask changed =>
            obtain ⟨identity, value, heap, nextState, nextContext, _, maskWritten, contextWritten,
              taken, valueTyped, movedTyped, _⟩ := BindingMap.take.progress store selected path selection ready
            cases Option.some.inj (mask.symm.trans maskWritten)
            cases Option.some.inj (changed.symm.trans contextWritten)
            obtain ⟨after, values, evaluated, valuesTyped, observed, afterTyped, scope, supply⟩ :=
              ih tailCompatible tailOrdinary tail (environment := { environment with heap := heap }) movedTyped
            refine ⟨after, value :: values,
              .cons (.move (by simp [AddressedEnvironment.take, taken])) evaluated,
              .cons valueTyped valuesTyped, ?_, afterTyped, scope, supply⟩
            change some value :: values.map some = environment.read program place ::
              rest.map (fun input => input.1.inputObservation program environment)
            have first : some value = environment.read program place := (BindingMap.take.read_before taken).symm
            rw [← first]
            apply congrArg (List.cons (some value))
            apply observed.trans
            apply List.map_congr_left
            intro pending member
            rcases pending with ⟨expression, type⟩
            have next := parts.1 (expression, type) member
            cases next with
            | moveRead apart => exact BindingMap.take.read_frame store apart taken
            | moveMove apart => exact BindingMap.take.read_frame store apart taken

/-- Pre-state source admission constructs actual compatible-input evaluation and
callee entry, then general preservation types that reached body configuration.
The callee body may recurse or diverge; no completed call is assumed. -/
theorem HasType.compatible_call_entry (checkedProgram : program.Checked)
    {before : FlowContext} {inputs : List (Expr × Ty)} {identity : Nat} {declaration : FunctionDecl}
    (declared : program.functions identity = some declaration)
    (visible : declaration.visibility.Allows declaration.home home)
    (arguments : inputs.map Prod.snd = declaration.parameters.map fun parameter => parameter.2.type)
    (compatible : inputs.Pairwise (fun left right => InputCompatible program home before.slots left.1 right.1))
    (ordinary : ∀ input ∈ inputs, ∃ place, input.1 = .read place ∨ input.1 = .move place)
    (admitted : ∀ input ∈ inputs, ∃ after, HasType program home before input.1 input.2 after)
    {environment : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings before)
    (issued : environment.supply.Issued environment.activation) :
    ∃ final middle values bindings,
      HasType program home before (.call identity (inputs.map Prod.fst))
        declaration.result final ∧
      EvaluatesMany program environment (inputs.map Prod.fst) values middle ∧
      values.map some = inputs.map (fun input => input.1.inputObservation program environment) ∧
      prepareBindings declaration.parameters values = some bindings ∧
      Run program ⟨environment, .expression (.call identity (inputs.map Prod.fst)), []⟩
        ⟨enterBindings middle.heap middle.supply bindings, .expression declaration.body, [.restore middle.scope]⟩ ∧
      ConfigurationTyped program final (.one declaration.result)
        ⟨enterBindings middle.heap middle.supply bindings, .expression declaration.body, [.restore middle.scope]⟩ ∧
      ∃ next, Step program
        ⟨enterBindings middle.heap middle.supply bindings, .expression declaration.body, [.restore middle.scope]⟩ next := by
  obtain ⟨final, inputsChecked⟩ := HasTypes.compatible_inputs compatible admitted
  have checked : HasType program home before (.call identity (inputs.map Prod.fst))
      declaration.result final := .call declared visible (by simpa only [arguments] using inputsChecked)
  obtain ⟨middle, values, evaluated, valuesTyped, observed, _⟩ :=
    HasTypes.compatible_inputs_execute compatible ordinary inputsChecked store
  obtain ⟨bindings, prepared, _, _⟩ := prepareBindings.progress
    (by simpa only [arguments] using valuesTyped) (checkedProgram.functions identity declaration declared).distinct
  have entered : Run program
      ⟨environment, .expression (.call identity (inputs.map Prod.fst)), []⟩
      ⟨enterBindings middle.heap middle.supply bindings, .expression declaration.body, [.restore middle.scope]⟩ :=
    .step (.call declared) ((Run.extend evaluated [.call declaration]).trans
      (.step (.callInputs prepared) (.refl _)))
  have safe := checked.soundness checkedProgram store issued entered
  refine ⟨final, middle, values, bindings, checked, evaluated, observed, prepared, entered, safe.1, ?_⟩
  rcases safe.2.1 with terminal | next
  · cases terminal
  · exact next



/-- Pre-state-compatible owned arguments yield general call-prefix safety,
including actual argument movement, callee entry, recursive execution and return.
No intermediate input readiness or completed execution is assumed. -/
theorem HasType.disjoint_call_soundness (checkedProgram : program.Checked)
    {before : FlowContext} {inputs : List (Place × Ty)} {identity : Nat} {declaration : FunctionDecl}
    (declared : program.functions identity = some declaration)
    (visible : declaration.visibility.Allows declaration.home home)
    (arguments : inputs.map Prod.snd = declaration.parameters.map fun parameter => parameter.2.type)
    (separated : inputs.Pairwise (fun left right => PlaceDisjoint program home before.slots left.1 right.1))
    (ready : ∀ input ∈ inputs, ∃ state available,
      lookup input.1.root before = some state ∧
      PathType program home state.slot.type input.1.fields input.2 ∧
      state.initialization.selectFields program state.slot.type input.1.fields = some available ∧ available.Ready) :
    ∃ final, HasType program home before (.call identity (inputs.map fun input => Expr.move input.1))
        declaration.result final ∧
      ∀ (environment : Environment) (state : Configuration),
        BindingMap.Typed program environment.heap environment.activation environment.bindings before →
        environment.supply.Issued environment.activation →
        Run program ⟨environment, .expression (.call identity (inputs.map fun input => Expr.move input.1)), []⟩ state →
        ConfigurationTyped program final (.one declaration.result) state ∧
        (Terminal state ∨ ∃ next, Step program state next) ∧
        AddressedEnvironment.ConsumptionFrame program final.slots environment state.outerEnvironment ∧
        (state.environment.bindings.map Prod.fst).Nodup ∧ state.OwnershipSafe program := by
  obtain ⟨final, checked⟩ := HasType.call_disjoint_moves declared visible arguments separated ready
  exact ⟨final, checked, fun _ _ store issued run => checked.soundness checkedProgram store issued run⟩

/-- Pre-state-compatible mixed Copy/move inputs yield general call-prefix safety,
including actual argument movement, callee entry, recursive execution and return.
No intermediate input readiness or completed execution is assumed. -/
theorem HasType.compatible_call_soundness (checkedProgram : program.Checked)
    {before : FlowContext} {inputs : List (Expr × Ty)} {identity : Nat} {declaration : FunctionDecl}
    (declared : program.functions identity = some declaration)
    (visible : declaration.visibility.Allows declaration.home home)
    (arguments : inputs.map Prod.snd = declaration.parameters.map fun parameter => parameter.2.type)
    (compatible : inputs.Pairwise (fun left right => InputCompatible program home before.slots left.1 right.1))
    (admitted : ∀ input ∈ inputs, ∃ after, HasType program home before input.1 input.2 after) :
    ∃ final, HasType program home before (.call identity (inputs.map Prod.fst))
        declaration.result final ∧
      ∀ (environment : Environment) (state : Configuration),
        BindingMap.Typed program environment.heap environment.activation environment.bindings before →
        environment.supply.Issued environment.activation →
        Run program ⟨environment, .expression (.call identity (inputs.map Prod.fst)), []⟩ state →
        ConfigurationTyped program final (.one declaration.result) state ∧
        (Terminal state ∨ ∃ next, Step program state next) ∧
        AddressedEnvironment.ConsumptionFrame program final.slots environment state.outerEnvironment ∧
        (state.environment.bindings.map Prod.fst).Nodup ∧ state.OwnershipSafe program := by
  obtain ⟨final, checked⟩ := HasType.call_compatible_inputs declared visible arguments compatible admitted
  exact ⟨final, checked, fun _ _ store issued run => checked.soundness checkedProgram store issued run⟩

/-- Actual argument execution realizes the ordered checking output, even when
static call expansion is infinite. Completion is observed, not admitted. -/
theorem HasTypes.evaluation_soundness (checkedProgram : program.Checked)
    {context final : FlowContext} {expressions : List Expr} {types : List Ty}
    (checked : HasTypes program home context expressions types final)
    {environment after : Environment} {values : List Value}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
    (issued : environment.supply.Issued environment.activation)
    (evaluated : EvaluatesMany program environment expressions values after) :
    ValuesHaveTypes program values types ∧
      BindingMap.Typed program after.heap after.activation after.bindings final ∧
      after.supply.Issued after.activation ∧
      AddressedEnvironment.ConsumptionFrame program final.slots environment after := by
  have entry : ConfigurationTyped program final (.many types)
      ⟨environment, .arguments expressions, []⟩ :=
    .intro store issued (.arguments checked) .nil
  have current := entry.run checkedProgram evaluated
  have framed := entry.consumption_run checkedProgram evaluated
  cases current with
  | intro residents afterIssued code continuation =>
    cases continuation
    cases code with
    | results residentsTyped => exact ⟨residentsTyped, residents, afterIssued, framed⟩


/-- Argument termination reaches actual fresh callee entry even when the callee
itself is recursive. Allocation, preparation and the entered state are results. -/
theorem HasType.call_entry (checkedProgram : program.Checked)
    {before final : FlowContext} {identity : Nat} {arguments : List Expr} {type : Ty}
    (checked : HasType program home before (.call identity arguments) type final)
    (finite : ∀ argument ∈ arguments, FiniteCalls program argument) {environment : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings before)
    (issued : environment.supply.Issued environment.activation) :
    ∃ declaration values middle bindings,
      program.functions identity = some declaration ∧
      EvaluatesMany program environment arguments values middle ∧
      prepareBindings declaration.parameters values = some bindings ∧ BindingInputsTyped program bindings ∧
      Run program ⟨environment, .expression (.call identity arguments), []⟩
        ⟨enterBindings middle.heap middle.supply bindings, .expression declaration.body, [.restore middle.scope]⟩ ∧
      ConfigurationTyped program final (.one type)
        ⟨enterBindings middle.heap middle.supply bindings, .expression declaration.body, [.restore middle.scope]⟩ ∧
      (∃ next, Step program
        ⟨enterBindings middle.heap middle.supply bindings, .expression declaration.body, [.restore middle.scope]⟩ next) ∧
      AddressedEnvironment.ConsumptionFrame program final.slots environment
        (⟨enterBindings middle.heap middle.supply bindings, .expression declaration.body,
          [.restore middle.scope]⟩ : Configuration).outerEnvironment ∧
      ((enterBindings middle.heap middle.supply bindings).bindings.map Prod.fst).Nodup ∧
      (⟨enterBindings middle.heap middle.supply bindings, .expression declaration.body,
        [.restore middle.scope]⟩ : Configuration).OwnershipSafe program := by
  cases checked with
  | @call home before final identity arguments declaration declared visible inputs =>
    obtain ⟨values, middle, inputRun, residents, middleTyped, middleIssued⟩ :=
      inputs.executes checkedProgram finite store issued
    obtain ⟨bindings, prepared, inputsTyped, slots⟩ :=
      prepareBindings.progress residents (checkedProgram.functions _ _ declared).distinct
    have run : Run program ⟨environment, .expression (.call identity arguments), []⟩
        ⟨enterBindings middle.heap middle.supply bindings, .expression declaration.body, [.restore middle.scope]⟩ :=
      .step (.call declared) ((Run.extend inputRun [.call declaration]).trans
        (.step (.callInputs prepared) (.refl _)))
    have source : HasType program home before (.call identity arguments) declaration.result final :=
      .call declared visible inputs
    have safety := source.soundness checkedProgram store issued run
    have progress : ∃ next, Step program
        ⟨enterBindings middle.heap middle.supply bindings, .expression declaration.body, [.restore middle.scope]⟩ next := by
      rcases safety.2.1 with terminal | next
      · cases terminal
      · exact next
    exact ⟨declaration, values, middle, bindings, declared, inputRun, prepared, inputsTyped,
      run, safety.1, progress, safety.2.2⟩

/-- Mixed direct place inputs construct a safe callee entry from pre-state
admission alone. Read/move syntax proves argument termination; the body may diverge. -/
theorem HasType.compatible_access_entry (checkedProgram : program.Checked)
    {before : FlowContext} {inputs : List (Expr × Ty)} {identity : Nat} {declaration : FunctionDecl}
    (declared : program.functions identity = some declaration)
    (visible : declaration.visibility.Allows declaration.home home)
    (arguments : inputs.map Prod.snd = declaration.parameters.map fun parameter => parameter.2.type)
    (compatible : inputs.Pairwise (fun left right => InputCompatible program home before.slots left.1 right.1))
    (admitted : ∀ input ∈ inputs, ∃ after, HasType program home before input.1 input.2 after)
    (accesses : ∀ input ∈ inputs, ∃ place, input.1 = .read place ∨ input.1 = .move place)
    {environment : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings before)
    (issued : environment.supply.Issued environment.activation) :
    ∃ final values middle bindings,
      HasType program home before (.call identity (inputs.map Prod.fst)) declaration.result final ∧
      EvaluatesMany program environment (inputs.map Prod.fst) values middle ∧
      prepareBindings declaration.parameters values = some bindings ∧ BindingInputsTyped program bindings ∧
      Run program ⟨environment, .expression (.call identity (inputs.map Prod.fst)), []⟩
        ⟨enterBindings middle.heap middle.supply bindings, .expression declaration.body, [.restore middle.scope]⟩ ∧
      ConfigurationTyped program final (.one declaration.result)
        ⟨enterBindings middle.heap middle.supply bindings, .expression declaration.body, [.restore middle.scope]⟩ ∧
      (∃ next, Step program
        ⟨enterBindings middle.heap middle.supply bindings, .expression declaration.body, [.restore middle.scope]⟩ next) ∧
      AddressedEnvironment.ConsumptionFrame program final.slots environment
        (⟨enterBindings middle.heap middle.supply bindings, .expression declaration.body,
          [.restore middle.scope]⟩ : Configuration).outerEnvironment ∧
      ((enterBindings middle.heap middle.supply bindings).bindings.map Prod.fst).Nodup ∧
      (⟨enterBindings middle.heap middle.supply bindings, .expression declaration.body,
        [.restore middle.scope]⟩ : Configuration).OwnershipSafe program := by
  obtain ⟨final, checked⟩ := HasType.call_compatible_inputs declared visible arguments compatible admitted
  have finite : ∀ argument ∈ inputs.map Prod.fst, FiniteCalls program argument := by
    intro argument member
    obtain ⟨input, inputMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨place, copy | move⟩ := accesses input inputMember
    · rw [copy]; exact FiniteCalls.read place
    · rw [move]; exact FiniteCalls.move place
  obtain ⟨actual, values, middle, bindings, found, inputRun, prepared, inputsTyped, run, safe⟩ :=
    checked.call_entry checkedProgram finite store issued
  have same := Option.some.inj (found.symm.trans declared)
  subst actual
  exact ⟨final, values, middle, bindings, checked, inputRun, prepared, inputsTyped, run, safe⟩





/-- No checked execution can duplicate a value whose principal forbids Copy.
The claim is about the actual read transition, not merely a source annotation. -/
theorem HasType.no_noncopyable_read (checkedProgram : program.Checked)
    {context final : FlowContext} {expression : Expr} {type : Ty}
    (checked : HasType program home context expression type final)
    {environment current : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
    (issued : environment.supply.Issued environment.activation)
    {place : Place} {stack : List Frame} {owner : Value} {ownerType : Ty}
    (run : Run program ⟨environment, .expression expression, []⟩
      ⟨current, .expression (.read place), stack⟩)
    (step : Step program ⟨current, .expression (.read place), stack⟩
      ⟨current, .result owner, stack⟩)
    (resident : ValueHasType program owner ownerType)
    (required : ¬ UsePermitted program.data .copy ownerType) : False := by
  have permission := (checked.soundness checkedProgram store issued run).2.2.2.2
  cases step with
  | read selected => exact required (BindingMap.CopySafe.read_permission permission selected resident)


/-- Direct disposal cannot erase any nondiscardable principal, including one
inherited through aggregates or inactive nominal variants. -/
theorem HasType.no_nondiscardable_discard (checkedProgram : program.Checked)
    {context final : FlowContext} {expression : Expr} {type : Ty}
    (checked : HasType program home context expression type final)
    {environment current : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
    (issued : environment.supply.Issued environment.activation)
    {owner : Value} {ownerType : Ty} {rest : Expr} {stack : List Frame}
    (resident : ValueHasType program owner ownerType)
    (required : ¬ UsePermitted program.data .discard ownerType)
    (run : Run program ⟨environment, .expression expression, []⟩
      ⟨current, .result owner, .sequence rest :: stack⟩) : False := by
  obtain ⟨type, permission⟩ := (checked.soundness checkedProgram store issued run).2.2.2.2
  exact required (permission.read_permission_as (by simp [PartialValue.read]) resident)


/-- No checked execution prefix reaches a direct discard of a live exact
nominal owner. This includes empty nominal payloads, not just inhabited fields. -/
theorem HasType.no_exact_discard (checkedProgram : program.Checked)
    {context final : FlowContext} {expression : Expr} {type : Ty}
    (checked : HasType program home context expression type final)
    {environment current : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
    (issued : environment.supply.Issued environment.activation)
    {identity : Nat} {declaration : DataDecl} {tag : Option Nat} {fields : List Value}
    (declared : program.data identity = some declaration)
    (restricted : declaration.restriction = some .exact) {rest : Expr} {stack : List Frame}
    (run : Run program ⟨environment, .expression expression, []⟩
      ⟨current, .result (.nominal identity tag fields), .sequence rest :: stack⟩) : False := by
  obtain ⟨type, permission⟩ := (checked.soundness checkedProgram store issued run).2.2.2.2
  exact PartialValue.Disposable.not_exact_read (tag := tag) (fields := fields)
    declared restricted (by simp [PartialValue.read]) permission

/-- Actual lexical retirement preserves every cell with a live nondiscardable
descendant, without requiring the containing aggregate to remain readable. -/
theorem HasType.scope_preserves_nondiscardable (checkedProgram : program.Checked)
    {context final : FlowContext} {expression : Expr} {type : Ty}
    (checked : HasType program home context expression type final)
    {environment current : Environment} {after : Configuration}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
    (issued : environment.supply.Issued environment.activation)
    {value : Value} {count : Nat} {stack : List Frame}
    (run : Run program ⟨environment, .expression expression, []⟩
      ⟨current, .result value, .scope count :: stack⟩)
    (step : Step program ⟨current, .result value, .scope count :: stack⟩ after)
    {address : StorageId} {cell : StorageCell} (found : current.heap.read address = some cell)
    {selectedHome : Module} {selectedType : Ty} {fields : List FieldKey}
    (path : PathType program selectedHome cell.type fields selectedType)
    {owner : Value}
    (resident : ((cell.resident.selectFields program cell.type fields).bind PartialValue.read) = some owner)
    (required : ¬ UsePermitted program.data .discard selectedType) :
    after.environment.heap.read address = some cell := by
  have disposition := (checked.soundness checkedProgram store issued run).2.2.2.2
  cases step with
  | scope retired =>
    simp only [AddressedEnvironment.exitScope, Option.map_eq_some_iff] at retired
    obtain ⟨heap, released, same⟩ := retired
    subst_vars
    exact BindingMap.Disposable.release_preserves_nondiscardable disposition.1 released found path resident required

/-- Actual caller restoration preserves live nondiscardable descendants,
including those retained inside partially consumed aggregates. -/
theorem HasType.restore_preserves_nondiscardable (checkedProgram : program.Checked)
    {context final : FlowContext} {expression : Expr} {type : Ty}
    (checked : HasType program home context expression type final)
    {environment current : Environment} {after : Configuration}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
    (issued : environment.supply.Issued environment.activation)
    {value : Value} {caller : AddressedScope} {stack : List Frame}
    (run : Run program ⟨environment, .expression expression, []⟩
      ⟨current, .result value, .restore caller :: stack⟩)
    (step : Step program ⟨current, .result value, .restore caller :: stack⟩ after)
    {address : StorageId} {cell : StorageCell} (found : current.heap.read address = some cell)
    {selectedHome : Module} {selectedType : Ty} {fields : List FieldKey}
    (path : PathType program selectedHome cell.type fields selectedType)
    {owner : Value}
    (resident : ((cell.resident.selectFields program cell.type fields).bind PartialValue.read) = some owner)
    (required : ¬ UsePermitted program.data .discard selectedType) :
    after.environment.heap.read address = some cell := by
  have disposition := (checked.soundness checkedProgram store issued run).2.2.2.2
  cases step with
  | restore retired =>
    simp only [AddressedEnvironment.restore, Option.map_eq_some_iff] at retired
    obtain ⟨heap, released, same⟩ := retired
    subst_vars
    exact BindingMap.Disposable.release_preserves_nondiscardable disposition.1 released found path resident required


/-- An actual lexical retirement after a checked prefix cannot retire or alter a
live exact nominal owner in the heap. -/
theorem HasType.scope_preserves_exact (checkedProgram : program.Checked)
    {context final : FlowContext} {expression : Expr} {type : Ty}
    (checked : HasType program home context expression type final)
    {environment current : Environment} {after : Configuration}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
    (issued : environment.supply.Issued environment.activation)
    {value : Value} {count : Nat} {stack : List Frame}
    (run : Run program ⟨environment, .expression expression, []⟩
      ⟨current, .result value, .scope count :: stack⟩)
    (step : Step program ⟨current, .result value, .scope count :: stack⟩ after)
    {address : StorageId} {cell : StorageCell} (found : current.heap.read address = some cell)
    {identity : Nat} {declaration : DataDecl} {tag : Option Nat} {fields : List Value}
    (declared : program.data identity = some declaration) (restricted : declaration.restriction = some .exact)
    (resident : cell.resident.read = some (.nominal identity tag fields)) :
    after.environment.heap.read address = some cell := by
  have disposition := (checked.soundness checkedProgram store issued run).2.2.2.2
  cases step with
  | scope exited =>
    simp only [AddressedEnvironment.exitScope, Option.map_eq_some_iff] at exited
    obtain ⟨heap, released, same⟩ := exited
    subst_vars
    exact BindingMap.Disposable.release_preserves_exact disposition.1 released found declared restricted resident

/-- An actual caller restoration after a checked prefix cannot retire or alter a
live exact nominal owner in the heap. -/
theorem HasType.restore_preserves_exact (checkedProgram : program.Checked)
    {context final : FlowContext} {expression : Expr} {type : Ty}
    (checked : HasType program home context expression type final)
    {environment current : Environment} {after : Configuration}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
    (issued : environment.supply.Issued environment.activation)
    {value : Value} {caller : AddressedScope} {stack : List Frame}
    (run : Run program ⟨environment, .expression expression, []⟩
      ⟨current, .result value, .restore caller :: stack⟩)
    (step : Step program ⟨current, .result value, .restore caller :: stack⟩ after)
    {address : StorageId} {cell : StorageCell} (found : current.heap.read address = some cell)
    {identity : Nat} {declaration : DataDecl} {tag : Option Nat} {fields : List Value}
    (declared : program.data identity = some declaration) (restricted : declaration.restriction = some .exact)
    (resident : cell.resident.read = some (.nominal identity tag fields)) :
    after.environment.heap.read address = some cell := by
  have disposition := (checked.soundness checkedProgram store issued run).2.2.2.2
  cases step with
  | restore restored =>
    simp only [AddressedEnvironment.restore, Option.map_eq_some_iff] at restored
    obtain ⟨heap, released, same⟩ := restored
    subst_vars
    exact BindingMap.Disposable.release_preserves_exact disposition.1 released found declared restricted resident

/-- Selection is observed after RHS evaluation. A moved-out slot may be restored,
but a still-live exact selected owner cannot be overwritten. -/
theorem HasType.no_exact_overwrite (checkedProgram : program.Checked)
    {context final : FlowContext} {expression : Expr} {type : Ty}
    (checked : HasType program home context expression type final)
    {environment current : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
    (issued : environment.supply.Issued environment.activation)
    {assignmentHome : Module} {value : Value} {place : Place} {rest : Expr} {stack : List Frame}
    (run : Run program ⟨environment, .expression expression, []⟩
      ⟨current, .result value, .assign assignmentHome place rest :: stack⟩)
    {address : StorageId} {cell : StorageCell}
    (mapped : lookup place.root current.bindings = some address) (found : current.heap.read address = some cell)
    {identity : Nat} {declaration : DataDecl} {tag : Option Nat} {fields : List Value}
    (declared : program.data identity = some declaration) (restricted : declaration.restriction = some .exact)
    (selected : ((cell.resident.selectFields program cell.type place.fields).bind PartialValue.read) =
      some (.nominal identity tag fields)) : False := by
  exact BindingMap.ReplacementSafe.not_exact
    (checked.soundness checkedProgram store issued run).2.2.2.2 mapped found declared restricted selected


/-- After RHS evaluation, no checked prefix overwrites an ancestor of a live
nondiscardable owner, even if the old destination cannot itself be read. -/
theorem HasType.no_nondiscardable_overwrite (checkedProgram : program.Checked)
    {context final : FlowContext} {expression : Expr} {type : Ty}
    (checked : HasType program home context expression type final)
    {environment current : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
    (issued : environment.supply.Issued environment.activation)
    {assignmentHome : Module} {value : Value} {place : Place} {rest : Expr} {stack : List Frame}
    (run : Run program ⟨environment, .expression expression, []⟩
      ⟨current, .result value, .assign assignmentHome place rest :: stack⟩)
    {address : StorageId} {cell : StorageCell} {selectedHome : Module} {selectedType : Ty}
    (mapped : lookup place.root current.bindings = some address) (found : current.heap.read address = some cell)
    (path : PathType program selectedHome cell.type place.fields selectedType)
    {descendantHome : Module} {descendantType : Ty} {fields : List FieldKey}
    (descendant : PathType program descendantHome selectedType fields descendantType)
    {owner : Value}
    (selected : ((cell.resident.selectFields program cell.type place.fields).bind fun old =>
      (old.selectFields program selectedType fields).bind PartialValue.read) = some owner)
    (required : ¬ UsePermitted program.data .discard descendantType) : False := by
  exact BindingMap.ReplacementSafe.not_nondiscardable
    (checked.soundness checkedProgram store issued run).2.2.2.2 mapped found path descendant selected required


/-- Completed execution realizes exactly the declared output masks. No completed
run or future readiness is a premise of checking or progress. -/
theorem HasType.evaluation_soundness (checkedProgram : program.Checked)
    {context final : FlowContext} {expression : Expr} {type : Ty}
    (checked : HasType program home context expression type final)
    {environment after : Environment} {value : Value}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
    (issued : environment.supply.Issued environment.activation)
    (evaluated : Evaluates program environment expression value after) :
    ValueHasType program value type ∧
      BindingMap.Typed program after.heap after.activation after.bindings final ∧
      after.supply.Issued after.activation ∧
      AddressedEnvironment.ConsumptionFrame program final.slots environment after := by
  have entry := ConfigurationTyped.entry checked store issued
  have current := entry.run checkedProgram evaluated
  have framed := entry.consumption_run checkedProgram evaluated
  cases current with
  | intro residents afterIssued code continuation =>
    cases continuation
    cases code with
    | result resident => exact ⟨resident, residents, afterIssued, framed⟩

/-- Completed admitted calls expose their actual argument/body/restoration
phases and every left-to-right argument cut, with checked parameter values and
post-state safety. No static call-expansion or body-termination certificate is
needed: the supplied completed run is decomposed, not postulated by admission. -/
theorem HasType.call_evaluation_soundness (checkedProgram : program.Checked)
    {context final : FlowContext} {identity : Nat} {arguments : List Expr} {type : Ty}
    (checked : HasType program home context (.call identity arguments) type final)
    {environment after : Environment} {value : Value}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
    (issued : environment.supply.Issued environment.activation)
    (evaluated : Evaluates program environment (.call identity arguments) value after) :
    ∃ declaration values middle bindings localAfter,
      program.functions identity = some declaration ∧ type = declaration.result ∧
      EvaluatesMany program environment arguments values middle ∧
      ValuesHaveTypes program values (declaration.parameters.map fun parameter => parameter.2.type) ∧
      BindingMap.Typed program middle.heap middle.activation middle.bindings final ∧
      middle.supply.Issued middle.activation ∧
      AddressedEnvironment.ConsumptionFrame program final.slots environment middle ∧
      prepareBindings declaration.parameters values = some bindings ∧ BindingInputsTyped program bindings ∧
      Evaluates program (enterBindings middle.heap middle.supply bindings) declaration.body value localAfter ∧
      localAfter.restore middle.scope = some after ∧
      ValueHasType program value type ∧
      BindingMap.Typed program after.heap after.activation after.bindings final ∧
      after.supply.Issued after.activation ∧
      AddressedEnvironment.ConsumptionFrame program final.slots environment after ∧
      ∀ front back, arguments = front ++ back →
        ∃ first rest next, values = first ++ rest ∧
          EvaluatesMany program environment front first next ∧
          EvaluatesMany program next back rest middle := by
  obtain ⟨declaration, values, middle, bindings, localAfter, declared, inputRun, prepared, bodyRun, restored⟩ :=
    Evaluates.call_iff.mp evaluated
  have ⟨result, _, inputs⟩ := checked.call_signature declared
  have ⟨residents, middleTyped, middleIssued, middleFramed⟩ :=
    inputs.evaluation_soundness checkedProgram store issued inputRun
  obtain ⟨actual, produced, typed, _⟩ :=
    prepareBindings.progress residents (checkedProgram.functions _ _ declared).distinct
  cases Option.some.inj (prepared.symm.trans produced)
  have ⟨resident, afterTyped, afterIssued, framed⟩ := checked.evaluation_soundness checkedProgram store issued evaluated
  refine ⟨declaration, values, middle, bindings, localAfter, declared, result, inputRun, residents,
    middleTyped, middleIssued, middleFramed, prepared, typed, bodyRun, restored,
    resident, afterTyped, afterIssued, framed, ?_⟩
  intro front back same
  exact EvaluatesMany.append_iff.mp (same ▸ inputRun)


/-- Finite-call correctness constructs execution and proves its unique result,
exact post-state and consumption-only immutable frame. -/
theorem correctness (checkedProgram : program.Checked) {context final : FlowContext}
    {expression : Expr} {type : Ty} (admitted : HasType program home context expression type final)
    (finite : FiniteCalls program expression) {environment : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
    (issued : environment.supply.Issued environment.activation) :
    ∃ value after, Evaluates program environment expression value after ∧ ValueHasType program value type ∧
      BindingMap.Typed program after.heap after.activation after.bindings final ∧
      after.supply.Issued after.activation ∧
      AddressedEnvironment.ConsumptionFrame program final.slots environment after ∧
      ∀ other otherAfter, Evaluates program environment expression other otherAfter → other = value ∧ otherAfter = after := by
  obtain ⟨value, after, run, valueTyped, afterTyped, afterIssued, _⟩ := admitted.executes checkedProgram finite store issued
  exact ⟨value, after, run, valueTyped, afterTyped, afterIssued,
    (admitted.soundness checkedProgram store issued run).2.2.1, fun _ _ other => run.unique other⟩

theorem AddressedEnvironment.empty_typed :
    BindingMap.Typed program AddressedEnvironment.empty.heap AddressedEnvironment.empty.activation
      AddressedEnvironment.empty.bindings [] := .nil

theorem AddressedEnvironment.empty_issued :
    AddressedEnvironment.empty.supply.Issued AddressedEnvironment.empty.activation := Nat.zero_lt_succ 0

theorem closed_correctness (checkedProgram : program.Checked) {expression : Expr} {type : Ty}
    (admitted : HasType program home [] expression type []) (finite : FiniteCalls program expression) :
    ∃ value after, Evaluates program AddressedEnvironment.empty expression value after ∧ ValueHasType program value type ∧
      BindingMap.Typed program after.heap after.activation after.bindings [] ∧
      after.supply.Issued after.activation ∧
      AddressedEnvironment.ConsumptionFrame program [] AddressedEnvironment.empty after ∧
      ∀ other otherAfter, Evaluates program AddressedEnvironment.empty expression other otherAfter →
        other = value ∧ otherAfter = after :=
  correctness checkedProgram admitted finite AddressedEnvironment.empty_typed AddressedEnvironment.empty_issued

/-- Exact scalar admission, independent of incoming availability. -/
theorem integer_admission (context : FlowContext) (type : IntegerType) (magnitude : Nat) :
    (∃ result after, HasType program home context (.integer type magnitude) result after) ↔
      type.Contains program.target magnitude := by
  constructor
  · rintro ⟨_, _, admitted⟩
    cases admitted with | integer fits => exact fits
  · intro fits
    exact ⟨_, _, .integer fits⟩

theorem character_admission (context : FlowContext) (number : Nat) :
    (∃ result after, HasType program home context (.character number) result after) ↔ UnicodeScalar number := by
  constructor
  · rintro ⟨_, _, admitted⟩
    cases admitted with | character valid => exact valid
  · intro valid
    exact ⟨_, _, .character valid⟩

/-- The original unit subset retains its admission and evaluation meaning. -/
theorem unit_agreement : HasType program home [] .unit .unit [] ∧
    ∀ value, Evaluates program AddressedEnvironment.empty .unit value AddressedEnvironment.empty ↔ value = .unit := by
  refine ⟨.unit, fun value => ⟨?_, ?_⟩⟩
  · intro evaluation
    exact (Evaluates.unique Evaluates.unit evaluation).1
  · intro equal
    subst value
    exact .unit

/-- Every reached wildcard or constant-pattern disposal, including an arbitrary
nested subtree, has that resident's actual zero-use permission. -/
theorem HasType.pattern_discard_permission (checkedProgram : program.Checked)
    {context final : FlowContext} {expression : Expr} {type : Ty}
    (checked : HasType program home context expression type final)
    {environment current : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
    (issued : environment.supply.Issued environment.activation)
    {patternHome : Module} {values : List Value} {stack : List Frame} {front back : List (Pattern × Expr)}
    {pattern discarded : Pattern} {owner : Value} {body : Expr} {bindings : List BindingInput} {subjectType : Ty}
    (run : Run program ⟨environment, .expression expression, []⟩
      ⟨current, .results values, .patterns patternHome (front ++ (pattern, body) :: back) :: stack⟩)
    (missed : ∀ earlier ∈ front, earlier.1.matchValue (argumentValue values) = none)
    (matched : pattern.matchValue (argumentValue values) = some bindings)
    (focus : Pattern.SubjectAt pattern (argumentValue values) discarded owner)
    (discards : discarded = .wildcard ∨ ∃ annotation expected, discarded = .literal annotation expected)
    (resident : ValueHasType program owner subjectType) :
    UsePermitted program.data .discard subjectType ∧ discarded.matchValue owner = some [] := by
  have safe := (checked.soundness checkedProgram store issued run).2.2.2.2
  obtain ⟨subject, locals, actual, patternTyped⟩ := safe.selected_pattern missed matched
  obtain ⟨childType, childBindings, childResident, childPattern⟩ := PatternType.subject_at focus patternTyped actual
  obtain ⟨inputs, _, _, childMatch, _⟩ := focus.matched matched
  constructor
  · apply childResident.use_permission resident
    rcases discards with rfl | ⟨annotation, expected, rfl⟩
    · cases childPattern with | wildcard permission => exact permission
    · cases childPattern with | literal typed permission => exact permission
  · rcases discards with rfl | ⟨annotation, expected, rfl⟩
    · simp only [Pattern.matchValue]
    · simp only [Pattern.matchValue] at childMatch ⊢
      split at childMatch <;> simp_all

/-- An arbitrary nested binder in the first selected clause transfers its exact
resident into fresh storage through the real pattern-entry transition. The
position is derived from the matcher's ordered output, not supplied as readiness. -/
theorem HasType.pattern_binding (checkedProgram : program.Checked)
    {context final : FlowContext} {expression : Expr} {type : Ty}
    (checked : HasType program home context expression type final)
    {environment current : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
    (issued : environment.supply.Issued environment.activation)
    {patternHome : Module} {values : List Value} {stack : List Frame} {front back : List (Pattern × Expr)}
    {pattern : Pattern} {body : Expr} {bindings : List BindingInput}
    {name : BindingId} {boundType : Ty} {owner : Value}
    (run : Run program ⟨environment, .expression expression, []⟩
      ⟨current, .results values, .patterns patternHome (front ++ (pattern, body) :: back) :: stack⟩)
    (missed : ∀ earlier ∈ front, earlier.1.matchValue (argumentValue values) = none)
    (matched : pattern.matchValue (argumentValue values) = some bindings)
    (focus : Pattern.SubjectAt pattern (argumentValue values) (.binder name boundType) owner) :
    ∃ after identity position,
      Step program ⟨current, .results values, .patterns patternHome (front ++ (pattern, body) :: back) :: stack⟩ after ∧
      after.environment.bindings[position]? = some (name, identity) ∧
      lookup name after.environment.bindings = some identity ∧
      after.environment.heap.read identity = some ⟨current.activation, boundType, .resident owner⟩ ∧
      identity.index = current.heap.next + position ∧ ValueHasType program owner boundType := by
  have safe := (checked.soundness checkedProgram store issued run).2.2.2.2
  obtain ⟨subject, locals, actual, patternTyped⟩ := safe.selected_pattern missed matched
  obtain ⟨childType, childBindings, resident, childPattern⟩ := PatternType.subject_at focus patternTyped actual
  cases childPattern
  obtain ⟨inputs, before, after, childMatch, split⟩ := focus.matched matched
  have single : inputs = [⟨name, ⟨boundType, false⟩, owner⟩] := by
    simpa only [Pattern.matchValue, Option.some.injEq] using childMatch.symm
  have inputAt : bindings[before.length]? = some ⟨name, ⟨boundType, false⟩, owner⟩ := by
    simp [split, single, List.append_assoc]
  obtain ⟨identity, found, cell, position⟩ := allocateBindings.at current.heap current.activation inputAt
  have selected : selectArm (argumentValue values) (front ++ (pattern, body) :: back) = some (bindings, body) := by
    rw [selectArm.skip_missed _ _ _ missed]
    simp only [selectArm, matched]
  let result : Configuration := ⟨current.extend bindings, .expression body, .scope bindings.length :: stack⟩
  have entered : Step program
      ⟨current, .results values, .patterns patternHome (front ++ (pattern, body) :: back) :: stack⟩ result :=
    .selectedPattern selected
  have located : result.environment.bindings[before.length]? = some (name, identity) := by
    simp only [result, AddressedEnvironment.extend]
    exact List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1 |>.trans found
  have preserved := ConfigurationTyped.preservation checkedProgram
    (checked.soundness checkedProgram store issued run).1 entered
  have distinct : (result.environment.bindings.map Prod.fst).Nodup := by
    dsimp only [result] at preserved ⊢
    cases preserved with
    | intro store issued code continuation => exact store.keys.symm ▸ store.context_distinct
  exact ⟨result, identity, before.length, entered, located,
    lookup.of_mem distinct (List.mem_of_getElem? located), cell, position, resident⟩

/-- Every reached owned deconstruction uses authority from the module stored
by source elaboration in this very pattern frame, including nested fields and
matches reached inside called functions. Another module cannot supply access. -/
theorem HasType.pattern_deconstruction (checkedProgram : program.Checked)
    {context final : FlowContext} {expression : Expr} {type : Ty}
    (checked : HasType program home context expression type final)
    {environment current : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
    (issued : environment.supply.Issued environment.activation)
    {patternHome : Module} {values : List Value} {stack : List Frame} {front back : List (Pattern × Expr)}
    {pattern : Pattern} {body : Expr} {bindings : List BindingInput}
    {head : Head} {fields : List Pattern} {owner : Value}
    (run : Run program ⟨environment, .expression expression, []⟩
      ⟨current, .results values, .patterns patternHome (front ++ (pattern, body) :: back) :: stack⟩)
    (missed : ∀ earlier ∈ front, earlier.1.matchValue (argumentValue values) = none)
    (matched : pattern.matchValue (argumentValue values) = some bindings)
    (focus : Pattern.SubjectAt pattern (argumentValue values) (.node head fields) owner) :
    head.Accessible program patternHome := by
  have safe := (checked.soundness checkedProgram store issued run).2.2.2.2
  obtain ⟨subject, locals, actual, patternTyped⟩ := safe.selected_pattern missed matched
  obtain ⟨childType, childBindings, resident, childPattern⟩ := PatternType.subject_at focus patternTyped actual
  cases childPattern with
  | node shape access children => exact access

/-- A reached external non-exhaustive exact owner is not discarded or opened:
it is forwarded whole into an actual fresh binding, even when nested inside a
larger selected pattern. The externality test uses the frame's source module. -/
theorem HasType.pattern_external_exact_transfer (checkedProgram : program.Checked)
    {context final : FlowContext} {expression : Expr} {type : Ty}
    (checked : HasType program home context expression type final)
    {environment current : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
    (issued : environment.supply.Issued environment.activation)
    {patternHome : Module} {values : List Value} {stack : List Frame} {front back : List (Pattern × Expr)}
    {pattern selected : Pattern} {body : Expr} {bindings : List BindingInput}
    {identity : Nat} {tag : Option Nat} {fields : List Value} {declaration : DataDecl} {variants : List Fields}
    (declared : program.data identity = some declaration)
    (shape : declaration.shape = .enumeration variants true)
    (external : patternHome.package ≠ declaration.home.package)
    (exactOwner : ¬ UsePermitted program.data .discard (.nominal identity))
    (run : Run program ⟨environment, .expression expression, []⟩
      ⟨current, .results values, .patterns patternHome (front ++ (pattern, body) :: back) :: stack⟩)
    (missed : ∀ earlier ∈ front, earlier.1.matchValue (argumentValue values) = none)
    (matched : pattern.matchValue (argumentValue values) = some bindings)
    (focus : Pattern.SubjectAt pattern (argumentValue values) selected (.nominal identity tag fields)) :
    ∃ name after storage position, selected = .binder name (.nominal identity) ∧
      Step program ⟨current, .results values, .patterns patternHome (front ++ (pattern, body) :: back) :: stack⟩ after ∧
      lookup name after.environment.bindings = some storage ∧
      after.environment.heap.read storage = some ⟨current.activation, .nominal identity, .resident (.nominal identity tag fields)⟩ ∧
      storage.index = current.heap.next + position := by
  have safe := (checked.soundness checkedProgram store issued run).2.2.2.2
  obtain ⟨subject, locals, actual, patternTyped⟩ := safe.selected_pattern missed matched
  obtain ⟨childType, childBindings, resident, childPattern⟩ := PatternType.subject_at focus patternTyped actual
  cases resident with
  | nominal found chosen finite residents =>
    obtain ⟨name, same, _⟩ := childPattern.nonexhaustive_exact_forward declared shape external exactOwner
    subst selected
    obtain ⟨after, storage, position, entered, _, mapped, stored, fresh, _⟩ :=
      checked.pattern_binding checkedProgram store issued run missed matched focus
    exact ⟨name, after, storage, position, rfl, entered, mapped, stored, fresh⟩

/-- Every reached projection transfers a well-typed field with authority at
its elaborated module and leaves exactly a discardable residual aggregate. -/
theorem HasType.projection_transfer (checkedProgram : program.Checked)
    {context final : FlowContext} {expression : Expr} {type : Ty}
    (checked : HasType program home context expression type final)
    {environment current : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
    (issued : environment.supply.Issued environment.activation)
    {projectionHome : Module} {aggregate : Value} {key : FieldKey} {stack : List Frame}
    (run : Run program ⟨environment, .expression expression, []⟩
      ⟨current, .result aggregate, .project projectionHome key :: stack⟩) :
    ∃ parent child index selected remainder,
      ValueHasType program aggregate parent ∧
      ProjectionType program projectionHome parent key index child ∧
      Step program ⟨current, .result aggregate, .project projectionHome key :: stack⟩
        ⟨current, .result selected, stack⟩ ∧
      ValueHasType program selected child ∧
      (PartialValue.resident aggregate).writeFields program parent [key] .hole = some remainder ∧
      remainder.selectFields program parent [key] = some .hole ∧ remainder.Disposable program parent ∧
      ∀ (observer : Module) (descendant : Ty) (path : List FieldKey) (owner : Value),
        PathDisjoint program observer parent [key] path →
        PathType program observer parent path descendant →
        ((PartialValue.resident aggregate).selectFields program parent path).bind PartialValue.read = some owner →
        UsePermitted program.data .discard descendant ∧
        ∀ ownerType, ValueHasType program owner ownerType → UsePermitted program.data .discard ownerType := by
  have safe := (checked.soundness checkedProgram store issued run).2.2.2.2
  change aggregate.ProjectionCleanupSafe program projectionHome key at safe
  obtain ⟨parent, child, index, selected, remainder, resident, access, found, typed, written, absent, disposable⟩ := safe
  refine ⟨parent, child, index, selected, remainder, resident, access, .projectResult found,
    typed, written, absent, disposable, ?_⟩
  intro observer descendant path owner apart pathTyped observed
  have retained : (remainder.selectFields program parent path).bind PartialValue.read = some owner := by
    rw [apart.write_frame written]
    exact observed
  refine ⟨disposable.selected_permission pathTyped retained, ?_⟩
  intro ownerType ownerTyped
  obtain ⟨part, located, permission⟩ := pathTyped.disposable disposable
  rw [located] at retained
  exact permission.read_permission_as retained ownerTyped

/-- A move reached during arbitrary checked execution transfers the original
resident, leaves a real hole and preserves retained callers. No successful move
or next-state realization is supplied. -/
theorem HasType.move_transfers (checkedProgram : program.Checked)
    {context final : FlowContext} {expression : Expr} {type : Ty}
    (checked : HasType program home context expression type final)
    {environment current : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
    (issued : environment.supply.Issued environment.activation)
    {place : Place} {stack : List Frame}
    (run : Run program ⟨environment, .expression expression, []⟩
      ⟨current, .expression (.move place), stack⟩) :
    ∃ after value movedType,
      current.read program place = some value ∧ ValueHasType program value movedType ∧
      Step program ⟨current, .expression (.move place), stack⟩ ⟨after, .result value, stack⟩ ∧
      ConfigurationTyped program final (.one type) ⟨after, .result value, stack⟩ ∧
      after.take program place = none ∧ after.read program place = none ∧ after.scope = current.scope ∧
      after.supply = current.supply ∧ after.heap.next = current.heap.next ∧
      (∃ address old next, current.bindings.resolve place = some address ∧
        current.heap.read address.root = some old ∧ after.heap.read address.root = some next ∧
        next.activation = old.activation ∧ next.type = old.type ∧
        next.resident.selectFields program next.type address.fields = some .hole) ∧
      ∀ (caller : AddressedScope) states,
        BindingMap.Typed program current.heap caller.activation caller.bindings states →
        caller.activation ≠ current.activation →
        BindingMap.Typed program after.heap caller.activation caller.bindings states ∧
        (∀ identity ∈ caller.bindings.map Prod.snd, after.heap.read identity = current.heap.read identity) := by
  have typed := (checked.soundness checkedProgram store issued run).1
  have original := typed
  cases typed with
  | intro currentStore currentIssued code continuation =>
    cases code with
    | expression checked =>
      cases checked with
      | move selected path selection ready mask context =>
        obtain ⟨value, after, updated, nextContext, taken, resident, _, _, _, absent, scope, supply, next, retained⟩ :=
          AddressedEnvironment.take.progress currentStore selected path selection ready
        have observed : current.read program place = some value := by
          obtain ⟨pair, raw, same⟩ := Option.map_eq_some_iff.mp taken
          have valueSame : pair.1 = value := congrArg Prod.fst same
          exact valueSame ▸ BindingMap.take.read_before raw
        have entered : Step program ⟨current, .expression (.move place), stack⟩ ⟨after, .result value, stack⟩ := .move taken
        have hole := AddressedEnvironment.take.hole taken
        have unreadable : after.read program place = none := by
          obtain ⟨address, old, next, resolved, _, found, _, _, empty⟩ := hole
          have bindings : after.bindings = current.bindings := congrArg AddressedScope.bindings scope
          change after.bindings.read program after.heap place = none
          simp [BindingMap.read, bindings, resolved, StorageAddress.read, found, empty, PartialValue.read]
        exact ⟨after, value, _, observed, resident, entered,
          original.preservation checkedProgram entered, absent, unreadable, scope, supply, next, hole, retained⟩

end Grounded

