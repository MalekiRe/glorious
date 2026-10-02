import Grounded.Checking
import Grounded.Execution

/-! Flow checking supplies sound masks for each continuation. Arm-local masks
are approximated at scope retirement; retained callers are realized in the current heap. -/
namespace Grounded

inductive ResultType where
  | one (type : Ty)
  | many (types : List Ty)

inductive ControlTyped (program : Program) (before : FlowContext) : Control → ResultType → FlowContext → Prop where
  | expression {home expression type after} (checked : HasType program home before expression type after) :
      ControlTyped program before (.expression expression) (.one type) after
  | arguments {home expressions types after} (checked : HasTypes program home before expressions types after) :
      ControlTyped program before (.arguments expressions) (.many types) after
  | result {value type} (resident : ValueHasType program value type) :
      ControlTyped program before (.result value) (.one type) before
  | results {values types} (residents : ValuesHaveTypes program values types) :
      ControlTyped program before (.results values) (.many types) before

inductive FrameTyped (program : Program) (heap : RuntimeHeap StorageCell) (supply : ActivationSupply)
    (activation : ActivationId) : FlowContext → ResultType → Frame → FlowContext → ResultType → Prop where
  | sequence {home before after discarded result rest}
      (discard : UsePermitted program.data .discard discarded) (checked : HasType program home before rest result after) :
      FrameTyped program heap supply activation before (.one discarded) (.sequence rest) after (.one result)
  | bind {home before after name mutable localType result body finalMask}
      (discard : finalMask.Disposable program.data localType)
      (checked : HasType program home ((name, ⟨⟨localType, mutable⟩, .present⟩) :: before) body result
        ((name, ⟨⟨localType, mutable⟩, finalMask⟩) :: after))
      (fresh : name ∉ before.map Prod.fst) :
      FrameTyped program heap supply activation before (.one localType) (.bind name ⟨localType, mutable⟩ body) after (.one result)
  | scope {context after : FlowContext} (locals : FlowContext) {result}
      (discard : ∀ binding ∈ locals, binding.2.Disposable program.data)
      (joined : BindingContextApprox program.data context after) :
      FrameTyped program heap supply activation (locals ++ context) (.one result) (.scope locals.length) after (.one result)
  | assign {home before restored after place type result rest state updated available}
      (selected : lookup place.root before = some state)
      (path : PathType program home state.slot.type place.fields type)
      (writable : state.slot.mutable = true)
      (selection : state.initialization.selectFields program state.slot.type place.fields = some available)
      (discard : available.Disposable program.data type)
      (mask : state.initialization.writeFields program state.slot.type place.fields .present = some updated)
      (context : replaceBinding place.root { state with initialization := updated } before = some restored)
      (checked : HasType program home restored rest result after) :
      FrameTyped program heap supply activation before (.one type) (.assign place rest) after (.one result)
  | tupleHead {home before after first types tail} (checked : HasTypes program home before tail types after) :
      FrameTyped program heap supply activation before (.one first) (.tupleHead tail) after (.one (.tuple first types))
  | tupleTail {context first types head} (resident : ValueHasType program head first) :
      FrameTyped program heap supply activation context (.many types) (.tupleTail head) context (.one (.tuple first types))
  | project {home context parent result key index residual}
      (discard : residual.Disposable program.data parent)
      (mask : Initialization.present.writeFields program parent [key] .absent = some residual)
      (selected : ProjectionType program home parent key index result) :
      FrameTyped program heap supply activation context (.one parent) (.project home key) context (.one result)
  | array {context element length} (finite : FiniteLayout program.target program.data element)
      (size : length < 2 ^ program.target.pointerBits) :
      FrameTyped program heap supply activation context (.many (List.replicate length element)) .array context (.one (.array element length))
  | construct {home context identity tag declaration schema}
      (declared : program.data identity = some declaration) (chosen : declaration.constructor tag = some schema)
      (finite : FiniteLayout program.target program.data (.nominal identity))
      (visible : declaration.visibility.Allows declaration.home home)
      (access : ∀ field ∈ schema.residents, field.visibility.Allows declaration.home home) :
      FrameTyped program heap supply activation context (.many (schema.residents.map Field.type))
        (.construct identity tag) context (.one (.nominal identity))
  | call {context identity declaration} (declared : program.functions identity = some declaration) :
      FrameTyped program heap supply activation context (.many (declaration.parameters.map fun parameter => parameter.2.type))
        (.call declaration) context (.one declaration.result)
  | patterns {home before after inputs arms result}
      (nonempty : arms ≠ []) (covered : Covers program home [argumentType inputs] (arms.map fun arm => [arm.1]))
      (checked : ArmsType program home before (argumentType inputs) result [] arms after) :
      FrameTyped program heap supply activation before (.many inputs) (.patterns home arms) after (.one result)
  | restore {context : FlowContext} (locals : FlowContext) {result} {caller : AddressedScope}
      (discard : ∀ binding ∈ locals, binding.2.Disposable program.data)
      (retained : BindingMap.Typed program heap caller.activation caller.bindings context)
      (issued : supply.Issued caller.activation) (older : caller.activation.index < activation.index) :
      FrameTyped program heap supply activation locals (.one result) (.restore caller) context (.one result)
  | argumentHead {home before after first types tail} (checked : HasTypes program home before tail types after) :
      FrameTyped program heap supply activation before (.one first) (.argumentHead tail) after (.many (first :: types))
  | argumentTail {context first types head} (resident : ValueHasType program head first) :
      FrameTyped program heap supply activation context (.many types) (.argumentTail head) context (.many (first :: types))

inductive ContinuationTyped (program : Program) (heap : RuntimeHeap StorageCell) (supply : ActivationSupply) :
    ActivationId → FlowContext → ResultType → List Frame → FlowContext → ResultType → Prop where
  | nil {activation context result} : ContinuationTyped program heap supply activation context result [] context result
  | cons {activation context middle final input result output frame stack}
      (head : FrameTyped program heap supply activation context input frame middle result)
      (tail : ContinuationTyped program heap supply (frame.activation activation) middle result stack final output) :
      ContinuationTyped program heap supply activation context input (frame :: stack) final output

inductive ConfigurationTyped (program : Program) (context : FlowContext) (result : ResultType) : Configuration → Prop where
  | intro {current next : FlowContext} {input : ResultType} {environment : Environment} {control : Control} {stack : List Frame}
      (store : BindingMap.Typed program environment.heap environment.activation environment.bindings current)
      (issued : environment.supply.Issued environment.activation)
      (code : ControlTyped program current control input next)
      (continuation : ContinuationTyped program environment.heap environment.supply environment.activation next input stack context result) :
      ConfigurationTyped program context result ⟨environment, control, stack⟩

variable {program : Program}

theorem FrameTyped.activation_le {heap supply activation context next input result frame}
    (typed : FrameTyped program heap supply activation context input frame next result) :
    (frame.activation activation).index ≤ activation.index := by
  cases typed <;> simp only [Frame.activation] <;> omega

theorem FrameTyped.transport {heap after supply nextSupply activation context next input result frame}
    (typed : FrameTyped program heap supply activation context input frame next result)
    (issued : ∀ previous, supply.Issued previous → nextSupply.Issued previous)
    (preserved : ∀ (scope : AddressedScope) states, BindingMap.Typed program heap scope.activation scope.bindings states →
      scope.activation.index < activation.index → BindingMap.Typed program after scope.activation scope.bindings states) :
    FrameTyped program after nextSupply activation context input frame next result := by
  cases typed <;> constructor <;> first | assumption | apply preserved <;> assumption | apply issued <;> assumption

theorem ContinuationTyped.transport {heap after supply nextSupply activation context final input result stack}
    (typed : ContinuationTyped program heap supply activation context input stack final result)
    (issued : ∀ previous, supply.Issued previous → nextSupply.Issued previous)
    (preserved : ∀ (scope : AddressedScope) states, BindingMap.Typed program heap scope.activation scope.bindings states →
      scope.activation.index < activation.index → BindingMap.Typed program after scope.activation scope.bindings states) :
    ContinuationTyped program after nextSupply activation context input stack final result := by
  revert preserved
  induction typed with
  | nil => intro _; exact .nil
  | cons head tail ih =>
    intro preserved
    refine .cons (head.transport issued preserved) (ih ?_)
    intro scope states typed older
    exact preserved scope states typed (Nat.lt_of_lt_of_le older head.activation_le)

theorem ConfigurationTyped.entry {home before after expression type environment}
    (checked : HasType program home before expression type after)
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings before)
    (issued : environment.supply.Issued environment.activation) :
    ConfigurationTyped program after (.one type) ⟨environment, .expression expression, []⟩ :=
  .intro store issued (.expression checked) .nil

/-- Progress uses the current masks, including holes. Pending continuations
carry static output contexts, never assumptions that future heaps are ready. -/
theorem ConfigurationTyped.progress {context result state}
    (typed : ConfigurationTyped program context result state) : Terminal state ∨ ∃ next, Step program state next := by
  cases typed with
  | intro store issued code continuation =>
    cases code with
    | expression checked =>
      right
      cases checked with
      | unit => exact ⟨_, .unit⟩
      | integer fits => exact ⟨_, .integer fits⟩
      | character valid => exact ⟨_, .character valid⟩
      | group body => exact ⟨_, .group⟩
      | read selected path selection ready copyable =>
        obtain ⟨value, read, _⟩ := AddressedEnvironment.read.progress store selected path selection ready
        exact ⟨_, .read read⟩
      | move selected path selection ready mask context =>
        obtain ⟨value, after, _, _, taken, _⟩ := AddressedEnvironment.take.progress store selected path selection ready
        exact ⟨_, .move taken⟩
      | sequence head discard tail => exact ⟨_, .sequence⟩
      | bind initial discard body fresh => exact ⟨_, .bind⟩
      | tuple head tail => exact ⟨_, .tuple⟩
      | project source discard mask selected => exact ⟨_, .project⟩
      | array residents finite size => exact ⟨_, .array⟩
      | constant declared visible resolved structural body => exact ⟨_, .constant declared⟩
      | construct declared chosen finite visible access residents => exact ⟨_, .construct⟩
      | call declared visible inputs => exact ⟨_, .call declared⟩
      | assign resident selected path writable selection discard mask context rest => exact ⟨_, .assign⟩
      | applyPatterns arguments nonempty covered bodies => exact ⟨_, .applyPatterns⟩
    | arguments checked =>
      right
      cases checked with
      | nil => exact ⟨_, .nil⟩
      | cons head tail => exact ⟨_, .cons⟩
    | result resident =>
      cases continuation with
      | nil => exact .inl (.result _ _)
      | cons frame tail =>
        right
        cases frame with
        | sequence discard checked => exact ⟨_, .sequenceResult⟩
        | bind discard checked fresh => exact ⟨_, .bindResult⟩
        | scope locals discard joined =>
          obtain ⟨after, exited, _⟩ := AddressedEnvironment.exitScope.progress store locals.length
          exact ⟨_, .scope exited⟩
        | assign selected path writable selection discard mask context checked =>
          obtain ⟨after, _, _, written, _⟩ := AddressedEnvironment.write.progress store selected path resident
          exact ⟨_, .assignResult written⟩
        | tupleHead checked => exact ⟨_, .tupleHead⟩
        | project discard mask projection =>
          obtain ⟨value, selected, _, _⟩ := projection.access resident
          exact ⟨_, .projectResult selected⟩
        | restore locals discard retained callerIssued older =>
          obtain ⟨after, restored, _⟩ := AddressedEnvironment.restore.progress store retained (by
            intro same; have := congrArg ActivationId.index same; omega)
          exact ⟨_, .restore restored⟩
        | argumentHead checked => exact ⟨_, .argumentHead⟩
    | results residents =>
      cases continuation with
      | nil => exact .inl (.results _ _)
      | cons frame tail =>
        right
        cases frame with
        | tupleTail head => exact ⟨_, .tupleTail⟩
        | array finite size => exact ⟨_, .arrayResult⟩
        | construct declared chosen finite visible access => exact ⟨_, .constructResult⟩
        | call declared =>
          obtain ⟨inputs, prepared⟩ := prepareBindings.exists residents
          exact ⟨_, .callInputs prepared⟩
        | patterns nonempty covered checked =>
          obtain ⟨bindings, body, selected⟩ := covered.selectArm residents.argument
          exact ⟨_, .selectedPattern selected⟩
        | argumentTail head => exact ⟨_, .argumentTail⟩

theorem ConfigurationTyped.invoke {environment : Environment} {callerContext final locals : FlowContext}
    {home body type result stack} {inputs : List BindingInput}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings callerContext)
    (issued : environment.supply.Issued environment.activation)
    (continuation : ContinuationTyped program environment.heap environment.supply environment.activation
      callerContext (.one type) stack final result)
    (inputsTyped : BindingInputsTyped program inputs)
    (checked : HasType program home (inputs.map BindingInput.state) body type locals)
    (discard : ∀ binding ∈ locals, binding.2.Disposable program.data) :
    ConfigurationTyped program final result
      ⟨enterBindings environment.heap environment.supply inputs, .expression body, .restore environment.scope :: stack⟩ := by
  refine .intro (enterBindings.typed inputsTyped _ _) environment.supply.allocate_issued (.expression checked)
    (.cons (.restore locals discard (store.allocate _ inputs) (ActivationSupply.allocate_preserves issued) issued) ?_)
  apply continuation.transport (fun _ previous => ActivationSupply.allocate_preserves previous)
  intro scope states retained _
  exact retained.allocate _ inputs


theorem ConfigurationTyped.preservation {context : FlowContext} {result : ResultType}
    {before after : Configuration} (checkedProgram : program.Checked)
    (typed : ConfigurationTyped program context result before)
    (step : Step program before after) : ConfigurationTyped program context result after := by
  cases typed with
  | intro store issued code continuation =>
    cases step with
    | unit =>
      cases code with | expression checked => cases checked; exact .intro store issued (.result .unit) continuation
    | integer fits =>
      cases code with | expression checked => cases checked; exact .intro store issued (.result (.integer fits)) continuation
    | character valid =>
      cases code with | expression checked => cases checked; exact .intro store issued (.result (.character valid)) continuation
    | group =>
      cases code with | expression checked =>
        cases checked with | group body => exact .intro store issued (.expression body) continuation
    | read actual =>
      cases code with | expression checked =>
        cases checked with | read selected path selection ready copyable =>
          obtain ⟨value, found, resident⟩ := AddressedEnvironment.read.progress store selected path selection ready
          cases Option.some.inj (actual.symm.trans found)
          exact .intro store issued (.result resident) continuation
    | move actual =>
      cases code with | expression checked =>
        cases checked with | move selected path selection ready mask context =>
          obtain ⟨value, next, nextMask, nextContext, taken, resident, maskTaken, contextTaken, nextTyped,
            _, scope, supply, _, retained⟩ := AddressedEnvironment.take.progress store selected path selection ready
          cases Option.some.inj (mask.symm.trans maskTaken)
          cases Option.some.inj (context.symm.trans contextTaken)
          cases Option.some.inj (actual.symm.trans taken)
          have activation := congrArg AddressedScope.activation scope
          simp only [AddressedEnvironment.scope] at activation
          refine .intro nextTyped (by rw [supply, activation]; exact issued) (.result resident) ?_
          rw [supply, activation]
          apply continuation.transport (fun _ previous => previous)
          intro caller states callerTyped older
          exact (retained caller states callerTyped (by intro same; have := congrArg ActivationId.index same; omega)).1
    | sequence =>
      cases code with | expression checked =>
        cases checked with | sequence head discard tail =>
          exact .intro store issued (.expression head) (.cons (.sequence discard tail) continuation)
    | sequenceResult =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          cases frame with | sequence discard checked => exact .intro store issued (.expression checked) tail
    | bind =>
      cases code with | expression checked =>
        cases checked with | bind initial discard body fresh =>
          exact .intro store issued (.expression initial) (.cons (.bind discard body fresh) continuation)
    | @bindResult env stack name slot body value =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          cases frame with | @bind home before after bindingName mutable localType result body finalMask discard checked fresh =>
            have contextDistinct := store.context_distinct
            obtain ⟨entered, _, _, retained⟩ := AddressedEnvironment.extend.typed store
              (inputs := [⟨name, ⟨_, mutable⟩, value⟩]) (.cons resident .nil (by simp))
              (by simpa using List.nodup_cons.mpr ⟨fresh, contextDistinct⟩)
            refine .intro entered issued (.expression checked) (.cons (.scope [_] (by simpa [BindingState.Disposable] using discard) (.refl _)) ?_)
            exact tail.transport (fun _ previous => previous)
              (fun scope states typed _ => (retained scope.activation scope.bindings states typed).1)
    | scope exited =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          cases frame with | scope locals discard joined =>
            obtain ⟨after, produced, afterTyped, activation, supply, _, _, retained, _⟩ :=
              AddressedEnvironment.exitScope.progress store locals.length
            cases Option.some.inj (exited.symm.trans produced)
            refine .intro ((BindingMap.Typed.approximate (by simpa using afterTyped) joined)) (by rw [supply, activation]; exact issued) (.result resident) ?_
            rw [activation, supply]
            apply tail.transport (fun _ previous => previous)
            intro scope states typed older
            simp only [Frame.activation] at older
            exact (retained scope states typed (by intro same; have := congrArg ActivationId.index same; omega)).1
    | assign =>
      cases code with | expression checked =>
        cases checked with | assign resident selected path writable selection discard mask context rest =>
          exact .intro store issued (.expression resident)
            (.cons (.assign selected path writable selection discard mask context rest) continuation)
    | assignResult written =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          cases frame with | assign selected path writable selection discard mask context checked =>
            obtain ⟨next, nextMask, nextContext, produced, maskWritten, contextWritten, nextTyped,
              _, scope, supply, _, _, retained⟩ := AddressedEnvironment.write.progress store selected path resident
            cases Option.some.inj (mask.symm.trans maskWritten)
            cases Option.some.inj (context.symm.trans contextWritten)
            cases Option.some.inj (written.symm.trans produced)
            have activation := congrArg AddressedScope.activation scope
            simp only [AddressedEnvironment.scope] at activation
            refine .intro nextTyped (by rw [supply, activation]; exact issued) (.expression checked) ?_
            rw [supply, activation]
            apply tail.transport (fun _ previous => previous)
            intro caller states callerTyped older
            simp only [Frame.activation] at older
            exact (retained caller states callerTyped (by intro same; have := congrArg ActivationId.index same; omega)).1
    | tuple =>
      cases code with | expression checked =>
        cases checked with | tuple head tail =>
          exact .intro store issued (.expression head) (.cons (.tupleHead tail) continuation)
    | tupleHead =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          cases frame with | tupleHead checked =>
            exact .intro store issued (.arguments checked) (.cons (.tupleTail resident) tail)
    | tupleTail =>
      cases code with | results residents =>
        cases continuation with | cons frame tail =>
          cases frame with | tupleTail head => exact .intro store issued (.result (.tuple head residents)) tail
    | project =>
      cases code with | expression checked =>
        cases checked with | project source discard mask selected =>
          exact .intro store issued (.expression source) (.cons (.project discard mask selected) continuation)
    | projectResult selected =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          cases frame with | project discard mask projection =>
            obtain ⟨value, found, valueTyped, _⟩ := projection.access resident
            cases Option.some.inj (selected.symm.trans found)
            exact .intro store issued (.result valueTyped) tail
    | array =>
      cases code with | expression checked =>
        cases checked with | array residents finite size =>
          exact .intro store issued (.arguments residents) (.cons (.array finite size) continuation)
    | arrayResult =>
      cases code with | results residents =>
        cases continuation with | cons frame tail =>
          cases frame with | array finite size => exact .intro store issued (.result (.array residents finite size)) tail
    | constant declared =>
      cases code with | expression checked =>
        cases checked with | constant otherDeclared visible resolved structural body =>
          cases Option.some.inj (declared.symm.trans otherDeclared)
          exact ConfigurationTyped.invoke store issued continuation .nil body (by simp)
    | restore restored =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          cases frame with | restore locals discard callerTyped callerIssued older =>
            obtain ⟨after, produced, afterTyped, activation, bindings, supply, _, _, _, retained⟩ :=
              AddressedEnvironment.restore.progress store callerTyped (by
                intro same; have := congrArg ActivationId.index same; omega)
            cases Option.some.inj (restored.symm.trans produced)
            refine .intro (by rw [activation, bindings]; exact afterTyped)
              (by rw [supply, activation]; exact callerIssued) (.result resident) ?_
            rw [activation, supply]
            apply tail.transport (fun _ previous => previous)
            intro previous states typed oldest
            exact (retained previous states typed (by
              intro same; have := congrArg ActivationId.index same; simp only [Frame.activation] at oldest; omega)).1
    | construct =>
      cases code with | expression checked =>
        cases checked with | construct declared chosen finite visible access residents =>
          exact .intro store issued (.arguments residents) (.cons (.construct declared chosen finite visible access) continuation)
    | constructResult =>
      cases code with | results residents =>
        cases continuation with | cons frame tail =>
          cases frame with | construct declared chosen finite visible access =>
            exact .intro store issued (.result (.nominal declared chosen finite residents)) tail
    | call declared =>
      cases code with | expression checked =>
        cases checked with | call otherDeclared visible inputs =>
          cases Option.some.inj (declared.symm.trans otherDeclared)
          exact .intro store issued (.arguments inputs) (.cons (.call otherDeclared) continuation)
    | callInputs prepared =>
      cases code with | results residents =>
        cases continuation with | cons frame tail =>
          cases frame with | call declared =>
            have declaration := checkedProgram.functions _ _ declared
            obtain ⟨inputs, preparedInputs, inputsTyped, slots⟩ := prepareBindings.progress residents declaration.distinct
            cases Option.some.inj (prepared.symm.trans preparedInputs)
            obtain ⟨locals, body, discard⟩ := declaration.body
            apply ConfigurationTyped.invoke store issued tail inputsTyped
            · rw [← slots] at body
              simp only [initializedContext, List.map_map, Function.comp_def] at body
              exact body
            · exact discard
    | applyPatterns =>
      cases code with | expression checked =>
        cases checked with | applyPatterns arguments nonempty covered bodies =>
          exact .intro store issued (.arguments arguments) (.cons (.patterns nonempty covered bodies) continuation)
    | selectedPattern selected =>
      cases code with | results residents =>
        cases continuation with | cons frame tail =>
          cases frame with | patterns nonempty covered checked =>
            obtain ⟨locals, localsAfter, branchAfter, _, _, inputsTyped, slots, discard, bodyTyped, localSlots, distinct, joined, _⟩ :=
              checked.selected residents.argument selected
            obtain ⟨entered, _, _, retained⟩ := AddressedEnvironment.extend.typed store inputsTyped (by
              rw [← slots] at distinct
              simpa only [FlowContext.slots, List.map_append, List.map_map, Function.comp_def] using distinct)
            have states := congrArg initializedContext slots
            simp only [initializedContext, List.map_map, Function.comp_def] at states
            change List.map BindingInput.state _ = initializedContext locals at states
            rw [states] at entered
            refine .intro entered issued (.expression bodyTyped) (.cons ?_
              (tail.transport (fun _ previous => previous)
                (fun scope states typed _ => (retained scope.activation scope.bindings states typed).1)))
            have length := congrArg List.length slots
            have localLength := congrArg List.length localSlots
            simp only [FlowContext.slots, List.length_map] at length localLength
            rw [length, ← localLength]
            exact FrameTyped.scope _ discard joined
    | nil =>
      cases code with | arguments checked => cases checked; exact .intro store issued (.results .nil) continuation
    | cons =>
      cases code with | arguments checked =>
        cases checked with | cons head tail =>
          exact .intro store issued (.expression head) (.cons (.argumentHead tail) continuation)
    | argumentHead =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          cases frame with | argumentHead checked =>
            exact .intro store issued (.arguments checked) (.cons (.argumentTail resident) tail)
    | argumentTail =>
      cases code with | results residents =>
        cases continuation with | cons frame tail =>
          cases frame with | argumentTail head => exact .intro store issued (.results (.cons head residents)) tail



theorem ConfigurationTyped.run {context result before after}
    (checkedProgram : program.Checked)
    (typed : ConfigurationTyped program context result before) (run : Run program before after) :
    ConfigurationTyped program context result after := by
  induction run with
  | refl state => exact typed
  | step head tail ih => exact ih (typed.preservation checkedProgram head)

theorem ConfigurationTyped.bindings_distinct {context result state}
    (typed : ConfigurationTyped program context result state) : (state.environment.bindings.map Prod.fst).Nodup := by
  cases typed with
  | intro store issued code continuation => rw [store.keys]; exact store.context_distinct

theorem ConfigurationTyped.normal_form {context type state}
    (typed : ConfigurationTyped program context (.one type) state) (done : Terminal state) :
    ∃ environment value, state = ⟨environment, .result value, []⟩ ∧
      BindingMap.Typed program environment.heap environment.activation environment.bindings context ∧
      environment.supply.Issued environment.activation ∧ ValueHasType program value type := by
  cases done with
  | result environment value =>
    cases typed with | intro store issued code continuation =>
      cases continuation
      cases code with | result resident => exact ⟨_, _, rfl, store, issued, resident⟩
  | results environment values =>
    cases typed with | intro store issued code continuation =>
      cases continuation
      cases code


theorem ControlTyped.slots {current next control result}
    (typed : ControlTyped program current control result next) : next.slots = current.slots := by
  cases typed with
  | expression checked => exact checked.slots
  | arguments checked => exact checked.slots
  | result | results => rfl

theorem FrameTyped.declares {before : Environment} {current next : FlowContext}
    {input result : ResultType} {frame : Frame}
    (typed : FrameTyped program before.heap before.supply before.activation current input frame next result)
    (store : before.Declares program current.slots) : (frame.environment before).Declares program next.slots := by
  cases typed with
  | sequence discard checked => simpa only [Frame.environment, Frame.activation, checked.slots] using store
  | bind discard checked fresh =>
    have same : next.slots = current.slots := congrArg List.tail checked.slots
    simpa only [Frame.environment, Frame.activation, same] using store
  | scope locals discard joined =>
    simpa [Frame.environment, Frame.activation, FlowContext.slots, joined.slots] using store.drop locals.length
  | assign selected path writable selection discard mask context checked =>
    have same : next.slots = current.slots := checked.slots.trans (replaceBinding.map_same BindingState.slot selected context rfl)
    simpa only [Frame.environment, Frame.activation, same] using store
  | tupleHead checked => simpa only [Frame.environment, Frame.activation, checked.slots] using store
  | patterns nonempty covered checked => simpa only [Frame.environment, Frame.activation, checked.slots nonempty] using store
  | restore locals discard caller issued older => exact ⟨_, caller, rfl⟩
  | argumentHead checked => simpa only [Frame.environment, Frame.activation, checked.slots] using store
  | tupleTail | project | array | construct | call | argumentTail => exact store


theorem FrameTyped.consumption_frame {before after : Environment} {current next : FlowContext}
    {input result : ResultType} {frame : Frame}
    (typed : FrameTyped program before.heap before.supply before.activation current input frame next result)
    (store : before.Declares program current.slots)
    (framed : AddressedEnvironment.ConsumptionFrame program current.slots before after)
    (retained : ∀ (scope : AddressedScope) states,
      BindingMap.Typed program before.heap scope.activation scope.bindings states →
      scope.activation.index < before.activation.index →
      ∀ identity ∈ scope.bindings.map Prod.snd, after.heap.read identity = before.heap.read identity) :
    AddressedEnvironment.ConsumptionFrame program next.slots (frame.environment before) (frame.environment after) := by
  cases typed with
  | sequence discard checked => simpa only [Frame.environment, Frame.activation, checked.slots] using framed
  | bind discard checked fresh =>
    have same : next.slots = current.slots := congrArg List.tail checked.slots
    simpa only [Frame.environment, Frame.activation, same] using framed
  | scope locals discard joined =>
    simpa [Frame.environment, Frame.activation, FlowContext.slots, joined.slots] using framed.drop store locals.length
  | assign selected path writable selection discard mask context checked =>
    have same : next.slots = current.slots := checked.slots.trans (replaceBinding.map_same BindingState.slot selected context rfl)
    simpa only [Frame.environment, Frame.activation, same] using framed
  | tupleHead checked => simpa only [Frame.environment, Frame.activation, checked.slots] using framed
  | patterns nonempty covered checked => simpa only [Frame.environment, Frame.activation, checked.slots nonempty] using framed
  | restore locals discard caller issued older => 
    refine AddressedEnvironment.ConsumptionFrame.of_cells ?_ ?_
    · rfl
    · exact retained _ _ caller older
  | argumentHead checked => simpa only [Frame.environment, Frame.activation, checked.slots] using framed
  | tupleTail | project | array | construct | call | argumentTail => exact framed


theorem ContinuationTyped.consumption_frame {before after : Environment} {current final : FlowContext}
    {input result : ResultType} {stack : List Frame}
    (typed : ContinuationTyped program before.heap before.supply before.activation current input stack final result)
    (store : before.Declares program current.slots)
    (framed : AddressedEnvironment.ConsumptionFrame program current.slots before after)
    (retained : ∀ (scope : AddressedScope) states,
      BindingMap.Typed program before.heap scope.activation scope.bindings states →
      scope.activation.index < before.activation.index →
      ∀ identity ∈ scope.bindings.map Prod.snd, after.heap.read identity = before.heap.read identity) :
    AddressedEnvironment.ConsumptionFrame program final.slots
      (continuationEnvironment before stack) (continuationEnvironment after stack) := by
  induction stack generalizing before after current input with
  | nil => cases typed; exact framed
  | cons frame stack ih =>
    cases typed with
    | cons head tail =>
      apply ih tail (head.declares store) (head.consumption_frame store framed retained)
      intro scope states realized older
      exact retained scope states realized (Nat.lt_of_lt_of_le older head.activation_le)

theorem ContinuationTyped.consumption_allocation {before : Environment} {current final : FlowContext}
    {input result : ResultType} {stack : List Frame}
    (typed : ContinuationTyped program before.heap before.supply before.activation current input stack final result)
    (store : before.Declares program current.slots) (owner : ActivationId) (inputs : List BindingInput) (supply : ActivationSupply) :
    AddressedEnvironment.ConsumptionFrame program final.slots (continuationEnvironment before stack)
      (continuationEnvironment { before with heap := (allocateBindings before.heap owner inputs).2, supply := supply } stack) := by
  obtain ⟨states, stateTyped, slots⟩ := store
  apply typed.consumption_frame (after := { before with heap := (allocateBindings before.heap owner inputs).2, supply := supply })
    ⟨states, stateTyped, slots⟩ (.of_cells rfl (stateTyped.allocate_preserves owner inputs))
  intro scope states realized _
  exact realized.allocate_preserves owner inputs


/-- Every machine step preserves external immutable cells up to actual
consumption. Allocation, retirement and retained callers preserve cells exactly. -/
theorem ConfigurationTyped.consumption_step {context : FlowContext} {result : ResultType} {before after : Configuration}
    (typed : ConfigurationTyped program context result before) (step : Step program before after) :
    AddressedEnvironment.ConsumptionFrame program context.slots before.outerEnvironment after.outerEnvironment := by
  cases typed with
  | @intro current next input env control stack store issued code continuation =>
    have declared : env.Declares program next.slots := ⟨current, store, code.slots.symm⟩
    cases step <;> try exact .refl _ _
    case constant name declaration found =>
      exact continuation.consumption_allocation declared env.supply.allocate.1 [] env.supply.allocate.2
    case move after place value taken =>
      cases code with | expression checked =>
        cases checked with | move selected path selection ready mask context =>
          obtain ⟨value, producedAfter, _, _, produced, _, _, _, _, _, _, _, _, retained⟩ :=
            AddressedEnvironment.take.progress store selected path selection ready
          cases Option.some.inj (taken.symm.trans produced)
          apply continuation.consumption_frame declared (AddressedEnvironment.take.consumption_frame taken)
          intro scope states realized older
          exact (retained scope states realized (by intro same; have := congrArg ActivationId.index same; omega)).2
    case bindResult stack name slot body value =>
      let inputs : List BindingInput := [⟨name, slot, value⟩]
      cases continuation with | cons frame tail =>
        have outerDeclared := frame.declares declared
        cases frame
        change AddressedEnvironment.ConsumptionFrame program context.slots (continuationEnvironment env stack)
          (continuationEnvironment ((Frame.scope inputs.length).environment (env.extend inputs)) stack)
        rw [Frame.scope_extension]
        exact tail.consumption_allocation outerDeclared env.activation inputs env.supply
    case callInputs declaration values inputs prepared =>
      cases continuation with | cons frame tail =>
        have outerDeclared := frame.declares declared
        cases frame
        exact tail.consumption_allocation outerDeclared env.supply.allocate.1 inputs env.supply.allocate.2
    case selectedPattern bindings stack values arms body selected =>
      cases continuation with | cons frame tail =>
        have outerDeclared := frame.declares declared
        cases frame
        change AddressedEnvironment.ConsumptionFrame program context.slots (continuationEnvironment env stack)
          (continuationEnvironment ((Frame.scope bindings.length).environment (env.extend bindings)) stack)
        rw [Frame.scope_extension]
        exact tail.consumption_allocation outerDeclared env.activation bindings env.supply
    case scope after stack count value exited =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          cases frame with | scope locals discard joined =>
            obtain ⟨producedAfter, produced, _, _, _, _, _, retained, preserved⟩ :=
              AddressedEnvironment.exitScope.progress store locals.length
            cases Option.some.inj (exited.symm.trans produced)
            have scopeEq : after.scope = ((Frame.scope locals.length).environment env).scope := by
              obtain ⟨heap, _, same⟩ := Option.map_eq_some_iff.mp exited
              cases same
              rfl
            refine tail.consumption_frame (before := (Frame.scope locals.length).environment env) (after := after)
              ⟨_, store.drop locals.length, by simpa [FlowContext.slots] using joined.slots.symm⟩ (.of_cells scopeEq ?_) ?_
            · intro identity member
              apply preserved identity
              have maps := congrArg AddressedScope.bindings scopeEq
              change after.bindings = env.bindings.drop locals.length at maps
              rw [maps]
              exact member
            · intro scope states realized older
              change scope.activation.index < env.activation.index at older
              exact (retained scope states realized (by intro same; have := congrArg ActivationId.index same; omega)).2
    case assignResult after stack place rest value written =>
      cases code with | result resident =>
        have original := continuation
        cases continuation with | cons frame tail =>
          cases frame with | assign selected path writable selection discard mask context checked =>
            obtain ⟨producedAfter, _, _, produced, _, _, _, _, _, _, _, _, retained⟩ :=
              AddressedEnvironment.write.progress store selected path resident
            cases Option.some.inj (written.symm.trans produced)
            have selectedSlot := congrArg (Option.map BindingState.slot) selected
            rw [← lookup.map] at selectedSlot
            apply original.consumption_frame declared
              (AddressedEnvironment.write.consumption_frame declared selectedSlot writable written)
            intro scope states realized older
            exact (retained scope states realized (by intro same; have := congrArg ActivationId.index same; omega)).2
    case restore after caller stack value restored =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          cases frame with | restore locals discard callerTyped callerIssued older =>
            obtain ⟨producedAfter, produced, _, activation, bindings, _, _, _, preserved, retained⟩ :=
              AddressedEnvironment.restore.progress store callerTyped (by
                intro same; have := congrArg ActivationId.index same; omega)
            cases Option.some.inj (restored.symm.trans produced)
            have scopeEq : after.scope = caller := by
              simp only [AddressedEnvironment.scope, activation, bindings]
            refine tail.consumption_frame (before := (Frame.restore caller).environment env) (after := after)
              ⟨_, callerTyped, rfl⟩ (.of_cells scopeEq preserved) ?_
            intro scope states realized oldest
            change scope.activation.index < caller.activation.index at oldest
            exact (retained scope states realized (by intro same; have := congrArg ActivationId.index same; omega)).2

theorem ConfigurationTyped.consumption_run {context : FlowContext} {result : ResultType} {before after : Configuration}
    (checkedProgram : program.Checked) (typed : ConfigurationTyped program context result before)
    (run : Run program before after) :
    AddressedEnvironment.ConsumptionFrame program context.slots before.outerEnvironment after.outerEnvironment := by
  induction run with
  | refl state => exact .refl _ _
  | step head tail ih => exact (typed.consumption_step head).trans (ih (typed.preservation checkedProgram head))


/-- Actual copy reads and all modeled disposal sites respect the same structural
owned-use authority. Scope retirement also preserves newest-owner-first order.
These are current-state facts, not future readiness. -/
def Configuration.OwnershipSafe (program : Program) (state : Configuration) : Prop :=
  match state.control, state.continuation with
  | .expression (.read place), _ =>
      BindingMap.CopySafe program state.environment.heap state.environment.bindings place
  | .result _, .scope count :: _ =>
      BindingMap.Disposable program state.environment.heap (List.take count state.environment.bindings) ∧
        (BindingMap.releaseOrder (List.take count state.environment.bindings)).Pairwise
          (fun newer older => older.index < newer.index)
  | .result _, .restore _ :: _ =>
      BindingMap.Disposable program state.environment.heap state.environment.bindings ∧
        state.environment.bindings.releaseOrder.Pairwise (fun newer older => older.index < newer.index)
  | .result _, .assign place _ :: _ =>
      BindingMap.ReplacementSafe program state.environment.heap state.environment.bindings place
  | .result aggregate, .project home key :: _ => aggregate.ProjectionCleanupSafe program home key
  | .result value, .sequence _ :: _ => ∃ type, (PartialValue.resident value).Disposable program type
  | .results values, .patterns home arms :: _ =>
      ∀ bindings body, selectArm (argumentValue values) arms = some (bindings, body) →
        ∃ subject locals pattern front back,
          ValueHasType program (argumentValue values) subject ∧
          PatternType program home pattern subject locals ∧
          arms = front ++ (pattern, body) :: back ∧
          (∀ earlier ∈ front, earlier.1.matchValue (argumentValue values) = none) ∧
          pattern.matchValue (argumentValue values) = some bindings
  | _, _ => True

theorem ConfigurationTyped.ownership_safe {context : FlowContext} {result : ResultType}
    {state : Configuration} (typed : ConfigurationTyped program context result state) :
    state.OwnershipSafe program := by
  cases typed with
  | intro store issued code continuation =>
    cases code <;> try trivial
    case expression checked =>
      cases checked <;> try trivial
      case read =>
        exact store.copy_safe (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
    case result resident =>
      cases continuation
      · trivial
      case cons frame tail =>
        cases frame <;> try trivial
        case scope locals discard joined =>
          exact ⟨(store.take locals.length).disposable (by simpa using discard),
            BindingMap.releaseOrder_decreasing _ (store.take locals.length).addresses_distinct⟩
        case restore =>
          exact ⟨store.disposable (by assumption), BindingMap.releaseOrder_decreasing _ store.addresses_distinct⟩
        case assign =>
          exact store.replacement_safe (by assumption) (by assumption) (by assumption) (by assumption)
        case project =>
          exact ProjectionType.cleanup_safe (by assumption) resident (by assumption) (by assumption)
        case sequence =>
          exact ⟨_, Initialization.Disposable.realizes (.permitted (by assumption)) (.resident resident)⟩
    case results residents =>
      cases continuation
      · trivial
      case cons frame tail =>
        cases frame <;> try trivial
        case patterns nonempty covered checked =>
          intro bindings body selected
          obtain ⟨locals, _, _, pattern, _, _, _, _, _, _, _, _, patternTyped, matched, front, back, split, missed⟩ :=
            checked.selected residents.argument selected
          exact ⟨_, locals, pattern, front, back, residents.argument, patternTyped, split, missed, matched⟩
/-- Recover ownership authority for the actual first matching clause, not an
arbitrary clause with the same body or the same produced binding pack. -/
theorem Configuration.OwnershipSafe.selected_pattern {environment : Environment} {values : List Value}
    {stack : List Frame} {front back : List (Pattern × Expr)} {pattern : Pattern} {body : Expr}
    {patternHome : Module} {bindings : List BindingInput}
    (safe : (⟨environment, .results values, .patterns patternHome (front ++ (pattern, body) :: back) :: stack⟩ : Configuration).OwnershipSafe program)
    (missed : ∀ earlier ∈ front, earlier.1.matchValue (argumentValue values) = none)
    (matched : pattern.matchValue (argumentValue values) = some bindings) :
    ∃ subject locals, ValueHasType program (argumentValue values) subject ∧
      PatternType program patternHome pattern subject locals := by
  have selected : selectArm (argumentValue values) (front ++ (pattern, body) :: back) = some (bindings, body) := by
    rw [selectArm.skip_missed _ _ _ missed]
    simp only [selectArm, matched]
  obtain ⟨subject, locals, actual, actualFront, actualBack, resident, typed, split, skipped, found⟩ :=
    safe bindings body selected
  have same := selectArm.first_unique split missed skipped
    (by simp only [matched, ne_eq, reduceCtorEq, not_false_eq_true])
    (by simp only [found, ne_eq, reduceCtorEq, not_false_eq_true])
  have patternSame : pattern = actual := congrArg Prod.fst same
  exact ⟨subject, locals, resident, patternSame.symm ▸ typed⟩

/-- Source-prefix ownership safety constrains every actual lexical retirement,
including its intermediate heap transitions and strict acquisition order. -/
theorem Configuration.OwnershipSafe.scope_retirement {before : Environment} {after : Configuration}
    {value : Value} {count : Nat} {stack : List Frame}
    (safe : (⟨before, .result value, .scope count :: stack⟩ : Configuration).OwnershipSafe program)
    (step : Step program ⟨before, .result value, .scope count :: stack⟩ after)
    {front back : List StorageId} {identity : StorageId}
    (split : BindingMap.releaseOrder (List.take count before.bindings) = front ++ identity :: back) :
    ∃ middle next, before.heap.retireMany front = some middle ∧
      middle.retire identity = some next ∧ next.retireMany back = some after.environment.heap ∧
      (∀ older ∈ back, older.index < identity.index) ∧
      ∃ cell, middle.read identity = some cell ∧ cell.resident.Disposable program cell.type := by
  cases step with
  | scope exited =>
    obtain ⟨heap, released, same⟩ := Option.map_eq_some_iff.mp exited
    cases same
    exact BindingMap.Disposable.release_prefix safe.1 released safe.2 split

/-- Function return consumes the same release producer as lexical scope exit;
parameter-list order cannot override actual newest-owner-first retirement. -/
theorem Configuration.OwnershipSafe.return_retirement {before : Environment} {after : Configuration}
    {value : Value} {caller : AddressedScope} {stack : List Frame}
    (safe : (⟨before, .result value, .restore caller :: stack⟩ : Configuration).OwnershipSafe program)
    (step : Step program ⟨before, .result value, .restore caller :: stack⟩ after)
    {front back : List StorageId} {identity : StorageId}
    (split : before.bindings.releaseOrder = front ++ identity :: back) :
    ∃ middle next, before.heap.retireMany front = some middle ∧
      middle.retire identity = some next ∧ next.retireMany back = some after.environment.heap ∧
      (∀ older ∈ back, older.index < identity.index) ∧
      ∃ cell, middle.read identity = some cell ∧ cell.resident.Disposable program cell.type := by
  cases step with
  | restore restored =>
    obtain ⟨heap, released, same⟩ := Option.map_eq_some_iff.mp restored
    cases same
    exact BindingMap.Disposable.release_prefix safe.1 released safe.2 split

/-- Every retained scope is realized in the current heap, not merely the active
scope or the outermost caller. Traversing frames does not execute pending code. -/
theorem ContinuationTyped.live_scopes {before : Environment} {current final : FlowContext}
    {input result : ResultType} {stack : List Frame}
    (typed : ContinuationTyped program before.heap before.supply before.activation current input stack final result)
    (store : before.Declares program current.slots) :
    ∀ front back, stack = front ++ back →
      ∀ identity ∈ (continuationEnvironment before front).bindings.map Prod.snd,
        ∃ cell, before.heap.read identity = some cell := by
  intro front
  induction front generalizing before current input stack with
  | nil =>
    intro back same identity member
    obtain ⟨states, residents, _⟩ := store
    exact residents.live identity member
  | cons frame front ih =>
    intro back same identity member
    subst stack
    cases typed with
    | cons head tail => exact ih tail (head.declares store) back rfl identity member

theorem ConfigurationTyped.live_scopes {context result state}
    (typed : ConfigurationTyped program context result state) :
    ∀ front back, state.continuation = front ++ back →
      ∀ identity ∈ (continuationEnvironment state.environment front).bindings.map Prod.snd,
        ∃ cell, state.environment.heap.read identity = some cell := by
  cases typed with
  | intro store issued code continuation =>
    exact continuation.live_scopes ⟨_, store, code.slots.symm⟩

/-- Retired identities cannot remain in any active or retained caller binding
map of a well-typed machine configuration. This is not reference-loan typing. -/
theorem ConfigurationTyped.retired_not_retained {context result state} {identity : StorageId}
    (typed : ConfigurationTyped program context result state)
    (retired : state.environment.heap.Retired identity)
    {front back : List Frame} (split : state.continuation = front ++ back) :
    identity ∉ (continuationEnvironment state.environment front).bindings.map Prod.snd := by
  intro member
  obtain ⟨cell, found⟩ := typed.live_scopes front back split identity member
  rw [retired.2] at found
  cases found

/-- Maximal behavior starts from the actual typed control and continuation,
including partially evaluated calls and pending caller restoration. -/
theorem ConfigurationTyped.behavior (checkedProgram : program.Checked)
    {context : FlowContext} {type : Ty} {before : Configuration}
    (typed : ConfigurationTyped program context (.one type) before) :
    (∃ after value, Run program before ⟨after, .result value, []⟩ ∧
      ValueHasType program value type ∧
      BindingMap.Typed program after.heap after.activation after.bindings context ∧
      AddressedEnvironment.ConsumptionFrame program context.slots before.outerEnvironment after ∧
      (⟨after, .result value, []⟩ : Configuration).OwnershipSafe program ∧
      before.ExternalFrame ⟨after, .result value, []⟩ ∧
      ∀ identity, before.environment.heap.next ≤ identity.index → identity.index < after.heap.next →
        after.heap.Retired identity) ∨
    (∃ trace, InfiniteRun program before trace ∧
      ∀ index, ConfigurationTyped program context (.one type) (trace index) ∧
        AddressedEnvironment.ConsumptionFrame program context.slots before.outerEnvironment (trace index).outerEnvironment ∧
        (trace index).OwnershipSafe program ∧
        before.ExternalFrame (trace index) ∧
        ∀ identity, before.environment.heap.next ≤ identity.index →
          ∀ cell, (trace index).environment.heap.read identity = some cell →
            ¬ (trace index).Untracked identity) := by
  rcases Run.terminal_or_infinite before
      (fun _ run => (typed.run checkedProgram run).progress) with ⟨state, run, done⟩ | ⟨trace, infinite⟩
  · left
    have current := typed.run checkedProgram run
    obtain ⟨after, value, same, store, _, resident⟩ := current.normal_form done
    subst state
    refine ⟨after, value, run, resident, store, typed.consumption_run checkedProgram run,
      current.ownership_safe, run.external_frame, run.return_retires_all ?_⟩
    intro identity member
    obtain ⟨cell, found⟩ := typed.live_scopes before.continuation [] (by simp) identity member
    exact before.environment.heap.bounded _ _ found
  · right
    refine ⟨trace, infinite, ?_⟩
    intro index
    have run := infinite.prefix index
    have current := typed.run checkedProgram run
    exact ⟨current, typed.consumption_run checkedProgram run, current.ownership_safe, run.external_frame,
      fun _ fresh _ live => run.allocated_tracked fresh live⟩


end Grounded

