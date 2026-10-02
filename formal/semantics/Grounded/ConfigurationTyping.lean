import Grounded.Checking
import Grounded.Execution

/-! Flow checking supplies sound masks for each continuation. Arm-local masks
are approximated at scope retirement; retained callers are realized in the current heap. -/
namespace Grounded

inductive ResultType where
  | one (type : Ty)
  | many (types : List Ty)

/-- Each pending resident has structural zero-use authority. Shell markers
retain that authority without retaining runtime copies of their children. -/
inductive DisposalTask.Safe (program : Program) : DisposalTask → Prop where
  | enter {value type} (typed : ValueHasType program value type)
      (allowed : UsePermitted program.data .discard type) : Safe program (.enter value)
  | release {value type} (typed : ValueHasType program value type)
      (allowed : UsePermitted program.data .discard type) : Safe program (.release value.head)
  | tupleShell {head tail first rest}
      (allowed : (PartialValue.tuple head tail).Disposable program (.tuple first rest)) :
      Safe program (.release .tuple)
  | nominalShell {identity tag fields}
      (allowed : (PartialValue.nominal identity tag fields).Disposable program (.nominal identity)) :
      Safe program (.release (.nominal identity tag))
/-- Cleanup has zero-use authority under every valid typing of the actual
resident. A different annotation cannot disguise an exact-linear owner. -/
theorem DisposalTask.Safe.zero_use {program : Program} {value : Value} {type : Ty}
    {principal : Principal} (safe : DisposalTask.Safe program (.enter value))
    (resident : ValueHasType program value type) (classified : type.HasPrincipal program.data principal) :
    principal.Permits 0 := by
  cases safe with
  | enter typed allowed =>
    have permission := typed.use_permission resident allowed
    exact ((classified .discard).mp permission) 0 (by simp)
theorem DisposalTask.Safe.expand {program : Program} {value : Value}
    (safe : DisposalTask.Safe program (.enter value)) :
    ∀ task ∈ DisposalTask.expand value, DisposalTask.Safe program task := by
  cases safe with
  | enter typed allowed =>
    intro task member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨child, childMember, rfl⟩ := List.mem_map.mp member
      obtain ⟨type, resident, permission⟩ := typed.children_disposable allowed (List.mem_reverse.mp childMember)
      exact .enter resident permission
    · cases List.mem_singleton.mp member
      exact .release typed allowed

private theorem PartialValuesTyped.empty_permissions {program : Program} {values types states}
    (typed : PartialValuesTyped program values types states)
    (empty : ∀ state ∈ states, state.Empty) : InitializationsDisposable program.data types states := by
  induction types generalizing values states with
  | nil => cases typed; exact .nil
  | cons type types ih =>
    cases typed with
    | cons head tail => exact .cons (.empty (empty _ (by simp))) (ih tail (fun state member => empty state (by simp [member])))

private theorem PartialValuesTyped.whole_permissions {program : Program} {values types states}
    (typed : PartialValuesTyped program values types states)
    (allowed : ∀ type ∈ types, UsePermitted program.data .discard type) :
    InitializationsDisposable program.data types states := by
  induction types generalizing values states with
  | nil => cases typed; exact .nil
  | cons type types ih =>
    cases typed with
    | cons head tail => exact .cons (.permitted (allowed _ (by simp))) (ih tail (fun type member => allowed type (by simp [member])))

/-- Residual permission authorizes every work item produced from actual partial
storage. Empty slots produce no work; opaque fields use structural permission. -/
theorem PartialValue.Disposable.disposalTasks {program : Program} {value : PartialValue} {type : Ty}
    (disposable : value.Disposable program type) :
    ∀ task ∈ value.disposalTasks, DisposalTask.Safe program task := by
  obtain ⟨state, typed, permission⟩ := disposable
  induction typed using PartialValue.Typed.rec
    (motive_2 := fun values types states _ => InitializationsDisposable program.data types states →
      ∀ task ∈ partialDisposalTasks values, DisposalTask.Safe program task) with
  | hole type => simp [PartialValue.disposalTasks]
  | resident typed =>
    intro task member
    simp only [PartialValue.disposalTasks] at member
    cases List.mem_singleton.mp member
    exact .enter typed (Initialization.Disposable.present_iff.mp permission)
  | @tuple head tail first rest headState tailStates headTyped tailTyped headIH tailIH =>
    have parts : InitializationsDisposable program.data (first :: rest) (headState :: tailStates) := by
      cases permission with
      | empty absent =>
        simp only [Initialization.Empty] at absent
        exact (PartialValuesTyped.cons headTyped tailTyped).empty_permissions absent.2
      | permitted allowed =>
        cases allowed with
        | tuple first rest => exact (PartialValuesTyped.cons headTyped tailTyped).whole_permissions (by simpa using And.intro first rest)
      | tuple head tail => exact .cons head tail
    intro task member
    simp only [PartialValue.disposalTasks, partialDisposalTasks] at member
    rcases List.mem_append.mp member with member | member
    · cases parts with
      | cons first rest =>
        rcases List.mem_append.mp member with member | member
        · exact tailIH rest task member
        · exact headIH first task member
    · cases List.mem_singleton.mp member
      exact .tupleShell ⟨_, .tuple headTyped tailTyped, permission⟩
  | @nominal identity tag declaration schema values states declared chosen finite residents ih =>
    have parts : InitializationsDisposable program.data (schema.residents.map Field.type) states := by
      cases permission with
      | empty absent =>
        simp only [Initialization.Empty] at absent
        exact residents.empty_permissions absent.2
      | permitted allowed =>
        cases allowed with
        | nominal found restriction fields =>
          cases Option.some.inj (declared.symm.trans found)
          apply residents.whole_permissions
          intro type member
          obtain ⟨field, fieldMember, rfl⟩ := List.mem_map.mp member
          apply fields _ ?_ field fieldMember
          cases shape : declaration.shape with
          | «structure» fs =>
            cases tag <;> simp [DataDecl.constructor, shape] at chosen
            subst schema
            simp [DataDecl.schemas, shape]
          | enumeration variants nonExhaustive =>
            cases tag <;> simp only [DataDecl.constructor, shape] at chosen
            · contradiction
            · simpa [DataDecl.schemas, shape] using List.mem_of_getElem? chosen
      | nominal found restriction fields =>
        cases Option.some.inj (declared.symm.trans found)
        exact fields tag schema chosen
    intro task member
    simp only [PartialValue.disposalTasks] at member
    rcases List.mem_append.mp member with member | member
    · exact ih parts task member
    · cases List.mem_singleton.mp member
      exact .nominalShell ⟨_, .nominal declared chosen finite residents, permission⟩
  | uncertain typed ih => exact ih (.permitted (Initialization.Disposable.maybe_iff.mp permission))
  | nil => rename_i permission task member; simp [partialDisposalTasks] at member
  | cons head tail headIH tailIH =>
    rename_i permission task member
    simp only [partialDisposalTasks] at member
    cases permission with
    | cons headPermission tailPermission =>
      rcases List.mem_append.mp member with member | member
      · exact tailIH tailPermission task member
      · exact headIH headPermission task member
inductive ControlTyped (program : Program) (before : FlowContext) : Control → ResultType → FlowContext → Prop where
  | expression {home expression type after} (checked : HasType program home before expression type after) :
      ControlTyped program before (.expression expression) (.one type) after
  | arguments {home expressions types after} (checked : HasTypes program home before expressions types after) :
      ControlTyped program before (.arguments expressions) (.many types) after
  | result {value type} (resident : ValueHasType program value type) :
      ControlTyped program before (.result value) (.one type) before
  | results {values types} (residents : ValuesHaveTypes program values types) :
      ControlTyped program before (.results values) (.many types) before
  | cleanup {pending rest result after}
      (safe : ∀ task ∈ pending, DisposalTask.Safe program task)
      (checked : ControlTyped program before rest result after) :
      ControlTyped program before (.cleanup pending rest) result after
  | install {home restored after place type result rest state updated available value}
      (resident : ValueHasType program value type)
      (selected : lookup place.root before = some state)
      (path : PathType program home state.slot.type place.fields type)
      (writable : state.slot.mutable = true)
      (selection : state.initialization.selectFields program state.slot.type place.fields = some available)
      (discard : available.Disposable program.data type)
      (mask : state.initialization.writeFields program state.slot.type place.fields .present = some updated)
      (context : replaceBinding place.root { state with initialization := updated } before = some restored)
      (checked : HasType program home restored rest result after) :
      ControlTyped program before (.install home place value rest) (.one result) after

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
  | retire {context : FlowContext} {result index}
      (inside : index < context.length)
      (discard : ∀ binding, context[index]? = some binding → binding.2.Disposable program.data) :
      FrameTyped program heap supply activation context (.one result) (.retire index) (context.eraseIdx index) (.one result)
  | assign {home before restored after place type result rest state updated available}
      (selected : lookup place.root before = some state)
      (path : PathType program home state.slot.type place.fields type)
      (writable : state.slot.mutable = true)
      (selection : state.initialization.selectFields program state.slot.type place.fields = some available)
      (discard : available.Disposable program.data type)
      (mask : state.initialization.writeFields program state.slot.type place.fields .present = some updated)
      (context : replaceBinding place.root { state with initialization := updated } before = some restored)
      (checked : HasType program home restored rest result after) :
      FrameTyped program heap supply activation before (.one type) (.assign home place rest) after (.one result)
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
  | @intro current next input environment control stack store issued code continuation =>
    cases code with
    | @cleanup pending rest result after safe checked =>
      right
      cases pending with
      | nil => exact ⟨_, .cleanupDone⟩
      | cons task pending => cases task with
        | enter value => exact ⟨_, .cleanupEnter⟩
        | release head => exact ⟨_, .cleanupRelease⟩
    | install resident selected path writable selection discard mask context checked =>
      obtain ⟨after, _, _, written, _⟩ := AddressedEnvironment.write.progress store selected path resident
      exact .inr ⟨_, .install written⟩
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
          by_cases empty : List.take locals.length environment.bindings = []
          · exact ⟨_, .scope empty⟩
          · obtain ⟨index, entry, chosen, _, member, _⟩ := BindingMap.release_next _ _ (List.take_prefix _ _) empty
            obtain ⟨cell, found⟩ := (store.take locals.length).live _ (List.mem_map_of_mem (f := Prod.snd) member)
            exact ⟨_, .scopeOwner chosen found⟩
        | @retire current result index inside discard =>
          have length := congrArg List.length store.keys
          simp only [List.length_map] at length
          have bound : index < environment.bindings.length := by omega
          have selected := List.getElem?_eq_getElem bound
          obtain ⟨after, retired, _⟩ := AddressedEnvironment.retireBinding.progress store selected
          exact ⟨_, .retire retired⟩
        | assign selected path writable selection discard mask context checked =>
          obtain ⟨old, _, selected, _⟩ := (store.replacement_safe selected path selection discard).selection
          exact ⟨_, .assignResult selected⟩
        | tupleHead checked => exact ⟨_, .tupleHead⟩
        | project discard mask projection =>
          obtain ⟨value, remainder, selected, _⟩ := projection.take_progress resident mask discard
          exact ⟨_, .projectResult selected⟩
        | restore locals discard retained callerIssued older =>
          by_cases empty : environment.bindings = []
          · exact ⟨_, .restore empty⟩
          · obtain ⟨index, entry, chosen, _, member, _⟩ := BindingMap.release_next _ _ ⟨[], List.append_nil _⟩ empty
            obtain ⟨cell, found⟩ := store.live _ (List.mem_map_of_mem (f := Prod.snd) member)
            exact ⟨_, .restoreOwner chosen found⟩
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
          cases frame with | sequence discard checked =>
            exact .intro store issued (.cleanup (by simpa using DisposalTask.Safe.enter resident discard) (.expression checked)) tail
    | cleanupEnter =>
      cases code with | cleanup safe checked =>
        refine .intro store issued (.cleanup ?_ checked) continuation
        intro task member
        rcases List.mem_append.mp member with member | member
        · exact (safe _ (by simp)).expand task member
        · exact safe task (by simp [member])
    | cleanupRelease =>
      cases code with | cleanup safe checked =>
        exact .intro store issued (.cleanup (fun task member => safe task (by simp [member])) checked) continuation
    | cleanupDone =>
      cases code with | cleanup safe checked => exact .intro store issued checked continuation
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
            have empty : locals = [] := by
              have length := congrArg List.length store.keys
              have zero := congrArg List.length exited
              simp only [List.length_map, List.length_append, List.length_take, List.length_nil] at length zero
              exact List.eq_nil_of_length_eq_zero (by omega)
            subst locals
            exact .intro (store.approximate joined) issued (.result resident) tail
    | scopeOwner chosen found =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          cases frame with | scope locals discard joined =>
            have inside := BindingMap.nextRelease.in_prefix (List.take_prefix _ _) chosen
            simp only [List.length_take] at inside
            have localIndex := Nat.lt_of_lt_of_le inside (Nat.min_le_left _ _)
            have safe := (store.take locals.length).disposable (by simpa using discard)
            obtain ⟨cell, actual, permission⟩ := safe _ (BindingMap.nextRelease.member chosen)
            cases Option.some.inj (actual.symm.trans found)
            refine .intro store issued (.cleanup permission.disposalTasks (.result resident))
              (.cons (.retire (by simp only [List.length_append]; omega) ?_) ?_)
            · intro binding selected
              rw [List.getElem?_append_left localIndex] at selected
              exact discard binding (List.mem_of_getElem? selected)
            · rw [List.eraseIdx_append_of_lt_length localIndex]
              have length := List.length_eraseIdx_of_lt localIndex
              rw [← length]
              exact .cons (.scope _ (fun binding member => discard binding (List.mem_of_mem_eraseIdx member)) joined) tail
    | restoreOwner chosen found =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          cases frame with | restore locals discard callerTyped callerIssued older =>
            obtain ⟨entry, selected, matching⟩ := BindingMap.nextRelease.binding chosen
            obtain ⟨state, cell, source, actual, _⟩ := store.index selected
            have inside := (List.getElem?_eq_some_iff.mp source).1
            obtain ⟨cell, actual, permission⟩ := store.disposable discard _ (BindingMap.nextRelease.member chosen)
            cases Option.some.inj (actual.symm.trans found)
            exact .intro store issued (.cleanup permission.disposalTasks (.result resident))
              (.cons (.retire inside (fun binding selected => discard binding (List.mem_of_getElem? selected)))
                (.cons (.restore _ (fun binding member => discard binding (List.mem_of_mem_eraseIdx member)) callerTyped callerIssued older) tail))
    | retire operation =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          cases frame with | retire inside discard =>
            obtain ⟨entry, selected, _, _, _⟩ := AddressedEnvironment.retireBinding.eq_some_iff.mp operation
            obtain ⟨next, produced, _, _, _, activation, supply, _, nextTyped, _, callers⟩ :=
              AddressedEnvironment.retireBinding.progress store selected
            cases Option.some.inj (operation.symm.trans produced)
            refine .intro nextTyped (by rw [supply, activation]; exact issued) (.result resident) ?_
            rw [supply, activation]
            apply tail.transport (fun _ previous => previous)
            intro caller states callerTyped older
            exact (callers caller states callerTyped (by
              intro same
              have equal := congrArg ActivationId.index same
              simp only [Frame.activation] at older
              omega)).1
    | assign =>
      cases code with | expression checked =>
        cases checked with | assign resident selected path writable selection discard mask context rest =>
          exact .intro store issued (.expression resident)
            (.cons (.assign selected path writable selection discard mask context rest) continuation)
    | assignResult actual =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          cases frame with | assign selected path writable selection discard mask context checked =>
            obtain ⟨old, _, produced, permission⟩ := (store.replacement_safe selected path selection discard).selection
            cases Option.some.inj (actual.symm.trans produced)
            exact .intro store issued (.cleanup permission.disposalTasks
              (.install resident selected path writable selection discard mask context checked)) tail
    | install written =>
      cases code with
      | install resident selected path writable selection discard mask context checked =>
            obtain ⟨next, nextMask, nextContext, produced, maskWritten, contextWritten, nextTyped,
              _, scope, supply, _, _, retained⟩ := AddressedEnvironment.write.progress store selected path resident
            cases Option.some.inj (mask.symm.trans maskWritten)
            cases Option.some.inj (context.symm.trans contextWritten)
            cases Option.some.inj (written.symm.trans produced)
            have activation := congrArg AddressedScope.activation scope
            simp only [AddressedEnvironment.scope] at activation
            refine .intro nextTyped (by rw [supply, activation]; exact issued) (.expression checked) ?_
            rw [supply, activation]
            apply continuation.transport (fun _ previous => previous)
            intro caller states callerTyped older
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
            obtain ⟨value, remainder, found, valueTyped, _, _, disposable⟩ := projection.take_progress resident mask discard
            cases Option.some.inj (selected.symm.trans found)
            exact .intro store issued (.cleanup disposable.disposalTasks (.result valueTyped)) tail
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
            exact .intro callerTyped callerIssued (.result resident) tail
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
    | @selectedPattern patternHome env bindings stack values arms body selected =>
      cases code with | results residents =>
        cases continuation with | cons frame tail =>
          cases frame with | patterns nonempty covered checked =>
            obtain ⟨locals, localsAfter, branchAfter, pattern, _, inputsTyped, slots, discard, bodyTyped, localSlots, distinct, joined, patternTyped, matched, _⟩ :=
              checked.selected residents.argument selected
            obtain ⟨entered, _, _, retained⟩ := AddressedEnvironment.extend.typed store inputsTyped (by
              rw [← slots] at distinct
              simpa only [FlowContext.slots, List.map_append, List.map_map, Function.comp_def] using distinct)
            have states := congrArg initializedContext slots
            simp only [initializedContext, List.map_map, Function.comp_def] at states
            change List.map BindingInput.state _ = initializedContext locals at states
            rw [states] at entered
            have safe : ∀ task ∈ bindings.discarded.map DisposalTask.enter, DisposalTask.Safe program task := by
              intro task member
              obtain ⟨resident, included, rfl⟩ := List.mem_map.mp member
              obtain ⟨type, typed, allowed⟩ := patternTyped.discarded residents.argument matched resident included
              exact .enter typed allowed
            refine .intro entered issued (.cleanup safe (.expression bodyTyped)) (.cons ?_
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

/-- The global invariant exposes current disposal authority at every reached
cleanup state; it does not rely on successful future destruction. -/
theorem ConfigurationTyped.cleanup_safe {context result environment pending rest stack}
    (typed : ConfigurationTyped program context result ⟨environment, .cleanup pending rest, stack⟩) :
    ∀ task ∈ pending, DisposalTask.Safe program task := by
  cases typed with
  | intro store issued code continuation => cases code with | cleanup safe checked => exact safe
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

/-- One actual retirement inside the local prefix preserves the remaining
scope continuation, including its decremented local count and retained callers. -/
theorem ConfigurationTyped.retire_scope {context : FlowContext} {result : ResultType}
    {before after : Environment} {value : Value} {count index : Nat} {stack : List Frame}
    {entry : BindingId × StorageId}
    (typed : ConfigurationTyped program context result ⟨before, .result value, .scope count :: stack⟩)
    (selected : before.bindings[index]? = some entry) (inside : index < count)
    (retired : before.retireBinding index = some after) :
    ConfigurationTyped program context result ⟨after, .result value, .scope (count - 1) :: stack⟩ := by
  cases typed with | intro store issued code continuation =>
    cases code with | result resident =>
      cases continuation with | cons frame tail =>
        cases frame with | scope locals discard joined =>
          obtain ⟨next, produced, _, _, _, activation, supply, _, nextTyped, _, callers⟩ :=
            AddressedEnvironment.retireBinding.progress store selected
          cases Option.some.inj (retired.symm.trans produced)
          rw [List.eraseIdx_append_of_lt_length inside] at nextTyped
          have length := List.length_eraseIdx_of_lt inside
          rw [← length]
          refine .intro nextTyped (by rw [supply, activation]; exact issued) (.result resident)
            (.cons (.scope (locals.eraseIdx index) (fun binding member => discard binding (List.mem_of_mem_eraseIdx member)) joined) ?_)
          rw [supply, activation]
          apply tail.transport (fun _ previous => previous)
          intro caller states callerTyped older
          exact (callers caller states callerTyped (by
            intro same
            have equal := congrArg ActivationId.index same
            simp only [Frame.activation] at older
            omega)).1

/-- A typed nonempty scope constructs the canonical next retirement and its
fully typed remaining continuation, without a successful operation premise. -/
theorem ConfigurationTyped.scope_next {context : FlowContext} {result : ResultType}
    {current : Environment} {value : Value} {count : Nat} {stack : List Frame}
    (typed : ConfigurationTyped program context result ⟨current, .result value, .scope count :: stack⟩) :
    count = 0 ∨ ∃ (index : Nat) (entry : BindingId × StorageId) (next : Environment),
      BindingMap.nextRelease (List.take count current.bindings) current.bindings = some (index, entry.2) ∧
      index < count ∧ current.retireBinding index = some next ∧
      next.exitScope (count - 1) = current.exitScope count ∧
      ConfigurationTyped program context result ⟨next, .result value, .scope (count - 1) :: stack⟩ := by
  have original := typed
  cases typed with | intro store issued code continuation =>
    cases code with | result resident =>
      cases continuation with | cons frame tail =>
        cases frame with | scope locals discard joined =>
          by_cases empty : locals.length = 0
          · exact .inl empty
          · have length := congrArg List.length store.keys
            simp only [List.length_map] at length
            have nonempty : List.take locals.length current.bindings ≠ [] := by
              intro absent
              have short := congrArg List.length absent
              simp only [List.length_take, List.length_nil] at short
              simp only [List.length_append] at length
              omega
            obtain ⟨index, entry, chosen, selected, _, first⟩ := BindingMap.release_next _ _
              (List.take_prefix locals.length current.bindings) nonempty
            have inside := BindingMap.nextRelease.in_prefix (List.take_prefix locals.length current.bindings) chosen
            have localIndex : index < locals.length := by
              simp only [List.length_take] at inside
              omega
            obtain ⟨next, produced, _⟩ := AddressedEnvironment.retireBinding.progress store selected
            exact .inr ⟨index, entry, next, chosen, localIndex, produced,
              AddressedEnvironment.exitScope.retireBinding selected localIndex first produced,
              original.retire_scope selected localIndex produced⟩
/-- A typed scope constructs all canonical indexed retirements, preserving its
continuation at every stage and producing exactly the existing batch exit. -/
theorem ConfigurationTyped.scope_retirement_trace {context : FlowContext} {result : ResultType}
    {current : Environment} {value : Value} {count : Nat} {stack : List Frame}
    (typed : ConfigurationTyped program context result ⟨current, .result value, .scope count :: stack⟩) :
    ∃ trace : Nat → Environment,
      trace 0 = current ∧ current.exitScope count = some (trace count) ∧
      (∀ position < count, ∃ (index : Nat) (identity : StorageId),
        BindingMap.nextRelease (List.take (count - position) (trace position).bindings) (trace position).bindings = some (index, identity) ∧
        index < count - position ∧ (trace position).retireBinding index = some (trace (position + 1))) ∧
      (∀ position ≤ count,
        ConfigurationTyped program context result ⟨trace position, .result value, .scope (count - position) :: stack⟩ ∧
        (trace position).exitScope (count - position) = current.exitScope count) := by
  cases count with
  | zero =>
    refine ⟨fun _ => current, rfl, by simp [AddressedEnvironment.exitScope, releaseBindings, BindingMap.releaseOrder, RuntimeHeap.retireMany], ?_, ?_⟩
    · intro position bound
      omega
    · intro position bound
      have zero : position = 0 := by omega
      subst position
      exact ⟨typed, rfl⟩
  | succ count =>
    rcases typed.scope_next with empty | ⟨index, entry, next, chosen, inside, produced, same, nextTyped⟩
    · omega
    · obtain ⟨trace, start, finish, steps, states⟩ := nextTyped.scope_retirement_trace
      refine ⟨(fun position => match position with | 0 => current | position + 1 => trace position), rfl, ?_, ?_, ?_⟩
      · exact same.symm.trans finish
      · intro position bound
        cases position with
        | zero => exact ⟨index, entry.2, chosen, inside, by simpa only [start] using produced⟩
        | succ position => simpa using steps position (by omega)
      · intro position bound
        cases position with
        | zero => exact ⟨typed, rfl⟩
        | succ position =>
          obtain ⟨pointTyped, pointSame⟩ := states position (by omega)
          exact ⟨by simpa using pointTyped, by simpa using pointSame.trans same⟩
termination_by count


/-- Retiring one callee owner preserves the returned payload, the saved caller,
and every older continuation; it does not restore the caller prematurely. -/
theorem ConfigurationTyped.retire_restore {context : FlowContext} {result : ResultType}
    {before after : Environment} {value : Value} {caller : AddressedScope}
    {index : Nat} {entry : BindingId × StorageId} {stack : List Frame}
    (typed : ConfigurationTyped program context result ⟨before, .result value, .restore caller :: stack⟩)
    (selected : before.bindings[index]? = some entry)
    (retired : before.retireBinding index = some after) :
    ConfigurationTyped program context result ⟨after, .result value, .restore caller :: stack⟩ := by
  cases typed with | intro store issued code continuation =>
    cases code with | result resident =>
      cases continuation with | cons frame tail =>
        cases frame with | restore locals discard callerTyped callerIssued older =>
          obtain ⟨next, produced, _, _, _, activation, supply, _, nextTyped, _, callers⟩ :=
            AddressedEnvironment.retireBinding.progress store selected
          cases Option.some.inj (retired.symm.trans produced)
          have different : caller.activation ≠ before.activation := by
            intro same
            have equal := congrArg ActivationId.index same
            omega
          refine .intro nextTyped (by rw [supply, activation]; exact issued) (.result resident)
            (.cons (.restore _
              (fun binding member => discard binding (List.mem_of_mem_eraseIdx member))
              (callers caller _ callerTyped different).1
              (by rw [supply]; exact callerIssued) (by rw [activation]; exact older)) ?_)
          rw [supply]
          apply tail.transport (fun _ previous => previous)
          intro scope states scopeTyped previous
          exact (callers scope states scopeTyped (by
            intro same
            have equal := congrArg ActivationId.index same
            simp only [Frame.activation] at previous
            omega)).1

/-- A returning callee either has no remaining bindings or constructs its next
canonical retirement with a fully preserved return continuation. -/
theorem ConfigurationTyped.restore_next {context : FlowContext} {result : ResultType}
    {current : Environment} {value : Value} {caller : AddressedScope} {stack : List Frame}
    (typed : ConfigurationTyped program context result ⟨current, .result value, .restore caller :: stack⟩) :
    current.bindings = [] ∨ ∃ (index : Nat) (entry : BindingId × StorageId) (next : Environment),
      BindingMap.nextRelease current.bindings current.bindings = some (index, entry.2) ∧
      current.retireBinding index = some next ∧
      next.bindings.releaseOrder = current.bindings.releaseOrder.tail ∧
      next.restore caller = current.restore caller ∧
      ConfigurationTyped program context result ⟨next, .result value, .restore caller :: stack⟩ := by
  by_cases empty : current.bindings = []
  · exact .inl empty
  · have original := typed
    cases typed with | intro store issued code continuation =>
      obtain ⟨index, entry, chosen, selected, _, first⟩ := BindingMap.release_next _ _
        ⟨[], List.append_nil _⟩ empty
      obtain ⟨next, produced, _, _, _, _, _, bindings, _⟩ := AddressedEnvironment.retireBinding.progress store selected
      refine .inr ⟨index, entry, next, chosen, produced, ?_,
        AddressedEnvironment.restore.retireBinding selected first produced caller,
        original.retire_restore selected produced⟩
      rw [bindings]
      exact BindingMap.releaseOrder_eraseIdx selected first


/-- Canonical callee retirement constructs a finite physical trace with one
operation per original binding. Every intermediate state preserves the full
return continuation and the exact original restoration result. -/
theorem ConfigurationTyped.restore_retirement_trace {context : FlowContext} {result : ResultType}
    {current : Environment} {value : Value} {caller : AddressedScope} {stack : List Frame}
    (typed : ConfigurationTyped program context result ⟨current, .result value, .restore caller :: stack⟩) :
    ∃ trace : Nat → Environment,
      trace 0 = current ∧ (trace current.bindings.length).bindings = [] ∧
      (∀ position < current.bindings.length, ∃ (index : Nat) (identity : StorageId),
        BindingMap.nextRelease (trace position).bindings (trace position).bindings = some (index, identity) ∧
        (trace position).retireBinding index = some (trace (position + 1))) ∧
      (∀ position ≤ current.bindings.length,
        ConfigurationTyped program context result ⟨trace position, .result value, .restore caller :: stack⟩ ∧
        (trace position).restore caller = current.restore caller) := by
  rcases typed.restore_next with empty | ⟨index, entry, next, chosen, produced, order, same, nextTyped⟩
  · refine ⟨fun _ => current, rfl, empty, ?_, ?_⟩
    · intro position bound
      simp [empty] at bound
    · intro position bound
      exact ⟨typed, rfl⟩
  · have size := AddressedEnvironment.retireBinding.length_step produced
    obtain ⟨trace, start, finish, steps, states⟩ := nextTyped.restore_retirement_trace
    refine ⟨(fun position => match position with | 0 => current | position + 1 => trace position), rfl, ?_, ?_, ?_⟩
    · simpa only [← size] using finish
    · intro position bound
      cases position with
      | zero => exact ⟨index, entry.2, chosen, by simpa only [start] using produced⟩
      | succ position => exact steps position (by omega)
    · intro position bound
      cases position with
      | zero => exact ⟨typed, rfl⟩
      | succ position =>
        obtain ⟨pointTyped, pointSame⟩ := states position (by omega)
        exact ⟨pointTyped, pointSame.trans same⟩
termination_by current.bindings.length


/-- Every actually executed callee-owned retirement prefix retains the full
return continuation. Membership is checked against the pre-state owner map;
no intermediate caller typing or pending-owner readiness is supplied. -/
theorem ConfigurationTyped.restore_prefix {context : FlowContext} {result : ResultType}
    {current : Environment} {value : Value} {caller : AddressedScope} {stack : List Frame}
    (typed : ConfigurationTyped program context result ⟨current, .result value, .restore caller :: stack⟩)
    {front : List StorageId} {middle : RuntimeHeap StorageCell}
    (owned : ∀ identity ∈ front, identity ∈ current.bindings.map Prod.snd)
    (executed : current.heap.retireMany front = some middle) :
    ConfigurationTyped program context result
      ⟨{ current with heap := middle, bindings := current.bindings.filter fun entry => decide (entry.2 ∉ front) },
        .result value, .restore caller :: stack⟩ := by
  cases typed with | intro store issued code continuation =>
    cases code with | result resident =>
      cases continuation with | cons frame tail =>
        cases frame with | restore locals discard callerTyped callerIssued older =>
          obtain ⟨remaining, subset, retained⟩ := store.retirement_prefix executed
          have callers : ∀ (scope : AddressedScope) states,
              BindingMap.Typed program current.heap scope.activation scope.bindings states →
              scope.activation ≠ current.activation →
              BindingMap.Typed program middle scope.activation scope.bindings states := by
            intro scope states scopeTyped different
            apply scopeTyped.frame
            intro identity member
            apply RuntimeHeap.retireMany_outside executed
            intro retired
            exact (scopeTyped.apart_activations store different identity member) (owned identity retired)
          have different : caller.activation ≠ current.activation := by
            intro same
            have equal := congrArg ActivationId.index same
            omega
          refine .intro retained issued (.result resident)
            (.cons (.restore remaining (fun binding member => discard binding (subset.subset member))
              (callers caller _ callerTyped different) callerIssued older) ?_)
          apply tail.transport (fun _ previous => previous)
          intro scope states scopeTyped previous
          apply callers scope states scopeTyped
          intro same
          have equal := congrArg ActivationId.index same
          simp only [Frame.activation] at previous
          omega


theorem ControlTyped.slots {current next control result}
    (typed : ControlTyped program current control result next) : next.slots = current.slots := by
  induction typed with
  | cleanup safe checked ih => exact ih
  | expression checked => exact checked.slots
  | arguments checked => exact checked.slots
  | result | results => rfl
  | install resident selected path writable selection discard mask context checked =>
    exact checked.slots.trans (replaceBinding.map_same BindingState.slot selected context rfl)

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
  | @retire context result index inside discard =>
    simpa [Frame.environment, Frame.activation, FlowContext.slots, List.eraseIdx_eq_take_drop_succ, List.map_append, List.map_take, List.map_drop] using store.eraseIdx index
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
  | @retire context result index inside discard =>
    simpa [Frame.environment, Frame.activation, FlowContext.slots, List.eraseIdx_eq_take_drop_succ, List.map_append, List.map_take, List.map_drop] using framed.eraseIdx store index
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

/-- Callee retirement preserves observations through the entire caller stack,
not only its typing. Retired roots belong to the pre-state callee activation. -/
theorem ConfigurationTyped.restore_prefix_consumption {context : FlowContext} {result : ResultType}
    {current : Environment} {value : Value} {caller : AddressedScope} {stack : List Frame}
    (typed : ConfigurationTyped program context result ⟨current, .result value, .restore caller :: stack⟩)
    {front : List StorageId} {middle : RuntimeHeap StorageCell}
    (owned : ∀ identity ∈ front, identity ∈ current.bindings.map Prod.snd)
    (executed : current.heap.retireMany front = some middle) :
    AddressedEnvironment.ConsumptionFrame program context.slots
      (⟨current, .result value, .restore caller :: stack⟩ : Configuration).outerEnvironment
      (⟨{ current with heap := middle, bindings := current.bindings.filter fun entry => decide (entry.2 ∉ front) },
        .result value, .restore caller :: stack⟩ : Configuration).outerEnvironment := by
  cases typed with | intro store issued code continuation =>
    cases code with | result resident =>
      cases continuation with | cons frame tail =>
        cases frame with | restore locals discard callerTyped callerIssued older =>
          have preserved : ∀ (scope : AddressedScope) states,
              BindingMap.Typed program current.heap scope.activation scope.bindings states →
              scope.activation.index < current.activation.index →
              ∀ identity ∈ scope.bindings.map Prod.snd, middle.read identity = current.heap.read identity := by
            intro scope states scopeTyped previous identity member
            apply RuntimeHeap.retireMany_outside executed
            intro retired
            apply scopeTyped.apart_activations store (fun same => ?_) identity member (owned identity retired)
            have equal := congrArg ActivationId.index same
            omega
          apply tail.consumption_frame
            (before := Frame.environment (.restore caller) current)
            (after := { current with heap := middle, activation := caller.activation, bindings := caller.bindings })
            ⟨_, callerTyped, rfl⟩ (.of_cells rfl (preserved caller _ callerTyped older))
          intro scope states scopeTyped previous
          exact preserved scope states scopeTyped (Nat.lt_trans previous older)


/-- Local retirement preserves the retained lexical suffix and all observations
through its continuation, despite synchronized removal of one binding. -/
theorem ConfigurationTyped.retire_scope_consumption {context : FlowContext} {result : ResultType}
    {before after : Environment} {value : Value} {count index : Nat} {stack : List Frame}
    {entry : BindingId × StorageId}
    (typed : ConfigurationTyped program context result ⟨before, .result value, .scope count :: stack⟩)
    (selected : before.bindings[index]? = some entry) (inside : index < count)
    (retired : before.retireBinding index = some after) :
    AddressedEnvironment.ConsumptionFrame program context.slots
      (⟨before, .result value, .scope count :: stack⟩ : Configuration).outerEnvironment
      (⟨after, .result value, .scope (count - 1) :: stack⟩ : Configuration).outerEnvironment := by
  cases typed with | intro store issued code continuation =>
    cases code with | result resident =>
      cases continuation with | cons frame tail =>
        have declared := frame.declares (before := before) ⟨_, store, rfl⟩
        cases frame with | scope locals discard joined =>
          obtain ⟨next, produced, _, _, _, activation, supply, bindings, _, outside, callers⟩ :=
            AddressedEnvironment.retireBinding.progress store selected
          cases Option.some.inj (retired.symm.trans produced)
          have suffix := BindingMap.eraseIdx_drop before.bindings inside
          have excluded : entry.2 ∉ (before.bindings.drop locals.length).map Prod.snd := by
            rw [← suffix]
            intro member
            obtain ⟨binding, member, same⟩ := List.mem_map.mp member
            have erased := List.mem_of_mem_drop member
            rw [BindingMap.eraseIdx_filter store.addresses_distinct selected] at erased
            exact (of_decide_eq_true (List.mem_filter.mp erased).2) same
          refine tail.consumption_frame
            (before := Frame.environment (.scope locals.length) before)
            (after := Frame.environment (.scope (locals.length - 1)) after)
            declared (.of_cells ?_ ?_) ?_
          · simp only [Frame.environment, Frame.activation, AddressedEnvironment.scope]
            rw [activation, bindings, suffix]
          · intro identity member
            exact outside identity (fun same => excluded (same ▸ member))
          · intro caller states callerTyped older
            exact (callers caller states callerTyped (by
              intro same
              have equal := congrArg ActivationId.index same
              simp only [Frame.environment, Frame.activation] at older
              omega)).2


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
          (continuationEnvironment ((Frame.scope bindings.bindings.length).environment (env.extend bindings.bindings)) stack)
        rw [Frame.scope_extension]
        exact tail.consumption_allocation outerDeclared env.activation bindings.bindings env.supply
    case scope stack count value empty =>
      have suffix : env.bindings.drop count = env.bindings := by
        simpa [empty] using List.take_append_drop count env.bindings
      simp only [Configuration.outerEnvironment, continuationEnvironment, Frame.environment, Frame.activation, suffix]
      exact .refl _ _
    case scopeOwner stack count index identity value cell chosen found =>
      have inside := BindingMap.nextRelease.in_prefix (List.take_prefix _ _) chosen
      simp only [List.length_take] at inside
      have localIndex := Nat.lt_of_lt_of_le inside (Nat.min_le_left _ _)
      simp only [Configuration.outerEnvironment, continuationEnvironment, Frame.environment, Frame.activation,
        BindingMap.eraseIdx_drop _ localIndex]
      exact .refl _ _
    case retire after stack index value operation =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          have projected := frame.declares declared
          cases frame with | retire inside discard =>
            obtain ⟨entry, selected, _, _, _⟩ := AddressedEnvironment.retireBinding.eq_some_iff.mp operation
            obtain ⟨next, produced, _, _, _, activation, supply, bindings, _, outside, callers⟩ :=
              AddressedEnvironment.retireBinding.progress store selected
            cases Option.some.inj (operation.symm.trans produced)
            apply tail.consumption_frame (before := (Frame.retire index).environment env) (after := after) projected (.of_cells ?_ ?_) ?_
            · simp only [Frame.environment, Frame.activation, AddressedEnvironment.scope, activation, bindings]
            · intro identity member
              apply outside identity
              intro same
              obtain ⟨binding, member, matching⟩ := List.mem_map.mp member
              change binding ∈ env.bindings.eraseIdx index at member
              rw [BindingMap.eraseIdx_filter store.addresses_distinct selected] at member
              exact (of_decide_eq_true (List.mem_filter.mp member).2) (matching.trans same)
            · intro caller states callerTyped older
              exact (callers caller states callerTyped (by
                intro same
                have equal := congrArg ActivationId.index same
                simp only [Frame.environment, Frame.activation] at older
                omega)).2
    case install after stack place rest value written =>
      cases code with
      | install resident selected path writable selection discard mask context checked =>
            obtain ⟨producedAfter, _, _, produced, _, _, _, _, _, _, _, _, retained⟩ :=
              AddressedEnvironment.write.progress store selected path resident
            cases Option.some.inj (written.symm.trans produced)
            have selectedSlot := congrArg (Option.map BindingState.slot) selected
            rw [← lookup.map] at selectedSlot
            change lookup place.root current.slots = some _ at selectedSlot
            rw [← (ControlTyped.install resident selected path writable selection discard mask context checked).slots] at selectedSlot
            have framed := AddressedEnvironment.write.consumption_frame declared selectedSlot writable written
            apply continuation.consumption_frame declared framed
            intro scope states realized older
            exact (retained scope states realized (by intro same; have := congrArg ActivationId.index same; omega)).2

theorem ConfigurationTyped.consumption_run {context : FlowContext} {result : ResultType} {before after : Configuration}
    (checkedProgram : program.Checked) (typed : ConfigurationTyped program context result before)
    (run : Run program before after) :
    AddressedEnvironment.ConsumptionFrame program context.slots before.outerEnvironment after.outerEnvironment := by
  induction run with
  | refl state => exact .refl _ _
  | step head tail ih => exact (typed.consumption_step head).trans (ih (typed.preservation checkedProgram head))

/-- Cleanup retains its protected continuation payload; installation retains
the replacement until old-resident cleanup has finished. -/
def Control.PrincipalConsistent (program : Program) : Control → Prop
  | .result value => value.PrincipalConsistent program
  | .results values => ∀ value ∈ values, value.PrincipalConsistent program
  | .cleanup pending rest =>
      (∀ value, .enter value ∈ pending → value.PrincipalConsistent program) ∧
        rest.PrincipalConsistent program
  | .install _ _ value _ => value.PrincipalConsistent program
  | _ => True

def Frame.PrincipalConsistent (program : Program) : Frame → Prop
  | .tupleTail value | .argumentTail value => value.PrincipalConsistent program
  | _ => True

theorem ControlTyped.principal_consistent {before after control result}
    (typed : ControlTyped program before control result after) :
    control.PrincipalConsistent program := by
  induction typed with
  | result resident => exact resident.principal_consistent
  | results residents =>
    intro value member
    obtain ⟨_, _, resident⟩ := residents.member member
    exact resident.principal_consistent
  | cleanup safe checked ih =>
    refine ⟨?_, ih⟩
    intro value member
    cases safe (.enter value) member with
    | enter resident allowed => exact resident.principal_consistent
  | install resident => exact resident.principal_consistent
  | expression | arguments => trivial

theorem FrameTyped.principal_consistent {heap supply activation context next input result frame}
    (typed : FrameTyped program heap supply activation context input frame next result) :
    frame.PrincipalConsistent program := by
  cases typed <;> try trivial
  case tupleTail resident => exact resident.principal_consistent
  case argumentTail resident => exact resident.principal_consistent

theorem ContinuationTyped.principal_consistent {heap supply activation context final input result stack}
    (typed : ContinuationTyped program heap supply activation context input stack final result) :
    ∀ frame ∈ stack, frame.PrincipalConsistent program := by
  induction typed with
  | nil => intro frame member; cases member
  | cons head tail ih =>
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · exact head.principal_consistent
    · exact ih frame member


/-- Current results and argument packs retain a principal consistent under every
valid resident typing. Copy reads and disposal sites respect the same structural
authority; scope retirement preserves newest-owner-first order. No future
readiness or completed execution is assumed. -/
def Configuration.OwnershipSafe (program : Program) (state : Configuration) : Prop :=
  (state.control.PrincipalConsistent program ∧
    ∀ frame ∈ state.continuation, frame.PrincipalConsistent program) ∧
  match state.control, state.continuation with
  | .cleanup pending _, _ =>
      (∀ task ∈ pending, DisposalTask.Safe program task) ∧
      ∀ value type principal, .enter value ∈ pending → ValueHasType program value type →
        type.HasPrincipal program.data principal → principal.Permits 0
  | .expression (.read place), _ =>
      BindingMap.CopySafe program state.environment.heap state.environment.bindings place ∧
      ∀ value type principal, state.environment.read program place = some value →
        ValueHasType program value type → type.HasPrincipal program.data principal →
        ∀ count, principal.Permits count
  | .result _, .scope count :: _ =>
      BindingMap.Disposable program state.environment.heap (List.take count state.environment.bindings) ∧
        (BindingMap.releaseOrder (List.take count state.environment.bindings)).Pairwise
          (fun newer older => older.index < newer.index)
  | .result _, .restore _ :: _ =>
      BindingMap.Disposable program state.environment.heap state.environment.bindings ∧
        state.environment.bindings.releaseOrder.Pairwise (fun newer older => older.index < newer.index)
  | .result _, .retire index :: _ =>
      ∀ entry cell, state.environment.bindings[index]? = some entry →
        state.environment.heap.read entry.2 = some cell → cell.resident.Disposable program cell.type
  | .result _, .assign home place _ :: _ =>
      BindingMap.ReplacementSafe program home state.environment.heap state.environment.bindings place
  | .install home place _ _, _ =>
      BindingMap.ReplacementSafe program home state.environment.heap state.environment.bindings place
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
    constructor
    · exact ⟨code.principal_consistent, continuation.principal_consistent⟩
    · cases code <;> try trivial
      case cleanup safe checked =>
        exact ⟨safe, fun _ _ _ member resident classified => (safe _ member).zero_use resident classified⟩
      case install resident selected path writable selection discard mask context checked =>
        exact store.replacement_safe selected path selection discard
      case expression checked =>
        cases checked <;> try trivial
        case read =>
          have safe := store.copy_safe (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
          exact ⟨safe, fun _ _ _ read resident classified => safe.permitted_uses read resident classified⟩
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
          case retire inside discard =>
            intro entry cell selected found
            obtain ⟨state, actual, source, actualFound, _, declared, resident⟩ := store.index selected
            cases Option.some.inj (actualFound.symm.trans found)
            have permission := discard _ source
            change state.initialization.Disposable program.data state.slot.type at permission
            rw [← declared] at permission
            exact permission.realizes resident.2
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

/-- A live nondiscardable descendant protects its containing cell at the actual
indexed retirement step, not only at a completed cleanup boundary. -/
theorem Configuration.OwnershipSafe.retire_preserves_nondiscardable
    {before : Environment} {after : Configuration} {value : Value} {index : Nat} {stack : List Frame}
    (safe : (⟨before, .result value, .retire index :: stack⟩ : Configuration).OwnershipSafe program)
    (step : Step program ⟨before, .result value, .retire index :: stack⟩ after)
    {address : StorageId} {cell : StorageCell} (found : before.heap.read address = some cell)
    {home : Module} {type : Ty} {fields : List FieldKey}
    (path : PathType program home cell.type fields type) {owner : PartialValue}
    (resident : cell.resident.selectFields program cell.type fields = some owner)
    (required : ¬ owner.Disposable program type) :
    after.environment.heap.read address = some cell := by
  cases step with
  | retire operation =>
    obtain ⟨entry, selected, heap, primitive, rfl⟩ := AddressedEnvironment.retireBinding.eq_some_iff.mp operation
    apply (RuntimeHeap.retire_other primitive ?_).trans found
    intro same
    have permission := safe.2 entry cell selected (same ▸ found)
    obtain ⟨part, actual, allowed⟩ := path.disposable permission
    cases Option.some.inj (actual.symm.trans resident)
    exact required allowed
/-- Recover ownership authority for the actual first matching clause, not an
arbitrary clause with the same body or the same produced binding pack. -/
theorem Configuration.OwnershipSafe.selected_pattern {environment : Environment} {values : List Value}
    {stack : List Frame} {front back : List (Pattern × Expr)} {pattern : Pattern} {body : Expr}
    {patternHome : Module} {bindings : PatternMatch}
    (safe : (⟨environment, .results values, .patterns patternHome (front ++ (pattern, body) :: back) :: stack⟩ : Configuration).OwnershipSafe program)
    (missed : ∀ earlier ∈ front, earlier.1.matchValue (argumentValue values) = none)
    (matched : pattern.matchValue (argumentValue values) = some bindings) :
    ∃ subject locals, ValueHasType program (argumentValue values) subject ∧
      PatternType program patternHome pattern subject locals := by
  have selected : selectArm (argumentValue values) (front ++ (pattern, body) :: back) = some (bindings, body) := by
    rw [selectArm.skip_missed _ _ _ missed]
    simp only [selectArm, matched]
  obtain ⟨subject, locals, actual, actualFront, actualBack, resident, typed, split, skipped, found⟩ :=
    safe.2 bindings body selected
  have same := selectArm.first_unique split missed skipped
    (by simp only [matched, ne_eq, reduceCtorEq, not_false_eq_true])
    (by simp only [found, ne_eq, reduceCtorEq, not_false_eq_true])
  have patternSame : pattern = actual := congrArg Prod.fst same
  exact ⟨subject, locals, resident, patternSame.symm ▸ typed⟩

/-- Source-prefix ownership safety constrains every actual lexical retirement,
including its intermediate heap transitions and strict acquisition order. -/
theorem Configuration.OwnershipSafe.scope_retirement {before after : Environment}
    {value returned : Value} {count : Nat} {stack : List Frame}
    (safe : (⟨before, .result value, .scope count :: stack⟩ : Configuration).OwnershipSafe program)
    (run : Run program ⟨before, .result value, [.scope count]⟩ ⟨after, .result returned, []⟩)
    {front back : List StorageId} {identity : StorageId}
    (split : BindingMap.releaseOrder (List.take count before.bindings) = front ++ identity :: back) :
    ∃ middle next, before.heap.retireMany front = some middle ∧
      middle.retire identity = some next ∧ next.retireMany back = some after.heap ∧
      (∀ older ∈ back, older.index < identity.index) ∧
      ∃ cell, before.heap.read identity = some cell ∧ middle.read identity = some cell ∧
        cell.resident.Disposable program cell.type ∧
        ∀ (observer : Module) (fields : List FieldKey) (nominal : Nat) (declaration : DataDecl),
          PathType program observer cell.type fields (.nominal nominal) →
          program.data nominal = some declaration → declaration.restriction = some .exact →
          ∃ part, cell.resident.selectFields program cell.type fields = some part ∧ part.Empty := by
  obtain ⟨_, exited⟩ := run.scope_result
  obtain ⟨heap, released, same⟩ := Option.map_eq_some_iff.mp exited
  cases same
  exact BindingMap.Disposable.release_prefix safe.2.1 released split

/-- Function return consumes the same release producer as lexical scope exit;
parameter-list order cannot override actual newest-owner-first retirement. -/
theorem Configuration.OwnershipSafe.return_retirement {before after : Environment}
    {value returned : Value} {caller : AddressedScope} {stack : List Frame}
    (safe : (⟨before, .result value, .restore caller :: stack⟩ : Configuration).OwnershipSafe program)
    (run : Run program ⟨before, .result value, [.restore caller]⟩ ⟨after, .result returned, []⟩)
    {front back : List StorageId} {identity : StorageId}
    (split : before.bindings.releaseOrder = front ++ identity :: back) :
    ∃ middle next, before.heap.retireMany front = some middle ∧
      middle.retire identity = some next ∧ next.retireMany back = some after.heap ∧
      (∀ older ∈ back, older.index < identity.index) ∧
      ∃ cell, before.heap.read identity = some cell ∧ middle.read identity = some cell ∧
        cell.resident.Disposable program cell.type ∧
        ∀ (observer : Module) (fields : List FieldKey) (nominal : Nat) (declaration : DataDecl),
          PathType program observer cell.type fields (.nominal nominal) →
          program.data nominal = some declaration → declaration.restriction = some .exact →
          ∃ part, cell.resident.selectFields program cell.type fields = some part ∧ part.Empty := by
  obtain ⟨_, restored⟩ := run.restore_result
  obtain ⟨heap, released, same⟩ := Option.map_eq_some_iff.mp restored
  cases same
  exact BindingMap.Disposable.release_prefix safe.2.1 released split

/-- Every active and retained scope keeps its actual owning activation and
typed partial residents in the current heap. No saved heap is substituted. -/
theorem ContinuationTyped.typed_scopes {before : Environment} {current final : FlowContext}
    {input result : ResultType} {stack : List Frame}
    (typed : ContinuationTyped program before.heap before.supply before.activation current input stack final result)
    (store : before.Declares program current.slots) :
    ∀ front back, stack = front ++ back →
      ∀ identity ∈ (continuationEnvironment before front).bindings.map Prod.snd,
        ∃ cell, before.heap.read identity = some cell ∧
          cell.activation = (continuationEnvironment before front).activation ∧
          ∃ state, cell.Typed program state := by
  intro front
  induction front generalizing before current input stack with
  | nil =>
    intro back same identity member
    obtain ⟨states, residents, _⟩ := store
    exact residents.live_typed identity member
  | cons frame front ih =>
    intro back same identity member
    subst stack
    cases typed with
    | cons head tail => exact ih tail (head.declares store) back rfl identity member

theorem ConfigurationTyped.typed_scopes {context result state}
    (typed : ConfigurationTyped program context result state) :
    ∀ front back, state.continuation = front ++ back →
      ∀ identity ∈ (continuationEnvironment state.environment front).bindings.map Prod.snd,
        ∃ cell, state.environment.heap.read identity = some cell ∧
          cell.activation = (continuationEnvironment state.environment front).activation ∧
          ∃ mask, cell.Typed program mask := by
  cases typed with
  | intro store issued code continuation =>
    exact continuation.typed_scopes ⟨_, store, code.slots.symm⟩

/-- Retired identities cannot remain in any active or retained caller binding
map of a well-typed machine configuration. This is not reference-loan typing. -/
theorem ConfigurationTyped.retired_not_retained {context result state} {identity : StorageId}
    (typed : ConfigurationTyped program context result state)
    (retired : state.environment.heap.Retired identity)
    {front back : List Frame} (split : state.continuation = front ++ back) :
    identity ∉ (continuationEnvironment state.environment front).bindings.map Prod.snd := by
  intro member
  obtain ⟨cell, found, _, _⟩ := typed.typed_scopes front back split identity member
  rw [retired.2] at found
  cases found

/-- Maximal behavior starts from the actual typed control and continuation,
including partially evaluated calls and pending caller restoration. -/
theorem ConfigurationTyped.behavior (checkedProgram : program.Checked)
    {context : FlowContext} {type : Ty} {before : Configuration}
    (typed : ConfigurationTyped program context (.one type) before) :
    (∃ after value, Run program before ⟨after, .result value, []⟩ ∧
      ValueHasType program value type ∧
      (∃ principal, type.HasPrincipal program.data principal ∧
        ∀ originalType originalPrincipal, ValueHasType program value originalType →
          originalType.HasPrincipal program.data originalPrincipal → originalPrincipal = principal) ∧
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
    refine ⟨after, value, run, resident, resident.principal_exists, store, typed.consumption_run checkedProgram run,
      current.ownership_safe, run.external_frame, run.return_retires_all ?_⟩
    intro identity member
    obtain ⟨cell, found, _, _⟩ := typed.typed_scopes before.continuation [] (by simp) identity member
    exact before.environment.heap.bounded _ _ found
  · right
    refine ⟨trace, infinite, ?_⟩
    intro index
    have run := infinite.prefix index
    have current := typed.run checkedProgram run
    exact ⟨current, typed.consumption_run checkedProgram run, current.ownership_safe, run.external_frame,
      fun _ fresh _ live => run.allocated_tracked fresh live⟩


end Grounded

