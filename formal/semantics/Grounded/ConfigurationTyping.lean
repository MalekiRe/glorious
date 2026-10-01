import Grounded.Checking
import Grounded.Execution

/-! Current-state realization of the shared heap. Retained frame scopes are
checked in this heap and ordered by actual generative activation identities. -/
namespace Grounded

abbrev StaticContext := List (BindingId × BindingType)

inductive ResultType where
  | one (type : Ty)
  | many (types : List Ty)

inductive ControlTyped (program : Program) (context : StaticContext) : Control → ResultType → Prop where
  | expression {home : Module} {expression : Expr} {type : Ty}
      (checked : HasType program home context expression type) :
      ControlTyped program context (.expression expression) (.one type)
  | arguments {home : Module} {expressions : List Expr} {types : List Ty}
      (checked : HasTypes program home context expressions types) :
      ControlTyped program context (.arguments expressions) (.many types)
  | result {value : Value} {type : Ty} (resident : ValueHasType program value type) :
      ControlTyped program context (.result value) (.one type)
  | results {values : List Value} {types : List Ty} (residents : ValuesHaveTypes program values types) :
      ControlTyped program context (.results values) (.many types)

inductive FrameTyped (program : Program) (heap : RuntimeHeap StorageCell) (supply : ActivationSupply)
    (activation : ActivationId) : StaticContext → ResultType → Frame → StaticContext → ResultType → Prop where
  | sequence {home : Module} {context : StaticContext} {discarded result : Ty} {rest : Expr}
      (discard : Duplicable program.data discarded) (checked : HasType program home context rest result) :
      FrameTyped program heap supply activation context (.one discarded) (.sequence rest) context (.one result)
  | bind {home : Module} {context : StaticContext} {name : BindingId} {mutable : Bool} {localType result : Ty} {body : Expr}
      (discard : Duplicable program.data localType)
      (checked : HasType program home ((name, ⟨localType, mutable⟩) :: context) body result)
      (fresh : name ∉ context.map Prod.fst) :
      FrameTyped program heap supply activation context (.one localType) (.bind name ⟨localType, mutable⟩ body) context (.one result)
  | scope {context : StaticContext} (locals : StaticContext) {result : Ty}
      (discard : ∀ binding ∈ locals, Duplicable program.data binding.2.type) :
      FrameTyped program heap supply activation (locals ++ context) (.one result) (.scope locals.length) context (.one result)
  | assign {home : Module} {context : StaticContext} {place : Place} {type result : Ty} {rest : Expr}
      (selected : PlaceType program home context place type true) (discard : Duplicable program.data type)
      (checked : HasType program home context rest result) :
      FrameTyped program heap supply activation context (.one type) (.assign place rest) context (.one result)
  | tupleHead {home : Module} {context : StaticContext} {first : Ty} {types : List Ty} {tail : List Expr}
      (checked : HasTypes program home context tail types) :
      FrameTyped program heap supply activation context (.one first) (.tupleHead tail) context (.one (.tuple first types))
  | tupleTail {context : StaticContext} {first : Ty} {types : List Ty} {head : Value}
      (resident : ValueHasType program head first) :
      FrameTyped program heap supply activation context (.many types) (.tupleTail head) context (.one (.tuple first types))
  | project {home : Module} {context : StaticContext} {parent result : Ty} {key : FieldKey} {index : Nat}
      (discard : Duplicable program.data parent) (selected : ProjectionType program home parent key index result) :
      FrameTyped program heap supply activation context (.one parent) (.project key) context (.one result)
  | array {context : StaticContext} {element : Ty} {length : Nat}
      (finite : FiniteLayout program.target program.data element) (size : length < 2 ^ program.target.pointerBits) :
      FrameTyped program heap supply activation context (.many (List.replicate length element)) .array context (.one (.array element length))
  | construct {home : Module} {context : StaticContext} {identity : Nat} {tag : Option Nat} {declaration : DataDecl} {schema : Fields}
      (declared : program.data identity = some declaration) (chosen : declaration.constructor tag = some schema)
      (finite : FiniteLayout program.target program.data (.nominal identity))
      (copyable : Duplicable program.data (.nominal identity))
      (visible : declaration.visibility.Allows declaration.home home)
      (access : ∀ field ∈ schema.residents, field.visibility.Allows declaration.home home) :
      FrameTyped program heap supply activation context (.many (schema.residents.map Field.type)) (.construct identity tag) context (.one (.nominal identity))
  | call {context : StaticContext} {identity : Nat} {declaration : FunctionDecl}
      (declared : program.functions identity = some declaration) :
      FrameTyped program heap supply activation context (.many (declaration.parameters.map (fun parameter => parameter.2.type)))
        (.call declaration) context (.one declaration.result)
  | patterns {home : Module} {context : StaticContext} {inputs : List Ty} {arms : List (Pattern × Expr)} {result : Ty}
      (nonempty : arms ≠ []) (covered : Covers program [argumentType inputs] (arms.map (fun arm => [arm.1])))
      (checked : ArmsType program home context (argumentType inputs) result [] arms) :
      FrameTyped program heap supply activation context (.many inputs) (.patterns arms) context (.one result)
  | restore {context : StaticContext} (locals : StaticContext) {result : Ty} {caller : AddressedScope}
      (discard : ∀ binding ∈ locals, Duplicable program.data binding.2.type)
      (retained : caller.Realizes program heap context)
      (issued : supply.Issued caller.activation)
      (older : caller.activation.index < activation.index) :
      FrameTyped program heap supply activation locals (.one result) (.restore caller) context (.one result)
  | argumentHead {home : Module} {context : StaticContext} {first : Ty} {types : List Ty} {tail : List Expr}
      (checked : HasTypes program home context tail types) :
      FrameTyped program heap supply activation context (.one first) (.argumentHead tail) context (.many (first :: types))
  | argumentTail {context : StaticContext} {first : Ty} {types : List Ty} {head : Value}
      (resident : ValueHasType program head first) :
      FrameTyped program heap supply activation context (.many types) (.argumentTail head) context (.many (first :: types))

inductive ContinuationTyped (program : Program) (heap : RuntimeHeap StorageCell) (supply : ActivationSupply) :
    ActivationId → StaticContext → ResultType → List Frame → StaticContext → ResultType → Prop where
  | nil {activation : ActivationId} {context : StaticContext} {result : ResultType} :
      ContinuationTyped program heap supply activation context result [] context result
  | cons {activation : ActivationId} {context middle final : StaticContext} {input result output : ResultType}
      {frame : Frame} {stack : List Frame}
      (head : FrameTyped program heap supply activation context input frame middle result)
      (tail : ContinuationTyped program heap supply (frame.activation activation) middle result stack final output) :
      ContinuationTyped program heap supply activation context input (frame :: stack) final output

inductive ConfigurationTyped (program : Program) (context : StaticContext) (result : ResultType) : Configuration → Prop where
  | intro {current : StaticContext} {input : ResultType} {environment : Environment} {control : Control} {stack : List Frame}
      (store : environment.Realizes program current)
      (code : ControlTyped program current control input)
      (continuation : ContinuationTyped program environment.heap environment.supply environment.activation current input stack context result) :
      ConfigurationTyped program context result ⟨environment, control, stack⟩

variable {program : Program}

theorem FrameTyped.activation_le {heap : RuntimeHeap StorageCell} {supply : ActivationSupply}
    {activation : ActivationId} {context next : StaticContext} {input result : ResultType} {frame : Frame}
    (typed : FrameTyped program heap supply activation context input frame next result) :
    (frame.activation activation).index ≤ activation.index := by
  cases typed <;> simp only [Frame.activation] <;> omega

theorem FrameTyped.transport {heap after : RuntimeHeap StorageCell} {supply nextSupply : ActivationSupply}
    {activation : ActivationId} {context next : StaticContext} {input result : ResultType} {frame : Frame}
    (typed : FrameTyped program heap supply activation context input frame next result)
    (issued : ∀ previous, supply.Issued previous → nextSupply.Issued previous)
    (preserved : ∀ scope scopeContext, AddressedScope.Realizes scope program heap scopeContext →
      scope.activation.index < activation.index → scope.Realizes program after scopeContext) :
    FrameTyped program after nextSupply activation context input frame next result := by
  cases typed <;> constructor <;> first | assumption | apply preserved <;> assumption | apply issued <;> assumption

theorem ContinuationTyped.transport {heap after : RuntimeHeap StorageCell} {supply nextSupply : ActivationSupply}
    {activation : ActivationId} {context final : StaticContext} {input result : ResultType} {stack : List Frame}
    (typed : ContinuationTyped program heap supply activation context input stack final result)
    (issued : ∀ previous, supply.Issued previous → nextSupply.Issued previous)
    (preserved : ∀ scope scopeContext, AddressedScope.Realizes scope program heap scopeContext →
      scope.activation.index < activation.index → scope.Realizes program after scopeContext) :
    ContinuationTyped program after nextSupply activation context input stack final result := by
  revert preserved
  induction typed with
  | nil => intro _; exact .nil
  | cons head tail ih =>
    intro preserved
    refine .cons (head.transport issued preserved) (ih ?_)
    intro scope scopeContext realized older
    exact preserved scope scopeContext realized (Nat.lt_of_lt_of_le older head.activation_le)

theorem ConfigurationTyped.entry {home : Module} {context : StaticContext} {expression : Expr} {type : Ty}
    (checked : HasType program home context expression type) {environment : Environment}
    (store : environment.Realizes program context) :
    ConfigurationTyped program context (.one type) ⟨environment, .expression expression, []⟩ :=
  .intro store (.expression checked) .nil


/-- Actual addressed operations construct reads, writes and retirements from
current realization. Neither successful cleanup nor a future run is assumed. -/
theorem ConfigurationTyped.progress {context : StaticContext} {result : ResultType} {state : Configuration}
    (typed : ConfigurationTyped program context result state) : Terminal state ∨ ∃ next, Step program state next := by
  cases typed with
  | intro store code continuation =>
    cases code with
    | expression checked =>
      right
      cases checked with
      | unit => exact ⟨_, .unit⟩
      | integer fits => exact ⟨_, .integer fits⟩
      | character valid => exact ⟨_, .character valid⟩
      | group body => exact ⟨_, .group⟩
      | read place copyable =>
        cases place with
        | root selected path =>
          obtain ⟨value, read, _⟩ := store.read (place := ⟨_, _⟩) (slot := ⟨_, _⟩) selected path
          exact ⟨_, .read read⟩
      | sequence head discard tail => exact ⟨_, .sequence⟩
      | bind initial discard body fresh => exact ⟨_, .bind⟩
      | tuple head tail => exact ⟨_, .tuple⟩
      | project source discard selected => exact ⟨_, .project⟩
      | array residents finite size => exact ⟨_, .array⟩
      | constant declared visible resolved structural body => exact ⟨_, .constant declared⟩
      | construct declared chosen finite copyable visible access residents => exact ⟨_, .construct⟩
      | call declared visible inputs => exact ⟨_, .call declared⟩
      | assign place discard resident rest => exact ⟨_, .assign⟩
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
        | scope locals discard =>
          obtain ⟨after, exited, _⟩ := store.exitScope locals.length
          exact ⟨_, .scope exited⟩
        | assign place discard checked =>
          cases place with
          | root selected path =>
            obtain ⟨after, written, _⟩ := store.write (place := ⟨_, _⟩) (slot := ⟨_, true⟩) selected path rfl resident
            exact ⟨_, .assignResult written⟩
        | tupleHead checked => exact ⟨_, .tupleHead⟩
        | project discard projection =>
          obtain ⟨value, selected, _, _⟩ := projection.access resident
          exact ⟨_, .projectResult selected⟩
        | restore locals discard retained issued older =>
          obtain ⟨after, restored, _⟩ := store.restore retained issued (by
            intro same
            have := congrArg ActivationId.index same
            omega)
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
        | construct declared chosen finite copyable visible access => exact ⟨_, .constructResult⟩
        | call declared =>
          obtain ⟨inputs, prepared⟩ := prepareBindings.exists residents
          exact ⟨_, .callInputs prepared⟩
        | patterns nonempty covered checked =>
          obtain ⟨bindings, body, selected⟩ := covered.selectArm residents.argument
          exact ⟨_, .selectedPattern selected⟩
        | argumentTail head => exact ⟨_, .argumentTail⟩


/-- Ordinary and constant calls enter through the same allocator and retain
only the caller scope. Older continuation frames are re-realized in the new heap. -/
theorem ConfigurationTyped.invoke {environment : Environment} {callerContext final : StaticContext}
    {home : Module} {body : Expr} {type : Ty} {result : ResultType} {stack : List Frame}
    {inputs : List BindingInput}
    (store : environment.Realizes program callerContext)
    (continuation : ContinuationTyped program environment.heap environment.supply environment.activation
      callerContext (.one type) stack final result)
    (inputsTyped : BindingInputsTyped program inputs)
    (checked : HasType program home (inputs.map fun input => (input.name, input.slot)) body type)
    (discard : ∀ binding ∈ inputs.map (fun input => (input.name, input.slot)), Duplicable program.data binding.2.type) :
    ConfigurationTyped program final result
      ⟨enterBindings environment.heap environment.supply inputs, .expression body, .restore environment.scope :: stack⟩ := by
  obtain ⟨entered, retained⟩ := inputsTyped.enter environment.heap environment.supply
  refine .intro entered (.expression checked) (.cons (.restore _ discard
    (retained environment.scope callerContext store.1).1
    (environment.supply.allocate_preserves store.2) store.2) ?_)
  apply continuation.transport (fun previous issued => ActivationSupply.allocate_preserves issued)
  intro scope context realized _
  exact (retained scope context realized).1


/-- Preservation follows every real shared-heap transition, including the
live realization of all older restoration frames. -/
theorem ConfigurationTyped.preservation {context : StaticContext} {result : ResultType}
    {before after : Configuration} (checkedProgram : program.Checked)
    (typed : ConfigurationTyped program context result before)
    (step : Step program before after) : ConfigurationTyped program context result after := by
  cases typed with
  | intro store code continuation =>
    cases step with
    | unit =>
      cases code with | expression checked => cases checked; exact .intro store (.result .unit) continuation
    | integer fits =>
      cases code with | expression checked => cases checked; exact .intro store (.result (.integer fits)) continuation
    | character valid =>
      cases code with | expression checked => cases checked; exact .intro store (.result (.character valid)) continuation
    | group =>
      cases code with | expression checked =>
        cases checked with | group body => exact .intro store (.expression body) continuation
    | read selected =>
      cases code with | expression checked =>
        cases checked with | read place copyable =>
          cases place with | root resolved path =>
            obtain ⟨value, found, resident⟩ := store.read (place := ⟨_, _⟩) (slot := ⟨_, _⟩) resolved path
            cases Option.some.inj (selected.symm.trans found)
            exact .intro store (.result resident) continuation
    | sequence =>
      cases code with | expression checked =>
        cases checked with | sequence head discard tail =>
          exact .intro store (.expression head) (.cons (.sequence discard tail) continuation)
    | sequenceResult =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          cases frame with | sequence discard checked => exact .intro store (.expression checked) tail
    | bind =>
      cases code with | expression checked =>
        cases checked with | bind initial discard body fresh =>
          exact .intro store (.expression initial) (.cons (.bind discard body fresh) continuation)
    | @bindResult env stack name slot body value =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          cases frame with | @bind home ctx bindingName mutable localType output body discard checked fresh =>
            obtain ⟨entered, retained⟩ := store.extend (inputs := [⟨name, ⟨_, mutable⟩, value⟩]) (.cons resident .nil (by simp))
              (by simpa using List.nodup_cons.mpr ⟨fresh, store.distinct⟩)
            refine .intro entered (.expression checked) (.cons (.scope [_] (by simpa using discard)) ?_)
            exact tail.transport (fun _ issued => issued) (fun scope ctx realized _ => (retained scope ctx realized).1)
    | scope exited =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          cases frame with | scope locals discard =>
            obtain ⟨after, produced, afterTyped, activation, supply, _, _, retained, _⟩ := store.exitScope locals.length
            cases Option.some.inj (exited.symm.trans produced)
            refine .intro (by simpa using afterTyped) (.result resident) ?_
            rw [activation, supply]
            apply tail.transport (fun _ issued => issued)
            intro scope ctx realized older
            simp only [Frame.activation] at older
            exact (retained scope ctx realized (by intro same; have := congrArg ActivationId.index same; omega)).1
    | assign =>
      cases code with | expression checked =>
        cases checked with | assign place discard resident rest =>
          exact .intro store (.expression resident) (.cons (.assign place discard rest) continuation)
    | assignResult written =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          cases frame with | assign place discard checked =>
            cases place with | root resolved path =>
              obtain ⟨updated, produced, afterTyped, _, framed, supply, _, retained⟩ :=
                store.write (place := ⟨_, _⟩) (slot := ⟨_, true⟩) resolved path rfl resident
              cases Option.some.inj (written.symm.trans produced)
              refine .intro afterTyped (.expression checked) ?_
              have activation := congrArg AddressedScope.activation framed.1
              simp only [AddressedEnvironment.scope] at activation
              rw [activation, supply]
              apply tail.transport (fun _ issued => issued)
              intro scope ctx realized older
              simp only [Frame.activation] at older
              obtain ⟨states, scopeTyped, slots, ready⟩ := realized
              exact ⟨states, (retained scope states scopeTyped (by
                intro same; have := congrArg ActivationId.index same; omega)).1, slots, ready⟩
    | tuple =>
      cases code with | expression checked =>
        cases checked with | tuple head tail =>
          exact .intro store (.expression head) (.cons (.tupleHead tail) continuation)
    | tupleHead =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          cases frame with | tupleHead checked =>
            exact .intro store (.arguments checked) (.cons (.tupleTail resident) tail)
    | tupleTail =>
      cases code with | results residents =>
        cases continuation with | cons frame tail =>
          cases frame with | tupleTail head => exact .intro store (.result (.tuple head residents)) tail
    | project =>
      cases code with | expression checked =>
        cases checked with | project source discard selected =>
          exact .intro store (.expression source) (.cons (.project discard selected) continuation)
    | projectResult selected =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          cases frame with | project discard projection =>
            obtain ⟨value, found, valueTyped, _⟩ := projection.access resident
            cases Option.some.inj (selected.symm.trans found)
            exact .intro store (.result valueTyped) tail
    | array =>
      cases code with | expression checked =>
        cases checked with | array residents finite size =>
          exact .intro store (.arguments residents) (.cons (.array finite size) continuation)
    | arrayResult =>
      cases code with | results residents =>
        cases continuation with | cons frame tail =>
          cases frame with | array finite size => exact .intro store (.result (.array residents finite size)) tail
    | constant declared =>
      cases code with | expression checked =>
        cases checked with | constant otherDeclared visible resolved structural body =>
          cases Option.some.inj (declared.symm.trans otherDeclared)
          exact ConfigurationTyped.invoke store continuation .nil body (by simp)
    | restore restored =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          cases frame with | restore locals discard callerRealized issued older =>
            obtain ⟨after, produced, afterTyped, scope, supply, _, _, _, _, retained⟩ :=
              store.restore callerRealized issued (by intro same; have := congrArg ActivationId.index same; omega)
            cases Option.some.inj (restored.symm.trans produced)
            refine .intro afterTyped (.result resident) ?_
            have activation := congrArg AddressedScope.activation scope
            simp only [AddressedEnvironment.scope] at activation
            rw [activation, supply]
            apply tail.transport (fun _ issued => issued)
            intro previous ctx realized oldest
            exact (retained previous ctx realized (by
              intro same; have := congrArg ActivationId.index same; simp only [Frame.activation] at oldest; omega)).1
    | construct =>
      cases code with | expression checked =>
        cases checked with | construct declared chosen finite copyable visible access residents =>
          exact .intro store (.arguments residents) (.cons (.construct declared chosen finite copyable visible access) continuation)
    | constructResult =>
      cases code with | results residents =>
        cases continuation with | cons frame tail =>
          cases frame with | construct declared chosen finite copyable visible access =>
            exact .intro store (.result (.nominal declared chosen finite residents)) tail
    | call declared =>
      cases code with | expression checked =>
        cases checked with | call otherDeclared visible inputs =>
          cases Option.some.inj (declared.symm.trans otherDeclared)
          exact .intro store (.arguments inputs) (.cons (.call otherDeclared) continuation)
    | callInputs prepared =>
      cases code with | results residents =>
        cases continuation with | cons frame tail =>
          cases frame with | call declared =>
            have declaration := checkedProgram _ _ declared
            obtain ⟨inputs, preparedInputs, inputsTyped, slots⟩ := prepareBindings.progress residents declaration.distinct
            cases Option.some.inj (prepared.symm.trans preparedInputs)
            apply ConfigurationTyped.invoke store tail inputsTyped
            · rw [slots]; exact declaration.body
            · rw [slots]; exact declaration.disposable
    | applyPatterns =>
      cases code with | expression checked =>
        cases checked with | applyPatterns arguments nonempty covered bodies =>
          exact .intro store (.arguments arguments) (.cons (.patterns nonempty covered bodies) continuation)
    | selectedPattern selected =>
      cases code with | results residents =>
        cases continuation with | cons frame tail =>
          cases frame with | patterns nonempty covered checked =>
            obtain ⟨locals, _, _, inputsTyped, slots, discard, bodyTyped, distinct⟩ := checked.selected residents.argument selected
            obtain ⟨entered, retained⟩ := store.extend inputsTyped (by
              rw [← slots] at distinct
              simpa only [List.map_append, List.map_map, Function.comp_def] using distinct)
            rw [slots] at entered
            refine .intro entered (.expression bodyTyped) (.cons ?_
              (tail.transport (fun _ issued => issued) (fun scope ctx realized _ => (retained scope ctx realized).1)))
            have length := congrArg List.length slots
            simp only [List.length_map] at length
            rw [length]
            exact .scope locals discard
    | nil =>
      cases code with | arguments checked => cases checked; exact .intro store (.results .nil) continuation
    | cons =>
      cases code with | arguments checked =>
        cases checked with | cons head tail =>
          exact .intro store (.expression head) (.cons (.argumentHead tail) continuation)
    | argumentHead =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          cases frame with | argumentHead checked =>
            exact .intro store (.arguments checked) (.cons (.argumentTail resident) tail)
    | argumentTail =>
      cases code with | results residents =>
        cases continuation with | cons frame tail =>
          cases frame with | argumentTail head => exact .intro store (.results (.cons head residents)) tail


theorem ConfigurationTyped.run {context : StaticContext} {result : ResultType} {before after : Configuration}
    (checkedProgram : program.Checked)
    (typed : ConfigurationTyped program context result before) (run : Run program before after) :
    ConfigurationTyped program context result after := by
  induction run with
  | refl state => exact typed
  | step head tail ih => exact ih (typed.preservation checkedProgram head)

theorem ConfigurationTyped.bindings_distinct {context : StaticContext} {result : ResultType} {state : Configuration}
    (typed : ConfigurationTyped program context result state) : (state.environment.bindings.map Prod.fst).Nodup := by
  cases typed with
  | intro store code continuation => rw [store.keys]; exact store.distinct

theorem ConfigurationTyped.normal_form {context : StaticContext} {type : Ty} {state : Configuration}
    (typed : ConfigurationTyped program context (.one type) state) (done : Terminal state) :
    ∃ environment value, state = ⟨environment, .result value, []⟩ ∧
      environment.Realizes program context ∧ ValueHasType program value type := by
  cases done with
  | result environment value =>
    cases typed with | intro store code continuation =>
      cases continuation
      cases code with | result resident => exact ⟨_, _, rfl, store, resident⟩
  | results environment values =>
    cases typed with | intro store code continuation =>
      cases continuation
      cases code


theorem FrameTyped.realizes {before : Environment} {current next : StaticContext}
    {input result : ResultType} {frame : Frame}
    (typed : FrameTyped program before.heap before.supply before.activation current input frame next result)
    (store : before.Realizes program current) : (frame.environment before).Realizes program next := by
  cases typed <;> try exact store
  case scope locals result discard => simpa [Frame.environment, Frame.activation] using store.drop locals.length
  case restore => exact ⟨by assumption, by assumption⟩

theorem FrameTyped.frame {before after : Environment} {current next : StaticContext}
    {input result : ResultType} {frame : Frame}
    (typed : FrameTyped program before.heap before.supply before.activation current input frame next result)
    (store : before.Realizes program current) (framed : AddressedEnvironment.Frames current before after)
    (retained : ∀ scope ctx, AddressedScope.Realizes scope program before.heap ctx →
      scope.activation.index < before.activation.index →
      ∀ identity ∈ scope.bindings.map Prod.snd, after.heap.read identity = before.heap.read identity) :
    AddressedEnvironment.Frames next (frame.environment before) (frame.environment after) := by
  cases typed <;> try exact framed
  case scope locals result discard => simpa [Frame.environment, Frame.activation] using framed.drop store locals.length
  case restore =>
    refine ⟨rfl, ?_⟩
    intro name slot identity selected immutable mapped
    exact retained _ _ (by assumption) (by assumption) identity (List.mem_map.mpr ⟨(name, identity), lookup.mem mapped, rfl⟩)

theorem ContinuationTyped.frame {before after : Environment} {current final : StaticContext}
    {input result : ResultType} {stack : List Frame}
    (typed : ContinuationTyped program before.heap before.supply before.activation current input stack final result)
    (store : before.Realizes program current) (framed : AddressedEnvironment.Frames current before after)
    (retained : ∀ scope ctx, AddressedScope.Realizes scope program before.heap ctx →
      scope.activation.index < before.activation.index →
      ∀ identity ∈ scope.bindings.map Prod.snd, after.heap.read identity = before.heap.read identity) :
    AddressedEnvironment.Frames final (continuationEnvironment before stack) (continuationEnvironment after stack) := by
  induction stack generalizing before after current input with
  | nil => cases typed; exact framed
  | cons frame stack ih =>
    cases typed with
    | cons head tail =>
      apply ih tail (head.realizes store) (head.frame store framed retained)
      intro scope ctx realized older
      exact retained scope ctx realized (Nat.lt_of_lt_of_le older head.activation_le)


theorem ContinuationTyped.frame_allocation {before : Environment} {current final : StaticContext}
    {input result : ResultType} {stack : List Frame}
    (typed : ContinuationTyped program before.heap before.supply before.activation current input stack final result)
    (store : before.Realizes program current) (owner : ActivationId) (inputs : List BindingInput) (supply : ActivationSupply) :
    AddressedEnvironment.Frames final (continuationEnvironment before stack)
      (continuationEnvironment { before with heap := (allocateBindings before.heap owner inputs).2, supply := supply } stack) := by
  apply typed.frame (after := { before with heap := (allocateBindings before.heap owner inputs).2, supply := supply })
    store (.of_cells rfl (store.1.allocate_preserves owner inputs))
  intro scope ctx realized _
  exact realized.allocate_preserves owner inputs


/-- Every actual transition preserves the immutable cells exposed outside
its continuation, including nested calls and actual scope retirement. -/
theorem ConfigurationTyped.frame_step {context : StaticContext} {result : ResultType} {before after : Configuration}
    (typed : ConfigurationTyped program context result before) (step : Step program before after) :
    AddressedEnvironment.Frames context before.outerEnvironment after.outerEnvironment := by
  cases typed with
  | @intro current input env control stack store code continuation =>
    cases step <;> try exact .refl _ _
    case constant name declaration declared =>
      exact continuation.frame_allocation store env.supply.allocate.1 [] env.supply.allocate.2
    case bindResult stack name slot body value =>
      let inputs : List BindingInput := [⟨name, slot, value⟩]
      cases continuation with | cons frame tail =>
        cases frame
        change AddressedEnvironment.Frames context (continuationEnvironment env stack)
          (continuationEnvironment ((Frame.scope inputs.length).environment (env.extend inputs)) stack)
        rw [Frame.scope_extension]
        exact tail.frame_allocation store env.activation inputs env.supply
    case callInputs declaration values inputs prepared =>
      cases continuation with | cons frame tail =>
        cases frame
        exact tail.frame_allocation store env.supply.allocate.1 inputs env.supply.allocate.2
    case selectedPattern bindings stack values arms body selected =>
      cases continuation with | cons frame tail =>
        cases frame
        change AddressedEnvironment.Frames context (continuationEnvironment env stack)
          (continuationEnvironment ((Frame.scope bindings.length).environment (env.extend bindings)) stack)
        rw [Frame.scope_extension]
        exact tail.frame_allocation store env.activation bindings env.supply
    case scope after stack count value exited =>
      cases continuation with | cons frame tail =>
        cases frame with | scope locals discard =>
          obtain ⟨next, produced, _, _, _, _, _, retained, preserved⟩ := store.exitScope locals.length
          cases Option.some.inj (exited.symm.trans produced)
          have scopeEq : after.scope = ((Frame.scope locals.length).environment env).scope := by
            obtain ⟨heap, _, same⟩ := Option.map_eq_some_iff.mp exited
            cases same
            rfl
          refine tail.frame (before := (Frame.scope locals.length).environment env) (after := after)
            (by simpa [Frame.environment, Frame.activation] using store.drop locals.length) (.of_cells scopeEq ?_) ?_
          · intro identity member
            apply preserved identity
            have maps := congrArg AddressedScope.bindings scopeEq
            change after.bindings = env.bindings.drop locals.length at maps
            rw [maps]
            exact member
          · intro scope ctx realized older
            change scope.activation.index < env.activation.index at older
            exact (retained scope ctx realized (by intro same; have := congrArg ActivationId.index same; omega)).2
    case assignResult after stack place rest value written =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          cases frame with | assign selected discard checked =>
            cases selected with | root resolved path =>
              obtain ⟨next, produced, _, _, framed, _, _, retained⟩ :=
                store.write (place := ⟨_, _⟩) (slot := ⟨_, true⟩) resolved path rfl resident
              cases Option.some.inj (written.symm.trans produced)
              apply tail.frame store framed
              intro scope ctx realized older
              change scope.activation.index < env.activation.index at older
              obtain ⟨states, scopeTyped, _, _⟩ := realized
              exact (retained scope states scopeTyped (by intro same; have := congrArg ActivationId.index same; omega)).2
    case restore after caller stack value restored =>
      cases continuation with | cons frame tail =>
        cases frame with | restore locals discard callerRealized issued older =>
          obtain ⟨next, produced, _, scopeEq, _, _, _, preserved, _, retained⟩ :=
            store.restore callerRealized issued (by intro same; have := congrArg ActivationId.index same; omega)
          cases Option.some.inj (restored.symm.trans produced)
          refine tail.frame (before := (Frame.restore caller).environment env) (after := after)
            ⟨callerRealized, issued⟩ (.of_cells scopeEq preserved) ?_
          intro scope ctx realized oldest
          change scope.activation.index < caller.activation.index at oldest
          exact (retained scope ctx realized (by intro same; have := congrArg ActivationId.index same; omega)).2


theorem ConfigurationTyped.frame_run {context : StaticContext} {result : ResultType} {before after : Configuration}
    (checkedProgram : program.Checked) (typed : ConfigurationTyped program context result before)
    (run : Run program before after) : AddressedEnvironment.Frames context before.outerEnvironment after.outerEnvironment := by
  induction run with
  | refl state => exact .refl _ _
  | step head tail ih => exact (typed.frame_step head).trans (ih (typed.preservation checkedProgram head))


end Grounded
