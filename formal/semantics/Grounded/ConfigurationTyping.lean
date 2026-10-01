import Grounded.Checking
import Grounded.Execution

/-! Current-state realization for the logical machine. Pending frames retain
checking products and actual typed values, never certificates of future runs. -/
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

inductive FrameTyped (program : Program) : StaticContext → ResultType → Frame → StaticContext → ResultType → Prop where
  | sequence {home : Module} {context : StaticContext} {discarded result : Ty} {rest : Expr}
      (discard : Duplicable program.data discarded) (checked : HasType program home context rest result) :
      FrameTyped program context (.one discarded) (.sequence rest) context (.one result)
  | bind {home : Module} {context : StaticContext} {name : BindingId} {mutable : Bool} {localType result : Ty} {body : Expr}
      (discard : Duplicable program.data localType)
      (checked : HasType program home ((name, ⟨localType, mutable⟩) :: context) body result)
      (fresh : name ∉ context.map Prod.fst) :
      FrameTyped program context (.one localType) (.bind name ⟨localType, mutable⟩ body) context (.one result)
  | scope {context : StaticContext} (locals : StaticContext) {result : Ty}
      (discard : ∀ binding ∈ locals, Duplicable program.data binding.2.type) :
      FrameTyped program (locals ++ context) (.one result) (.scope locals.length) context (.one result)
  | assign {home : Module} {context : StaticContext} {place : Place} {type result : Ty} {rest : Expr}
      (selected : PlaceType program home context place type true) (discard : Duplicable program.data type)
      (checked : HasType program home context rest result) :
      FrameTyped program context (.one type) (.assign place rest) context (.one result)
  | tupleHead {home : Module} {context : StaticContext} {first : Ty} {types : List Ty} {tail : List Expr}
      (checked : HasTypes program home context tail types) :
      FrameTyped program context (.one first) (.tupleHead tail) context (.one (.tuple first types))
  | tupleTail {context : StaticContext} {first : Ty} {types : List Ty} {head : Value}
      (resident : ValueHasType program head first) :
      FrameTyped program context (.many types) (.tupleTail head) context (.one (.tuple first types))
  | project {home : Module} {context : StaticContext} {parent result : Ty} {key : FieldKey} {index : Nat}
      (discard : Duplicable program.data parent) (selected : ProjectionType program home parent key index result) :
      FrameTyped program context (.one parent) (.project key) context (.one result)
  | array {context : StaticContext} {element : Ty} {length : Nat}
      (finite : FiniteLayout program.target program.data element) (size : length < 2 ^ program.target.pointerBits) :
      FrameTyped program context (.many (List.replicate length element)) .array context (.one (.array element length))
  | construct {home : Module} {context : StaticContext} {identity : Nat} {tag : Option Nat} {declaration : DataDecl} {schema : Fields}
      (declared : program.data identity = some declaration) (chosen : declaration.constructor tag = some schema)
      (finite : FiniteLayout program.target program.data (.nominal identity))
      (copyable : Duplicable program.data (.nominal identity))
      (visible : declaration.visibility.Allows declaration.home home)
      (access : ∀ field ∈ schema.residents, field.visibility.Allows declaration.home home) :
      FrameTyped program context (.many (schema.residents.map Field.type)) (.construct identity tag) context (.one (.nominal identity))
  | call {context : StaticContext} {identity : Nat} {declaration : FunctionDecl}
      (declared : program.functions identity = some declaration) :
      FrameTyped program context (.many (declaration.parameters.map (fun parameter => parameter.2.type)))
        (.call declaration) context (.one declaration.result)
  | patterns {home : Module} {context : StaticContext} {inputs : List Ty} {arms : List (Pattern × Expr)} {result : Ty}
      (nonempty : arms ≠ []) (covered : Covers program [argumentType inputs] (arms.map (fun arm => [arm.1])))
      (checked : ArmsType program home context (argumentType inputs) result [] arms) :
      FrameTyped program context (.many inputs) (.patterns arms) context (.one result)
  | restore {context : StaticContext} (locals : StaticContext) {result : Ty} {caller : Environment}
      (discard : ∀ binding ∈ locals, Duplicable program.data binding.2.type)
      (retained : EnvironmentTyped program caller context) :
      FrameTyped program locals (.one result) (.restore caller) context (.one result)
  | argumentHead {home : Module} {context : StaticContext} {first : Ty} {types : List Ty} {tail : List Expr}
      (checked : HasTypes program home context tail types) :
      FrameTyped program context (.one first) (.argumentHead tail) context (.many (first :: types))
  | argumentTail {context : StaticContext} {first : Ty} {types : List Ty} {head : Value}
      (resident : ValueHasType program head first) :
      FrameTyped program context (.many types) (.argumentTail head) context (.many (first :: types))

inductive ContinuationTyped (program : Program) : StaticContext → ResultType → List Frame → StaticContext → ResultType → Prop where
  | nil {context : StaticContext} {result : ResultType} : ContinuationTyped program context result [] context result
  | cons {context middle final : StaticContext} {input result output : ResultType} {frame : Frame} {stack : List Frame}
      (head : FrameTyped program context input frame middle result)
      (tail : ContinuationTyped program middle result stack final output) :
      ContinuationTyped program context input (frame :: stack) final output

inductive ConfigurationTyped (program : Program) (context : StaticContext) (result : ResultType) : Configuration → Prop where
  | intro {current : StaticContext} {input : ResultType} {environment : Environment} {control : Control} {stack : List Frame}
      (store : EnvironmentTyped program environment current)
      (code : ControlTyped program current control input)
      (continuation : ContinuationTyped program current input stack context result) :
      ConfigurationTyped program context result ⟨environment, control, stack⟩

variable {program : Program}

theorem ConfigurationTyped.bindings_distinct {context : StaticContext} {result : ResultType} {state : Configuration}
    (typed : ConfigurationTyped program context result state) : (state.environment.map Prod.fst).Nodup := by
  cases typed with
  | intro store code continuation => exact store.runtimeDistinct


theorem ConfigurationTyped.entry {home : Module} {context : StaticContext} {expression : Expr} {type : Ty}
    (checked : HasType program home context expression type) {environment : Environment}
    (store : EnvironmentTyped program environment context) :
    ConfigurationTyped program context (.one type) ⟨environment, .expression expression, []⟩ :=
  .intro store (.expression checked) .nil

/-- Every actual transition preserves the current store, code and continuation
correspondence. No successor readiness or completed run occurs in the premises. -/
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
          obtain ⟨value, found, resident⟩ := store.readPlace place
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
    | bindResult =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          cases frame with | bind discard checked fresh =>
            exact .intro (.cons resident store fresh) (.expression checked)
              (.cons (.scope [_] (by simpa using discard)) tail)
    | scope =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          cases frame with | scope locals discard =>
            exact .intro (by simpa [Frame.environment] using store.drop locals.length) (.result resident) tail
    | assign =>
      cases code with | expression checked =>
        cases checked with | assign place discard resident rest =>
          exact .intro store (.expression resident) (.cons (.assign place discard rest) continuation)
    | assignResult written =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          cases frame with | assign place discard checked =>
            obtain ⟨updated, produced, afterTyped, _, _⟩ := store.writePlace place resident
            cases Option.some.inj (written.symm.trans produced)
            exact .intro afterTyped (.expression checked) tail
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
          exact .intro .nil (.expression body) (.cons (.restore [] (by simp) store) continuation)
    | restore =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          cases frame with | restore locals discard retained => exact .intro retained (.result resident) tail
    | construct =>
      cases code with | expression checked =>
        cases checked with | construct declared chosen finite copyable visible access residents =>
          exact .intro store (.arguments residents)
            (.cons (.construct declared chosen finite copyable visible access) continuation)
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
            obtain ⟨inputs, preparedInputs, inputsTyped⟩ := EnvironmentTyped.parameters _ _ residents declaration.distinct
            cases Option.some.inj (prepared.symm.trans preparedInputs)
            exact .intro inputsTyped (.expression declaration.body)
              (.cons (.restore _ declaration.disposable store) tail)
    | applyPatterns =>
      cases code with | expression checked =>
        cases checked with | applyPatterns arguments nonempty covered bodies =>
          exact .intro store (.arguments arguments) (.cons (.patterns nonempty covered bodies) continuation)
    | selectedPattern selected =>
      cases code with | results residents =>
        cases continuation with | cons frame tail =>
          cases frame with | patterns nonempty covered checked =>
            obtain ⟨locals, _, _, bindingsTyped, discard, bodyTyped, distinct⟩ := checked.selected residents.argument selected
            refine .intro (bindingsTyped.append store distinct) (.expression bodyTyped) (.cons ?_ tail)
            rw [← List.length_map (f := fun input : BindingInput => (input.name, input.value)), bindingsTyped.length]
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


/-- A realized configuration is terminal or makes an actual transition. Lookup,
write and selected-clause success are constructed from their operation contracts. -/
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
        obtain ⟨value, selected, _⟩ := store.readPlace place
        exact ⟨_, .read selected⟩
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
        | scope locals discard => exact ⟨_, .scope⟩
        | assign place discard checked =>
          obtain ⟨after, written, _, _, _⟩ := store.writePlace place resident
          exact ⟨_, .assignResult written⟩
        | tupleHead checked => exact ⟨_, .tupleHead⟩
        | project discard projection =>
          obtain ⟨value, selected, _, _⟩ := projection.access resident
          exact ⟨_, .projectResult selected⟩
        | restore locals discard retained => exact ⟨_, .restore⟩
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

theorem ConfigurationTyped.run {context : StaticContext} {result : ResultType} {before after : Configuration}
    (checkedProgram : program.Checked)
    (typed : ConfigurationTyped program context result before) (run : Run program before after) :
    ConfigurationTyped program context result after := by
  induction run with
  | refl state => exact typed
  | step head tail ih => exact ih (typed.preservation checkedProgram head)

theorem ConfigurationTyped.normal_form {context : StaticContext} {type : Ty} {state : Configuration}
    (typed : ConfigurationTyped program context (.one type) state) (done : Terminal state) :
    ∃ environment value, state = ⟨environment, .result value, []⟩ ∧
      EnvironmentTyped program environment context ∧ ValueHasType program value type := by
  cases done with
  | result environment value =>
    cases typed with | intro store code continuation =>
      cases continuation
      cases code with | result resident => exact ⟨_, _, rfl, store, resident⟩
  | results environment values =>
    cases typed with | intro store code continuation =>
      cases continuation
      cases code


/-- The actual frame exit preserves immutable outer bindings. -/
theorem FrameTyped.frame {current next : StaticContext} {input result : ResultType} {frame : Frame}
    (typed : FrameTyped program current input frame next result) {before after : Environment}
    (framed : EnvironmentFrame current before after) :
    EnvironmentFrame next (frame.environment before) (frame.environment after) := by
  cases typed <;> try exact framed
  case scope locals result discard => simpa [Frame.environment] using framed.drop locals.length
  case restore result caller discard retained => exact retained.frame_refl

theorem ContinuationTyped.frame {current final : StaticContext} {input result : ResultType} {stack : List Frame}
    (typed : ContinuationTyped program current input stack final result) {before after : Environment}
    (framed : EnvironmentFrame current before after) :
    EnvironmentFrame final (continuationEnvironment before stack) (continuationEnvironment after stack) := by
  induction typed generalizing before after with
  | nil => exact framed
  | cons head tail ih => exact ih (head.frame framed)

/-- Every actual step frames the entry-visible environment, even while running
inside nested scopes or recursive callees. -/
theorem ConfigurationTyped.frame_step {context : StaticContext} {result : ResultType} {before after : Configuration}
    (typed : ConfigurationTyped program context result before) (step : Step program before after) :
    EnvironmentFrame context before.outerEnvironment after.outerEnvironment := by
  cases typed with
  | intro store code continuation =>
    cases step <;> try exact continuation.frame store.frame_refl
    case selectedPattern selected =>
      simpa [Configuration.outerEnvironment, continuationEnvironment, Frame.environment] using
        continuation.frame store.frame_refl
    case assignResult written =>
      cases code with | result resident =>
        cases continuation with | cons frame tail =>
          cases frame with | assign selected discard checked =>
            obtain ⟨updated, produced, _, framed, _⟩ := store.writePlace selected resident
            cases Option.some.inj (written.symm.trans produced)
            exact tail.frame framed

theorem ConfigurationTyped.frame_run {context : StaticContext} {result : ResultType} {before after : Configuration}
    (checkedProgram : program.Checked) (typed : ConfigurationTyped program context result before)
    (run : Run program before after) : EnvironmentFrame context before.outerEnvironment after.outerEnvironment := by
  induction run with
  | refl state => cases typed with | intro store code continuation => exact continuation.frame store.frame_refl
  | step head tail ih =>
    exact (typed.frame_step head).trans (ih (typed.preservation checkedProgram head))


end Grounded
