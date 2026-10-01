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
    exact BindingMap.Disposable.release_preserves_nondiscardable disposition released found path resident required

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
    exact BindingMap.Disposable.release_preserves_nondiscardable disposition released found path resident required


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
    exact BindingMap.Disposable.release_preserves_exact disposition released found declared restricted resident

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
    exact BindingMap.Disposable.release_preserves_exact disposition released found declared restricted resident

/-- Selection is observed after RHS evaluation. A moved-out slot may be restored,
but a still-live exact selected owner cannot be overwritten. -/
theorem HasType.no_exact_overwrite (checkedProgram : program.Checked)
    {context final : FlowContext} {expression : Expr} {type : Ty}
    (checked : HasType program home context expression type final)
    {environment current : Environment}
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
    (issued : environment.supply.Issued environment.activation)
    {value : Value} {place : Place} {rest : Expr} {stack : List Frame}
    (run : Run program ⟨environment, .expression expression, []⟩
      ⟨current, .result value, .assign place rest :: stack⟩)
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
    {value : Value} {place : Place} {rest : Expr} {stack : List Frame}
    (run : Run program ⟨environment, .expression expression, []⟩
      ⟨current, .result value, .assign place rest :: stack⟩)
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

end Grounded

