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
      (state.environment.bindings.map Prod.fst).Nodup ∧ state.StorageCleanupSafe program := by
  have entry := ConfigurationTyped.entry checked store issued
  have current := entry.run checkedProgram run
  exact ⟨current, current.progress, entry.consumption_run checkedProgram run, current.bindings_distinct, current.storage_cleanup_safe⟩

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
  exact PartialValue.Disposable.not_exact_resident declared restricted
    (checked.soundness checkedProgram store issued run).2.2.2.2

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
    (resident : cell.resident = .resident (.nominal identity tag fields)) :
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
    (resident : cell.resident = .resident (.nominal identity tag fields)) :
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
    (selected : cell.resident.selectFields program cell.type place.fields =
      some (.resident (.nominal identity tag fields))) : False := by
  exact BindingMap.ReplacementSafe.not_exact
    (checked.soundness checkedProgram store issued run).2.2.2.2 mapped found declared restricted selected


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

