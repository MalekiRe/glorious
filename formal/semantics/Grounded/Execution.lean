import Grounded.Places
import Grounded.Matching
import Grounded.BindingAccess

/-! One shared-heap explicit-frame operational semantics. Retained callers carry
only activation identities and address maps. Allocation, access and retirement
use the authoritative addressed operations; no checking certificates occur here. -/
namespace Grounded

abbrev Environment := AddressedEnvironment

inductive Control where
  | expression (expression : Expr)
  | arguments (expressions : List Expr)
  | result (value : Value)
  | results (values : List Value)

inductive Frame where
  | sequence (rest : Expr)
  | bind (name : BindingId) (slot : BindingType) (body : Expr)
  | scope (count : Nat)
  | assign (place : Place) (rest : Expr)
  | tupleHead (tail : List Expr)
  | tupleTail (head : Value)
  | project (key : FieldKey)
  | array
  | construct (identity : Nat) (tag : Option Nat)
  | call (declaration : FunctionDecl)
  | patterns (arms : List (Pattern × Expr))
  | restore (scope : AddressedScope)
  | argumentHead (tail : List Expr)
  | argumentTail (head : Value)

def Frame.activation (frame : Frame) (current : ActivationId) : ActivationId :=
  match frame with
  | .restore caller => caller.activation
  | _ => current

/-- The observable outer scope in the current shared heap. This is a view,
not a retirement operation and not a saved heap or allocation supply. -/
def Frame.environment (frame : Frame) (current : Environment) : Environment :=
  { current with
    activation := frame.activation current.activation
    bindings := match frame with
      | .scope count => current.bindings.drop count
      | .restore caller => caller.bindings
      | _ => current.bindings }

def continuationEnvironment (current : Environment) : List Frame → Environment
  | [] => current
  | frame :: rest => continuationEnvironment (frame.environment current) rest


structure Configuration where
  environment : Environment
  control : Control
  continuation : List Frame

def Configuration.outerEnvironment (state : Configuration) : Environment :=
  continuationEnvironment state.environment state.continuation


inductive Terminal : Configuration → Prop where
  | result (environment : Environment) (value : Value) : Terminal ⟨environment, .result value, []⟩
  | results (environment : Environment) (values : List Value) : Terminal ⟨environment, .results values, []⟩


/-- Runtime transitions use actual lookup, replacement and first-match results.
Invalid access has no transition; it is not an exhaustion or abort outcome. -/
inductive Step (program : Program) : Configuration → Configuration → Prop where
  | unit {env : Environment} {stack : List Frame} :
      Step program ⟨env, .expression .unit, stack⟩ ⟨env, .result .unit, stack⟩
  | integer {env : Environment} {stack : List Frame} {type : IntegerType} {magnitude : Nat}
      (fits : type.Contains program.target magnitude) :
      Step program ⟨env, .expression (.integer type magnitude), stack⟩
        ⟨env, .result (.integer type magnitude), stack⟩
  | character {env : Environment} {stack : List Frame} {number : Nat}
      (valid : UnicodeScalar number) :
      Step program ⟨env, .expression (.character number), stack⟩ ⟨env, .result (.character number), stack⟩
  | group {env : Environment} {stack : List Frame} {body : Expr} :
      Step program ⟨env, .expression (.group body), stack⟩ ⟨env, .expression body, stack⟩
  | read {env : Environment} {stack : List Frame} {place : Place} {value : Value}
      (selected : env.read program place = some value) :
      Step program ⟨env, .expression (.read place), stack⟩ ⟨env, .result value, stack⟩
  | move {env after : Environment} {stack : List Frame} {place : Place} {value : Value}
      (taken : env.take program place = some (value, after)) :
      Step program ⟨env, .expression (.move place), stack⟩ ⟨after, .result value, stack⟩
  | sequence {env : Environment} {stack : List Frame} {first rest : Expr} :
      Step program ⟨env, .expression (.sequence first rest), stack⟩
        ⟨env, .expression first, .sequence rest :: stack⟩
  | sequenceResult {env : Environment} {stack : List Frame} {value : Value} {rest : Expr} :
      Step program ⟨env, .result value, .sequence rest :: stack⟩ ⟨env, .expression rest, stack⟩
  | bind {env : Environment} {stack : List Frame} {mutable : Bool} {name : BindingId}
      {localType : Ty} {initial body : Expr} :
      Step program ⟨env, .expression (.bind mutable name localType initial body), stack⟩
        ⟨env, .expression initial, .bind name ⟨localType, mutable⟩ body :: stack⟩
  | bindResult {env : Environment} {stack : List Frame} {name : BindingId} {slot : BindingType} {body : Expr} {value : Value} :
      Step program ⟨env, .result value, .bind name slot body :: stack⟩
        ⟨env.extend [⟨name, slot, value⟩], .expression body, .scope 1 :: stack⟩
  | scope {env after : Environment} {stack : List Frame} {count : Nat} {value : Value}
      (exited : env.exitScope count = some after) :
      Step program ⟨env, .result value, .scope count :: stack⟩
        ⟨after, .result value, stack⟩
  | assign {env : Environment} {stack : List Frame} {place : Place} {value rest : Expr} :
      Step program ⟨env, .expression (.assign place value rest), stack⟩
        ⟨env, .expression value, .assign place rest :: stack⟩
  | assignResult {env after : Environment} {stack : List Frame} {place : Place} {rest : Expr} {value : Value}
      (written : env.write program place value = some after) :
      Step program ⟨env, .result value, .assign place rest :: stack⟩ ⟨after, .expression rest, stack⟩
  | tuple {env : Environment} {stack : List Frame} {head : Expr} {tail : List Expr} :
      Step program ⟨env, .expression (.tuple head tail), stack⟩
        ⟨env, .expression head, .tupleHead tail :: stack⟩
  | tupleHead {env : Environment} {stack : List Frame} {head : Value} {tail : List Expr} :
      Step program ⟨env, .result head, .tupleHead tail :: stack⟩
        ⟨env, .arguments tail, .tupleTail head :: stack⟩
  | tupleTail {env : Environment} {stack : List Frame} {head : Value} {tail : List Value} :
      Step program ⟨env, .results tail, .tupleTail head :: stack⟩ ⟨env, .result (.tuple head tail), stack⟩
  | project {env : Environment} {stack : List Frame} {body : Expr} {key : FieldKey} :
      Step program ⟨env, .expression (.project body key), stack⟩
        ⟨env, .expression body, .project key :: stack⟩
  | projectResult {env : Environment} {stack : List Frame} {aggregate value : Value} {key : FieldKey} {index : Nat}
      (selected : aggregate.projectField program key = some (index, value)) :
      Step program ⟨env, .result aggregate, .project key :: stack⟩ ⟨env, .result value, stack⟩
  | array {env : Environment} {stack : List Frame} {elements : List Expr} :
      Step program ⟨env, .expression (.array elements), stack⟩ ⟨env, .arguments elements, .array :: stack⟩
  | arrayResult {env : Environment} {stack : List Frame} {values : List Value} :
      Step program ⟨env, .results values, .array :: stack⟩ ⟨env, .result (.array values), stack⟩
  | constant {env : Environment} {stack : List Frame} {name : String} {declaration : ConstantDecl}
      (declared : program.constants name = some declaration) :
      Step program ⟨env, .expression (.constant name), stack⟩
        ⟨enterBindings env.heap env.supply [], .expression declaration.body, .restore env.scope :: stack⟩
  | restore {env after : Environment} {caller : AddressedScope} {stack : List Frame} {value : Value}
      (restored : env.restore caller = some after) :
      Step program ⟨env, .result value, .restore caller :: stack⟩
        ⟨after, .result value, stack⟩
  | construct {env : Environment} {stack : List Frame} {identity : Nat} {tag : Option Nat} {fields : List Expr} :
      Step program ⟨env, .expression (.construct identity tag fields), stack⟩
        ⟨env, .arguments fields, .construct identity tag :: stack⟩
  | constructResult {env : Environment} {stack : List Frame} {identity : Nat} {tag : Option Nat} {fields : List Value} :
      Step program ⟨env, .results fields, .construct identity tag :: stack⟩
        ⟨env, .result (.nominal identity tag fields), stack⟩
  | call {env : Environment} {stack : List Frame} {identity : Nat} {arguments : List Expr} {declaration : FunctionDecl}
      (declared : program.functions identity = some declaration) :
      Step program ⟨env, .expression (.call identity arguments), stack⟩
        ⟨env, .arguments arguments, .call declaration :: stack⟩
  | callInputs {env : Environment} {stack : List Frame} {declaration : FunctionDecl} {values : List Value}
      {inputs : List BindingInput} (prepared : prepareBindings declaration.parameters values = some inputs) :
      Step program ⟨env, .results values, .call declaration :: stack⟩
        ⟨enterBindings env.heap env.supply inputs, .expression declaration.body, .restore env.scope :: stack⟩
  | applyPatterns {env : Environment} {stack : List Frame} {inputs : List Ty} {arguments : List Expr} {arms : List (Pattern × Expr)} :
      Step program ⟨env, .expression (.applyPatterns inputs arguments arms), stack⟩
        ⟨env, .arguments arguments, .patterns arms :: stack⟩
  | selectedPattern {env : Environment} {bindings : List BindingInput} {stack : List Frame} {values : List Value}
      {arms : List (Pattern × Expr)} {body : Expr}
      (selected : selectArm (argumentValue values) arms = some (bindings, body)) :
      Step program ⟨env, .results values, .patterns arms :: stack⟩
        ⟨env.extend bindings, .expression body, .scope bindings.length :: stack⟩
  | nil {env : Environment} {stack : List Frame} :
      Step program ⟨env, .arguments [], stack⟩ ⟨env, .results [], stack⟩
  | cons {env : Environment} {stack : List Frame} {head : Expr} {tail : List Expr} :
      Step program ⟨env, .arguments (head :: tail), stack⟩
        ⟨env, .expression head, .argumentHead tail :: stack⟩
  | argumentHead {env : Environment} {stack : List Frame} {head : Value} {tail : List Expr} :
      Step program ⟨env, .result head, .argumentHead tail :: stack⟩
        ⟨env, .arguments tail, .argumentTail head :: stack⟩
  | argumentTail {env : Environment} {stack : List Frame} {head : Value} {tail : List Value} :
      Step program ⟨env, .results tail, .argumentTail head :: stack⟩
        ⟨env, .results (head :: tail), stack⟩

inductive Run (program : Program) : Configuration → Configuration → Prop where
  | refl (state : Configuration) : Run program state state
  | step {before middle after : Configuration} (head : Step program before middle)
      (tail : Run program middle after) : Run program before after

variable {program : Program}

/-- Distinct lexical roots frame reads only when their storage identities are
distinct. This is a pre-state separation condition, not a post-state promise. -/
theorem Step.assignment_frame {before : Environment} {after : Configuration} {stack : List Frame}
    {place other : Place} {rest : Expr} {value : Value}
    (distinct : (before.bindings.map Prod.snd).Nodup)
    (step : Step program ⟨before, .result value, .assign place rest :: stack⟩ after)
    (different : other.root ≠ place.root) :
    after.environment.read program other = before.read program other := by
  cases step with
  | assignResult written =>
    obtain ⟨heap, stored, same⟩ := Option.map_eq_some_iff.mp written
    cases same
    exact BindingMap.restore.read_other distinct stored different


/-- Raw malformed invocations cannot enter a body by silently dropping either
parameters or arguments. This holds independently of source admission. -/
theorem Step.call_arity {env : Environment} {stack : List Frame} {declaration : FunctionDecl}
    {values : List Value} {after : Configuration}
    (step : Step program ⟨env, .results values, .call declaration :: stack⟩ after) :
    declaration.parameters.length = values.length := by
  cases step with
  | callInputs prepared => exact prepareBindings.arity prepared

theorem Terminal.no_step {state next : Configuration} (done : Terminal state) : ¬ Step program state next := by
  intro step
  cases done <;> cases step


def Configuration.extend (state : Configuration) (tail : List Frame) : Configuration :=
  { state with continuation := state.continuation ++ tail }

theorem Step.extend {before after : Configuration} (step : Step program before after) (tail : List Frame) :
    Step program (before.extend tail) (after.extend tail) := by
  cases step <;> constructor <;> assumption

theorem Run.extend {before after : Configuration} (run : Run program before after) (tail : List Frame) :
    Run program (before.extend tail) (after.extend tail) := by
  induction run with
  | refl state => exact .refl _
  | step head rest ih => exact .step (head.extend tail) ih

theorem Run.trans {first middle last : Configuration} (front : Run program first middle)
    (back : Run program middle last) : Run program first last := by
  induction front with
  | refl state => exact back
  | step head rest ih => exact .step head (ih back)

/-- Until a subcomputation has a terminal control, its caller frames cannot
participate in a transition. This is an operational fact, not admission evidence. -/
theorem Step.unextend {before after : Configuration} {tail : List Frame}
    (step : Step program (before.extend tail) after)
    (active : ¬ Terminal before) :
    ∃ next, Step program before next ∧ after = next.extend tail := by
  rcases before with ⟨environment, control, stack⟩
  cases stack with
  | nil =>
    cases control with
    | result value => exact False.elim (active (.result _ _))
    | results values => exact False.elim (active (.results _ _))
    | expression expression =>
      cases step <;> exact ⟨_, by constructor <;> assumption, rfl⟩
    | arguments arguments =>
      cases step <;> exact ⟨_, by constructor <;> assumption, rfl⟩
  | cons frame stack =>
    cases control <;> cases frame <;> cases step <;>
      exact ⟨_, by constructor <;> assumption, rfl⟩

/-- A prefix either still executes above the saved continuation or has reached
its first terminal control and then continued through that saved continuation. -/
theorem Run.decompose_extension {before after : Configuration} (run : Run program before after) :
    ∀ (base : Configuration) (tail : List Frame), before = base.extend tail →
      (∃ current, Run program base current ∧ after = current.extend tail) ∨
      (∃ done, Terminal done ∧ Run program base done ∧ Run program (done.extend tail) after) := by
  induction run with
  | refl state =>
    intro base tail same
    exact .inl ⟨base, .refl _, same⟩
  | step head rest ih =>
    intro base tail same
    subst_vars
    by_cases terminal : Terminal base
    · exact .inr ⟨base, terminal, .refl _, .step head rest⟩
    · obtain ⟨next, step, same⟩ := head.unextend terminal
      rcases ih next tail same with ⟨current, front, final⟩ | ⟨done, terminal, front, back⟩
      · exact .inl ⟨current, .step step front, final⟩
      · exact .inr ⟨done, terminal, .step step front, back⟩

/-- Any run that consumes a retained frame first completes the computation
above it. Extract both actual runs, without a termination assumption. -/
theorem Run.unextend {before after : Configuration} (run : Run program before after) :
    ∀ (base : Configuration) (tail : List Frame), before = base.extend tail →
      after.continuation.length < tail.length →
      ∃ done, Terminal done ∧ Run program base done ∧ Run program (done.extend tail) after := by
  intro base tail same shorter
  rcases run.decompose_extension base tail same with ⟨current, _, final⟩ | completed
  · subst after
    simp only [Configuration.extend, List.length_append] at shorter
    omega
  · exact completed



theorem Step.unique {before first second : Configuration} (left : Step program before first)
    (right : Step program before second) : second = first := by
  cases left <;> cases right <;> simp_all

theorem Run.unique {before first second : Configuration} (left : Run program before first)
    (right : Run program before second)
    (leftDone : ∀ state, ¬ Step program first state)
    (rightDone : ∀ state, ¬ Step program second state) : second = first := by
  induction left generalizing second with
  | refl state =>
    cases right with
    | refl => rfl
    | step head tail => exact False.elim (leftDone _ head)
  | step head tail ih =>
    cases right with
    | refl => exact False.elim (rightDone _ head)
    | step other rest =>
      cases head.unique other
      exact ih rest leftDone rightDone

/-- An infinite execution contains an actual machine step at every index.
There is no fuel limit, stuttering transition or assumed evaluator. -/
structure InfiniteRun (program : Program) (before : Configuration)
    (trace : Nat → Configuration) : Prop where
  initial : trace 0 = before
  steps : ∀ index, Step program (trace index) (trace (index + 1))

theorem InfiniteRun.prefix {before : Configuration} {trace : Nat → Configuration}
    (infinite : InfiniteRun program before trace) (index : Nat) :
    Run program before (trace index) := by
  induction index with
  | zero => rw [infinite.initial]; exact .refl _
  | succ index ih => exact ih.trans (.step (infinite.steps index) (.refl _))

/-- Infinite behavior is also deterministic, not merely finite terminal results. -/
theorem InfiniteRun.unique {before : Configuration} {first second : Nat → Configuration}
    (left : InfiniteRun program before first) (right : InfiniteRun program before second) :
    first = second := by
  funext index
  induction index with
  | zero => exact left.initial.trans right.initial.symm
  | succ index ih =>
    have step := left.steps index
    rw [ih] at step
    exact (step.unique (right.steps index)).symm


/-- Determinism makes finite terminal execution and infinite execution exclusive. -/
theorem Run.excludes_infinite {before after : Configuration}
    (run : Run program before after) (done : Terminal after) :
    ∀ trace, ¬ InfiniteRun program before trace := by
  induction run with
  | refl state =>
    intro trace infinite
    exact done.no_step (by simpa only [infinite.initial] using infinite.steps 0)
  | step head tail ih =>
    intro trace infinite
    have first := infinite.steps 0
    rw [infinite.initial] at first
    have same := head.unique first
    exact ih done (fun index => trace (index + 1)) ⟨same, fun index => infinite.steps (index + 1)⟩

/-- Finite setup composes with an infinite execution using only actual steps. -/
theorem Run.prepend_infinite {before after : Configuration} (run : Run program before after)
    {trace : Nat → Configuration} (infinite : InfiniteRun program after trace) :
    ∃ whole, InfiniteRun program before whole := by
  induction run with
  | refl => exact ⟨trace, infinite⟩
  | @step before middle after head tail ih =>
    obtain ⟨continued, execution⟩ := ih infinite
    refine ⟨(fun index => match index with | 0 => before | index + 1 => continued index), rfl, ?_⟩
    intro index
    cases index with
    | zero => simpa only [execution.initial] using head
    | succ index => exact execution.steps index


/-- Reachable-state progress constructs an unbounded execution when no terminal
state is reachable. Source consumers derive progress from preservation. -/
theorem Run.terminal_or_infinite (before : Configuration)
    (progress : ∀ state, Run program before state → Terminal state ∨ ∃ next, Step program state next) :
    (∃ after, Run program before after ∧ Terminal after) ∨
      ∃ trace, InfiniteRun program before trace := by
  classical
  by_cases finished : ∃ after, Run program before after ∧ Terminal after
  · exact .inl finished
  · right
    have successor : ∀ current : {state // Run program before state},
        ∃ next : {state // Run program before state}, Step program current.val next.val := by
      intro current
      rcases progress current.val current.property with done | ⟨next, step⟩
      · exact False.elim (finished ⟨current.val, current.property, done⟩)
      · exact ⟨⟨next, current.property.trans (.step step (.refl _))⟩, step⟩
    let states : Nat → {state // Run program before state} :=
      Nat.rec ⟨before, .refl _⟩ (fun _ current => Classical.choose (successor current))
    exact ⟨fun index => (states index).val, rfl, fun index => Classical.choose_spec (successor (states index))⟩


theorem Frame.scope_extension (current : Environment) (inputs : List BindingInput) :
    (Frame.scope inputs.length).environment (current.extend inputs) =
      { current with heap := (allocateBindings current.heap current.activation inputs).2 } := by
  have length := congrArg List.length (allocateBindings.keys current.heap current.activation inputs)
  simp only [List.length_map] at length
  simp only [Frame.environment, Frame.activation, AddressedEnvironment.extend]
  rw [← length]
  simp


theorem Frame.scope_congr {before after : Environment}
    (same : after.scope = before.scope) (frame : Frame) :
    (frame.environment after).scope = (frame.environment before).scope := by
  have activation := congrArg AddressedScope.activation same
  have bindings := congrArg AddressedScope.bindings same
  simp only [AddressedEnvironment.scope] at activation bindings
  cases frame <;> simp [Frame.environment, Frame.activation, AddressedEnvironment.scope, activation, bindings]

theorem continuationEnvironment.scope_congr {before after : Environment}
    (same : after.scope = before.scope) (stack : List Frame) :
    (continuationEnvironment after stack).scope = (continuationEnvironment before stack).scope := by
  induction stack generalizing before after with
  | nil => exact same
  | cons frame rest ih => exact ih (frame.scope_congr same)

/-- Even raw operational transitions preserve the externally visible scope.
This says nothing about resident availability or equality of heap cells. -/
theorem Step.outer_scope {before after : Configuration} (step : Step program before after) :
    after.outerEnvironment.scope = before.outerEnvironment.scope := by
  cases step <;> try rfl
  case move after stack place value taken =>
    obtain ⟨result, _, same⟩ := Option.map_eq_some_iff.mp taken
    cases same
    apply continuationEnvironment.scope_congr
    rfl
  case bindResult env stack name slot body value =>
    change (continuationEnvironment ((Frame.scope 1).environment (env.extend [⟨name, slot, value⟩])) stack).scope = _
    have extended := Frame.scope_extension env [⟨name, slot, value⟩]
    simp only [List.length_cons, List.length_nil] at extended
    rw [extended]
    apply continuationEnvironment.scope_congr
    rfl
  case scope env after stack count value exited =>
    obtain ⟨heap, _, same⟩ := Option.map_eq_some_iff.mp exited
    cases same
    apply continuationEnvironment.scope_congr
    rfl
  case assignResult env after stack place rest value written =>
    obtain ⟨heap, _, same⟩ := Option.map_eq_some_iff.mp written
    cases same
    apply continuationEnvironment.scope_congr
    rfl
  case restore env after caller stack value restored =>
    obtain ⟨heap, _, same⟩ := Option.map_eq_some_iff.mp restored
    cases same
    apply continuationEnvironment.scope_congr
    rfl
  case selectedPattern env bindings stack values arms body selected =>
    change (continuationEnvironment ((Frame.scope bindings.length).environment (env.extend bindings)) stack).scope = _
    rw [Frame.scope_extension]
    apply continuationEnvironment.scope_congr
    rfl
  case constant =>
    simp only [Configuration.outerEnvironment, continuationEnvironment]
    apply continuationEnvironment.scope_congr
    rfl
  case callInputs =>
    simp only [Configuration.outerEnvironment, continuationEnvironment]
    apply continuationEnvironment.scope_congr
    rfl

theorem Run.outer_scope {before after : Configuration} (run : Run program before after) :
    after.outerEnvironment.scope = before.outerEnvironment.scope := by
  induction run with
  | refl => rfl
  | step head tail ih => exact ih.trans head.outer_scope


/-- An actual assignment preserves disjoint field observations even when the
lexical places resolve to the same storage identity. -/
theorem Step.assignment_frame_disjoint {before : Environment} {after : Configuration}
    {stack : List Frame} {place other : Place} {rest : Expr} {value : Value}
    {identity : StorageId} {cell : StorageCell} {home : Module}
    (mapped : lookup place.root before.bindings = some identity)
    (otherMapped : lookup other.root before.bindings = some identity)
    (found : before.heap.read identity = some cell)
    (apart : PathDisjoint program home cell.type place.fields other.fields)
    (step : Step program ⟨before, .result value, .assign place rest :: stack⟩ after) :
    after.environment.read program other = before.read program other := by
  cases step with
  | assignResult written =>
    obtain ⟨heap, stored, same⟩ := Option.map_eq_some_iff.mp written
    cases same
    exact BindingMap.restore.read_disjoint mapped otherMapped found apart stored

/-- Moving one owned field does not consume any pre-state-disjoint field. -/
theorem Step.move_frame_disjoint {before : Environment} {after : Configuration}
    {stack : List Frame} {place other : Place}
    {identity : StorageId} {cell : StorageCell} {home : Module}
    (mapped : lookup place.root before.bindings = some identity)
    (otherMapped : lookup other.root before.bindings = some identity)
    (found : before.heap.read identity = some cell)
    (apart : PathDisjoint program home cell.type place.fields other.fields)
    (step : Step program ⟨before, .expression (.move place), stack⟩ after) :
    after.environment.read program other = before.read program other := by
  cases step with
  | move taken =>
    obtain ⟨⟨owner, heap⟩, stored, same⟩ := Option.map_eq_some_iff.mp taken
    cases same
    exact BindingMap.take.read_disjoint mapped otherMapped found apart stored


/-- Every machine transition uses the existing allocation/write/retirement
history. This includes callee entry, caller restoration and selected-arm scopes. -/
theorem Step.heap_history {before after : Configuration} (step : Step program before after) :
    RuntimeHeap.History before.environment.heap after.environment.heap := by
  cases step with
  | move taken =>
    obtain ⟨⟨value, heap⟩, operation, same⟩ := Option.map_eq_some_iff.mp taken
    cases same
    obtain ⟨identity, _, raw⟩ := Option.bind_eq_some_iff.mp operation
    exact StorageAddress.take.history raw
  | assignResult written =>
    obtain ⟨heap, operation, same⟩ := Option.map_eq_some_iff.mp written
    cases same
    obtain ⟨identity, _, raw⟩ := Option.bind_eq_some_iff.mp operation
    exact StorageAddress.restore.history raw
  | scope exited =>
    obtain ⟨heap, released, same⟩ := Option.map_eq_some_iff.mp exited
    cases same
    exact RuntimeHeap.retireMany_history released
  | restore restored =>
    obtain ⟨heap, released, same⟩ := Option.map_eq_some_iff.mp restored
    cases same
    exact RuntimeHeap.retireMany_history released
  | bindResult => exact allocateBindings.history _ _ _
  | selectedPattern _ => exact allocateBindings.history _ _ _
  | constant _ => exact allocateBindings.history _ _ _
  | callInputs _ => exact allocateBindings.history _ _ _
  | _ => exact .refl _

theorem Run.heap_history {before after : Configuration} (run : Run program before after) :
    RuntimeHeap.History before.environment.heap after.environment.heap := by
  induction run with
  | refl => exact .refl _
  | step head rest ih => exact head.heap_history.trans ih

/-- Once retired, an issued storage identity stays retired through every actual
execution prefix, including recursive calls and further allocations. -/
theorem Run.retired {before after : Configuration} {identity : StorageId}
    (run : Run program before after) (retired : before.environment.heap.Retired identity) :
    after.environment.heap.Retired identity := retired.history run.heap_history

/-- Reusing a lexical spelling cannot revive its old storage identity. Even an
untyped stale binding map cannot read, move or restore that retired storage. -/
theorem Run.retired_inaccessible {before after : Configuration} {identity : StorageId}
    (run : Run program before after) (retired : before.environment.heap.Retired identity)
    {place : Place} (mapped : lookup place.root after.environment.bindings = some identity) :
    after.environment.read program place = none ∧
    after.environment.take program place = none ∧
    ∀ value, after.environment.write program place value = none := by
  have absent := (run.retired retired).2
  constructor
  · simp [AddressedEnvironment.read, BindingMap.read, BindingMap.resolve, StorageAddress.read, mapped, absent]
  constructor
  · simp [AddressedEnvironment.take, BindingMap.take, BindingMap.resolve, mapped, StorageAddress.take, absent]
  · intro value
    simp [AddressedEnvironment.write, BindingMap.restore, BindingMap.resolve, mapped, StorageAddress.restore, absent]

/-- Actual lexical-scope retirement permanently kills every released identity;
the following run need not return or preserve the original lexical environment. -/
theorem Run.scope_retired {before : Environment} {middle after : Configuration}
    {value : Value} {count : Nat} {stack : List Frame}
    (exit : Step program ⟨before, .result value, .scope count :: stack⟩ middle)
    (run : Run program middle after) {identity : StorageId}
    (member : identity ∈ (List.take count before.bindings).map Prod.snd) :
    after.environment.heap.Retired identity := by
  cases exit with
  | scope exited =>
    obtain ⟨heap, released, same⟩ := Option.map_eq_some_iff.mp exited
    cases same
    exact run.retired (releaseBindings.retired released identity member)

/-- Returning from a function retires its own binding identities, not the
caller's names; no subsequent execution can allocate those identities again. -/
theorem Run.return_retired {before : Environment} {middle after : Configuration}
    {value : Value} {caller : AddressedScope} {stack : List Frame}
    (exit : Step program ⟨before, .result value, .restore caller :: stack⟩ middle)
    (run : Run program middle after) {identity : StorageId}
    (member : identity ∈ before.bindings.map Prod.snd) :
    after.environment.heap.Retired identity := by
  cases exit with
  | restore restored =>
    obtain ⟨heap, released, same⟩ := Option.map_eq_some_iff.mp restored
    cases same
    exact run.retired (releaseBindings.retired released identity member)

/-- Finishing a body through its real return frame permanently retires the
entry bindings, even when the body performs nested calls or lexical allocations. -/
theorem Run.body_return_retires {entry after : Environment} {caller : AddressedScope}
    {body : Expr} {value : Value}
    (run : Run program ⟨entry, .expression body, [.restore caller]⟩ ⟨after, .result value, []⟩) :
    ∀ identity ∈ entry.bindings.map Prod.snd, after.heap.Retired identity := by
  obtain ⟨done, terminal, bodyRun, suffix⟩ := run.unextend
    ⟨entry, .expression body, []⟩ [.restore caller] rfl (by simp)
  cases terminal with
  | result current resident =>
    have bindings : current.bindings = entry.bindings :=
      congrArg AddressedScope.bindings bodyRun.outer_scope
    cases suffix with
    | step head tail =>
      intro identity member
      apply Run.return_retired head tail
      simpa only [bindings] using member
  | results current residents =>
    cases suffix with
    | step head tail => cases head

/-- A completed invocation witnesses actual parameter preparation and retirement
of the corresponding fresh callee cells, not merely a compatible final heap. -/
theorem Run.call_cleanup {before after : Environment} {declaration : FunctionDecl}
    {values : List Value} {value : Value}
    (run : Run program ⟨before, .results values, [.call declaration]⟩ ⟨after, .result value, []⟩) :
    ∃ inputs, prepareBindings declaration.parameters values = some inputs ∧
      ∀ identity ∈ (enterBindings before.heap before.supply inputs).bindings.map Prod.snd,
        after.heap.Retired identity := by
  cases run with
  | step head tail =>
    cases head with
    | callInputs prepared => exact ⟨_, prepared, tail.body_return_retires⟩


/-- An already-issued storage identity can survive a step only with its
original allocation owner and declared type; only its resident may change. -/
theorem Step.storage_origin {before after : Configuration} (step : Step program before after)
    {identity : StorageId} (allocated : identity.index < before.environment.heap.next)
    {result : StorageCell} (found : after.environment.heap.read identity = some result) :
    ∃ old, before.environment.heap.read identity = some old ∧
      result.activation = old.activation ∧ result.type = old.type := by
  cases step with
  | move taken =>
    obtain ⟨⟨value, heap⟩, operation, same⟩ := Option.map_eq_some_iff.mp taken
    cases same
    obtain ⟨address, _, raw⟩ := Option.bind_eq_some_iff.mp operation
    exact StorageAddress.take.identity raw found
  | assignResult written =>
    obtain ⟨heap, operation, same⟩ := Option.map_eq_some_iff.mp written
    cases same
    obtain ⟨address, _, raw⟩ := Option.bind_eq_some_iff.mp operation
    exact StorageAddress.restore.identity raw found
  | scope exited =>
    obtain ⟨heap, released, same⟩ := Option.map_eq_some_iff.mp exited
    cases same
    exact ⟨result, RuntimeHeap.retireMany_origin released found, rfl, rfl⟩
  | restore restored =>
    obtain ⟨heap, released, same⟩ := Option.map_eq_some_iff.mp restored
    cases same
    exact ⟨result, RuntimeHeap.retireMany_origin released found, rfl, rfl⟩
  | bindResult => exact ⟨result, (allocateBindings.old _ _ _ allocated).symm.trans found, rfl, rfl⟩
  | selectedPattern _ => exact ⟨result, (allocateBindings.old _ _ _ allocated).symm.trans found, rfl, rfl⟩
  | constant _ => exact ⟨result, (allocateBindings.old _ _ _ allocated).symm.trans found, rfl, rfl⟩
  | callInputs _ => exact ⟨result, (allocateBindings.old _ _ _ allocated).symm.trans found, rfl, rfl⟩
  | _ => exact ⟨result, found, rfl, rfl⟩

/-- Storage provenance is stable across arbitrary actual runs, including
recursive invocation and temporary initialization holes. No typing is assumed. -/
theorem Run.storage_origin {before after : Configuration} (run : Run program before after)
    {identity : StorageId} (allocated : identity.index < before.environment.heap.next)
    {result : StorageCell} (found : after.environment.heap.read identity = some result) :
    ∃ old, before.environment.heap.read identity = some old ∧
      result.activation = old.activation ∧ result.type = old.type := by
  induction run with
  | refl => exact ⟨result, found, rfl, rfl⟩
  | step head tail ih =>
    obtain ⟨middle, present, owner, type⟩ := ih (Nat.lt_of_lt_of_le allocated head.heap_history.next_le) found
    obtain ⟨old, original, oldOwner, oldType⟩ := head.storage_origin allocated present
    exact ⟨old, original, owner.trans oldOwner, type.trans oldType⟩


/-- A surviving address keeps its exact referent type across actual execution.
Liveness is checked at the observed state; this does not grant future access. -/
theorem Run.address_type {before after : Configuration} (run : Run program before after)
    {address : StorageAddress} {type : Ty}
    (checked : address.Typed program before.environment.heap type)
    (live : ∃ cell, after.environment.heap.read address.root = some cell) :
    address.Typed program after.environment.heap type := by
  cases checked with
  | intro found path =>
    obtain ⟨cell, current⟩ := live
    obtain ⟨old, original, _, declared⟩ :=
      run.storage_origin (before.environment.heap.bounded _ _ found) current
    cases Option.some.inj (found.symm.trans original)
    exact .intro current (by rw [declared]; exact path)

/-- A retired address has no physical referent typing at any later state. -/
theorem Run.retired_untyped {before after : Configuration} (run : Run program before after)
    {address : StorageAddress} (retired : before.environment.heap.Retired address.root) :
    ∀ type, ¬ address.Typed program after.environment.heap type := by
  intro type checked
  cases checked with
  | intro found path =>
    have absent := (run.retired retired).2
    rw [absent] at found
    cases found


/-- Only restore frames retain a separate caller binding map. -/
def Frame.Retains (frame : Frame) (identity : StorageId) : Prop :=
  match frame with
  | .restore caller => identity ∈ caller.bindings.map Prod.snd
  | _ => False

/-- Inspect the existing active and retained binding maps, not a shadow owner table. -/
def Configuration.Untracked (state : Configuration) (identity : StorageId) : Prop :=
  identity ∉ state.environment.bindings.map Prod.snd ∧
    ∀ frame ∈ state.continuation, ¬ frame.Retains identity

/-- A live cell outside every resulting scope cannot have been allocated or
abandoned by this step: it was already live and untracked before the step. -/
theorem Step.untracked_origin {before after : Configuration} (step : Step program before after)
    {identity : StorageId} {cell : StorageCell}
    (untracked : after.Untracked identity) (found : after.environment.heap.read identity = some cell) :
    (∃ old, before.environment.heap.read identity = some old) ∧ before.Untracked identity := by
  cases step <;> simp_all [Configuration.Untracked, Frame.Retains]
  case move env after stack place value taken =>
    obtain ⟨⟨result, heap⟩, operation, same⟩ := Option.map_eq_some_iff.mp taken
    cases same
    obtain ⟨address, _, raw⟩ := Option.bind_eq_some_iff.mp operation
    obtain ⟨old, original, _, _⟩ := StorageAddress.take.identity raw found
    exact ⟨⟨old, original⟩, untracked.1⟩
  case assignResult env after stack place rest value written =>
    obtain ⟨heap, operation, same⟩ := Option.map_eq_some_iff.mp written
    cases same
    obtain ⟨address, _, raw⟩ := Option.bind_eq_some_iff.mp operation
    obtain ⟨old, original, _, _⟩ := StorageAddress.restore.identity raw found
    exact ⟨⟨old, original⟩, untracked.1⟩
  case constant env stack name declaration declared =>
    exact ⟨⟨cell, found⟩, untracked.2.1⟩
  case callInputs env stack declaration values inputs prepared =>
    have outside : identity ∉ (allocateBindings env.heap env.supply.allocate.1 inputs).1.map Prod.snd := by
      simpa [enterBindings] using untracked.1
    exact ⟨⟨cell, (allocateBindings.outside _ _ _ outside).symm.trans found⟩, untracked.2.1⟩
  case bindResult env stack name slot body value =>
    have outside : identity ∉ (env.extend [⟨name, slot, value⟩]).bindings.map Prod.snd := by
      simpa using untracked.1
    have parts : identity ∉ (allocateBindings env.heap env.activation [⟨name, slot, value⟩]).1.map Prod.snd ∧
        identity ∉ env.bindings.map Prod.snd := by
      simpa only [AddressedEnvironment.extend, List.map_append, List.mem_append, not_or] using outside
    exact ⟨⟨cell, (allocateBindings.outside _ _ _ parts.1).symm.trans found⟩, by simpa using parts.2⟩
  case selectedPattern env inputs stack values arms body selected =>
    have outside : identity ∉ (env.extend inputs).bindings.map Prod.snd := by simpa using untracked.1
    have parts : identity ∉ (allocateBindings env.heap env.activation inputs).1.map Prod.snd ∧
        identity ∉ env.bindings.map Prod.snd := by
      simpa only [AddressedEnvironment.extend, List.map_append, List.mem_append, not_or] using outside
    exact ⟨⟨cell, (allocateBindings.outside _ _ _ parts.1).symm.trans found⟩, by simpa using parts.2⟩
  case restore env after caller stack value restored =>
    obtain ⟨heap, released, same⟩ := Option.map_eq_some_iff.mp restored
    cases same
    refine ⟨⟨cell, RuntimeHeap.retireMany_origin released found⟩, ?_, untracked.1⟩
    intro name member
    have absent := (releaseBindings.retired released identity (List.mem_map_of_mem (f := Prod.snd) member)).2
    rw [absent] at found
    cases found
  case scope env after stack count value exited =>
    obtain ⟨heap, released, same⟩ := Option.map_eq_some_iff.mp exited
    cases same
    refine ⟨⟨cell, RuntimeHeap.retireMany_origin released found⟩, ?_⟩
    intro name member
    have split : (name, identity) ∈ List.take count env.bindings ∨ (name, identity) ∈ env.bindings.drop count := by
      rw [← List.mem_append, List.take_append_drop]
      exact member
    rcases split with removed | retained
    · have absent := (releaseBindings.retired released identity (List.mem_map_of_mem (f := Prod.snd) removed)).2
      rw [absent] at found
      cases found
    · exact untracked.1 name retained

/-- Storage accountability composes through arbitrary finite execution. -/
theorem Run.untracked_origin {before after : Configuration} (run : Run program before after)
    {identity : StorageId} {cell : StorageCell}
    (untracked : after.Untracked identity) (found : after.environment.heap.read identity = some cell) :
    (∃ old, before.environment.heap.read identity = some old) ∧ before.Untracked identity := by
  induction run with
  | refl => exact ⟨⟨cell, found⟩, untracked⟩
  | step head tail ih =>
    obtain ⟨⟨middle, live⟩, tracked⟩ := ih untracked found
    exact head.untracked_origin tracked live

/-- Every newly allocated live cell remains in an actual active or retained scope. -/
theorem Run.allocated_tracked {before after : Configuration} (run : Run program before after)
    {identity : StorageId} (fresh : before.environment.heap.next ≤ identity.index)
    {cell : StorageCell} (live : after.environment.heap.read identity = some cell) :
    ¬ after.Untracked identity := by
  intro untracked
  obtain ⟨⟨old, found⟩, _⟩ := run.untracked_origin untracked live
  exact Nat.not_lt_of_ge fresh (before.environment.heap.bounded _ _ found)

/-- A complete return retires all storage allocated during the run, including
nested calls, pattern bindings and locals, not just entry parameters. -/
theorem Run.return_retires_all {before : Configuration} {after : Environment} {value : Value}
    (run : Run program before ⟨after, .result value, []⟩)
    (bounded : ∀ identity ∈ before.outerEnvironment.bindings.map Prod.snd,
      identity.index < before.environment.heap.next) :
    ∀ identity, before.environment.heap.next ≤ identity.index → identity.index < after.heap.next →
      after.heap.Retired identity := by
  intro identity fresh allocated
  refine ⟨allocated, ?_⟩
  cases found : after.heap.read identity with
  | none => rfl
  | some cell =>
    have same := congrArg AddressedScope.bindings run.outer_scope
    change after.bindings = before.outerEnvironment.bindings at same
    have outside : identity ∉ after.bindings.map Prod.snd := by
      intro member
      have original : identity ∈ before.outerEnvironment.bindings.map Prod.snd := by
        simpa only [same] using member
      exact Nat.not_lt_of_ge fresh (bounded identity original)
    exact False.elim (run.allocated_tracked fresh found ⟨outside, by simp⟩)

/-- An already-live cell outside all active and retained scopes is untouched.
This is a pre-state frame condition, not a post-state liveness assumption. -/
theorem Step.untracked_frame {before after : Configuration} (step : Step program before after)
    {identity : StorageId} {cell : StorageCell}
    (untracked : before.Untracked identity) (found : before.environment.heap.read identity = some cell) :
    after.environment.heap.read identity = some cell ∧ after.Untracked identity := by
  cases step <;> simp_all [Configuration.Untracked, Frame.Retains]
  case move env after stack place value taken =>
    obtain ⟨⟨result, heap⟩, operation, same⟩ := Option.map_eq_some_iff.mp taken
    cases same
    obtain ⟨address, resolved, raw⟩ := Option.bind_eq_some_iff.mp operation
    obtain ⟨target, mapped, same⟩ := Option.map_eq_some_iff.mp resolved
    cases same
    have apart : identity ≠ target := by
      intro same; subst target
      exact untracked.1 place.root (lookup.mem mapped)
    simp only [StorageAddress.take, Option.bind_eq_some_iff, Option.map_eq_some_iff] at raw
    obtain ⟨resident, _, selected, _, owner, _, updated, _, next, written, same⟩ := raw
    cases same
    exact ⟨(RuntimeHeap.write_other written apart).trans found, untracked.1⟩
  case assignResult env after stack place rest value written =>
    obtain ⟨heap, operation, same⟩ := Option.map_eq_some_iff.mp written
    cases same
    obtain ⟨address, resolved, raw⟩ := Option.bind_eq_some_iff.mp operation
    obtain ⟨target, mapped, same⟩ := Option.map_eq_some_iff.mp resolved
    cases same
    have apart : identity ≠ target := by
      intro same; subst target
      exact untracked.1 place.root (lookup.mem mapped)
    simp only [StorageAddress.restore, Option.bind_eq_some_iff] at raw
    obtain ⟨resident, _, updated, _, written⟩ := raw
    exact ⟨(RuntimeHeap.write_other written apart).trans found, untracked.1⟩
  case constant env stack name declaration declared =>
    exact ⟨found, by simp [enterBindings, allocateBindings], untracked.1⟩
  case callInputs env stack declaration values inputs prepared =>
    have old := env.heap.bounded _ _ found
    refine ⟨(allocateBindings.old _ _ _ old).trans found, ?_, untracked.1⟩
    intro name member
    have bound := allocateBindings.bounds env.heap env.supply.allocate.1 inputs identity
      (List.mem_map_of_mem (f := Prod.snd) member)
    omega
  case bindResult env stack name slot body value =>
    have old := env.heap.bounded _ _ found
    refine ⟨(allocateBindings.old _ _ _ old).trans found, ?_⟩
    intro other member
    rcases List.mem_append.mp member with fresh | previous
    · have bound := allocateBindings.bounds env.heap env.activation [⟨name, slot, value⟩] identity
        (List.mem_map_of_mem (f := Prod.snd) fresh)
      omega
    · exact untracked.1 other previous
  case selectedPattern env inputs stack values arms body selected =>
    have old := env.heap.bounded _ _ found
    refine ⟨(allocateBindings.old _ _ _ old).trans found, ?_⟩
    intro name member
    rcases List.mem_append.mp member with fresh | previous
    · have bound := allocateBindings.bounds env.heap env.activation inputs identity
        (List.mem_map_of_mem (f := Prod.snd) fresh)
      omega
    · exact untracked.1 name previous
  case restore env after caller stack value restored =>
    obtain ⟨heap, released, same⟩ := Option.map_eq_some_iff.mp restored
    cases same
    have outside : identity ∉ env.bindings.map Prod.snd := by simpa using untracked.1
    exact ⟨(releaseBindings.outside released outside).trans found, untracked.2.1⟩
  case scope env after stack count value exited =>
    obtain ⟨heap, released, same⟩ := Option.map_eq_some_iff.mp exited
    cases same
    have outside : identity ∉ (List.take count env.bindings).map Prod.snd := by
      intro member
      obtain ⟨⟨name, address⟩, included, same⟩ := List.mem_map.mp member
      cases same
      exact untracked.1 name (List.mem_of_mem_take included)
    refine ⟨(releaseBindings.outside released outside).trans found, ?_⟩
    intro name member
    exact untracked.1 name (List.mem_of_mem_drop member)

/-- The entire external live cell survives, including partial residents,
allocation owner and declared type. No future liveness is required. -/
def Configuration.ExternalFrame (before after : Configuration) : Prop :=
  ∀ identity cell, before.Untracked identity → before.environment.heap.read identity = some cell →
    after.environment.heap.read identity = some cell ∧ after.Untracked identity

theorem Run.external_frame {before after : Configuration} (run : Run program before after) :
    before.ExternalFrame after := by
  intro identity cell outside found
  induction run with
  | refl => exact ⟨found, outside⟩
  | step head tail ih =>
    obtain ⟨middle, retained⟩ := head.untracked_frame outside found
    exact ih retained middle

/-- A callee cannot mutate cells outside its entry ownership, even when they
occur in the saved caller. Covers every prefix, including the return cleanup. -/
theorem Run.body_frame {entry : Environment} {after : Configuration} {caller : AddressedScope}
    {body : Expr} {identity : StorageId} {cell : StorageCell}
    (run : Run program ⟨entry, .expression body, [.restore caller]⟩ after)
    (outside : identity ∉ entry.bindings.map Prod.snd)
    (found : entry.heap.read identity = some cell) :
    after.environment.heap.read identity = some cell := by
  have untracked : (⟨entry, .expression body, []⟩ : Configuration).Untracked identity :=
    ⟨outside, by simp⟩
  rcases run.decompose_extension ⟨entry, .expression body, []⟩ [.restore caller] rfl with
    ⟨current, prefixRun, same⟩ | ⟨done, terminal, prefixRun, suffix⟩
  · subst after
    exact (prefixRun.external_frame identity cell untracked found).1
  · obtain ⟨preserved, remaining⟩ := prefixRun.external_frame identity cell untracked found
    cases terminal with
    | result current value =>
      cases suffix with
      | refl => exact preserved
      | step head tail =>
        cases head with
        | restore restored =>
          obtain ⟨heap, released, same⟩ := Option.map_eq_some_iff.mp restored
          cases same
          cases tail with
          | refl => exact (releaseBindings.outside released remaining.1).trans preserved
          | step impossible rest => cases impossible
    | results current values =>
      cases suffix with
      | refl => exact preserved
      | step impossible rest => cases impossible

/-- Actual fresh parameter allocation isolates every already-live caller cell.
No typing, callee termination or post-state liveness premise is needed. -/
theorem Run.call_frame {before : Environment} {after : Configuration} {declaration : FunctionDecl}
    {values : List Value} (run : Run program ⟨before, .results values, [.call declaration]⟩ after)
    {identity : StorageId} {cell : StorageCell} (found : before.heap.read identity = some cell) :
    after.environment.heap.read identity = some cell := by
  cases run with
  | refl => exact found
  | step head tail =>
    cases head with
    | callInputs prepared =>
      have old := before.heap.bounded _ _ found
      apply tail.body_frame
      · intro member
        have bound := allocateBindings.bounds before.heap before.supply.allocate.1 _ identity member
        omega
      · exact (allocateBindings.old _ _ _ old).trans found

end Grounded
