import Grounded.Places
import Grounded.Matching

/-! One explicit-frame operational semantics. Frames retain actual pending values,
caller environments and scope boundaries. No checking or execution certificate
occurs in a runtime configuration. Storage is still the logical lexical store. -/
namespace Grounded

abbrev Environment := List (BindingId × Value)

inductive Control where
  | expression (expression : Expr)
  | arguments (expressions : List Expr)
  | result (value : Value)
  | results (values : List Value)

inductive Frame where
  | sequence (rest : Expr)
  | bind (name : BindingId) (localType : Ty) (body : Expr)
  | scope (count : Nat)
  | assign (place : Place) (rest : Expr)
  | tupleHead (tail : List Expr)
  | tupleTail (head : Value)
  | project (key : FieldKey)
  | array
  | construct (identity : Nat) (tag : Option Nat)
  | call (declaration : FunctionDecl)
  | patterns (arms : List (Pattern × Expr))
  | restore (environment : Environment)
  | argumentHead (tail : List Expr)
  | argumentTail (head : Value)

/-- The environment exposed outside a frame. This is the same scope/return
operation used by execution; it does not execute any pending expression. -/
def Frame.environment (frame : Frame) (current : Environment) : Environment :=
  match frame with
  | .scope count => current.drop count
  | .restore caller => caller
  | _ => current

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
      (selected : readPlace program place env = some value) :
      Step program ⟨env, .expression (.read place), stack⟩ ⟨env, .result value, stack⟩
  | sequence {env : Environment} {stack : List Frame} {first rest : Expr} :
      Step program ⟨env, .expression (.sequence first rest), stack⟩
        ⟨env, .expression first, .sequence rest :: stack⟩
  | sequenceResult {env : Environment} {stack : List Frame} {value : Value} {rest : Expr} :
      Step program ⟨env, .result value, .sequence rest :: stack⟩ ⟨env, .expression rest, stack⟩
  | bind {env : Environment} {stack : List Frame} {mutable : Bool} {name : BindingId}
      {localType : Ty} {initial body : Expr} :
      Step program ⟨env, .expression (.bind mutable name localType initial body), stack⟩
        ⟨env, .expression initial, .bind name localType body :: stack⟩
  | bindResult {env : Environment} {stack : List Frame} {name : BindingId} {localType : Ty} {body : Expr} {value : Value} :
      Step program ⟨env, .result value, .bind name localType body :: stack⟩
        ⟨(name, value) :: env, .expression body, .scope 1 :: stack⟩
  | scope {env : Environment} {stack : List Frame} {count : Nat} {value : Value} :
      Step program ⟨env, .result value, .scope count :: stack⟩
        ⟨(Frame.scope count).environment env, .result value, stack⟩
  | assign {env : Environment} {stack : List Frame} {place : Place} {value rest : Expr} :
      Step program ⟨env, .expression (.assign place value rest), stack⟩
        ⟨env, .expression value, .assign place rest :: stack⟩
  | assignResult {env after : Environment} {stack : List Frame} {place : Place} {rest : Expr} {value : Value}
      (written : writePlace program place value env = some after) :
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
        ⟨[], .expression declaration.body, .restore env :: stack⟩
  | restore {env caller : Environment} {stack : List Frame} {value : Value} :
      Step program ⟨env, .result value, .restore caller :: stack⟩
        ⟨(Frame.restore caller).environment env, .result value, stack⟩
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
        ⟨inputs.map (fun input => (input.name, input.value)), .expression declaration.body, .restore env :: stack⟩
  | applyPatterns {env : Environment} {stack : List Frame} {inputs : List Ty} {arguments : List Expr} {arms : List (Pattern × Expr)} :
      Step program ⟨env, .expression (.applyPatterns inputs arguments arms), stack⟩
        ⟨env, .arguments arguments, .patterns arms :: stack⟩
  | selectedPattern {env : Environment} {bindings : List BindingInput} {stack : List Frame} {values : List Value}
      {arms : List (Pattern × Expr)} {body : Expr}
      (selected : selectArm (argumentValue values) arms = some (bindings, body)) :
      Step program ⟨env, .results values, .patterns arms :: stack⟩
        ⟨bindings.map (fun input => (input.name, input.value)) ++ env, .expression body, .scope bindings.length :: stack⟩
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

/-- The destination-write step preserves every differently rooted place in the
post-RHS environment. It makes no claim about earlier RHS effects. -/
theorem Step.assignment_frame {before : Environment} {after : Configuration} {stack : List Frame}
    {place other : Place} {rest : Expr} {value : Value}
    (step : Step program ⟨before, .result value, .assign place rest :: stack⟩ after)
    (different : other.root ≠ place.root) :
    readPlace program other after.environment = readPlace program other before := by
  cases step with
  | assignResult written => exact writePlace.read_other written different


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

end Grounded
