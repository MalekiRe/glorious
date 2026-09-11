import Glorious.Semantics.VM
import Glorious.Proof.Operational

/-! The receiving machine is specified by its instructions, not by running the
lowerer backwards. Registers own residents and must be vacant before a write.
The source type interpretation is ghost data; every interpreted type must be
related to the actual artifact table. -/
namespace Glorious.Semantics.Spec.Target

inductive RepresentsType (program : Program) (artifact : VM.Artifact) : Term → Nat → Prop where
  | unit {index} (entry : artifact.types[index]? = some (.builtin "Unit")) : RepresentsType program artifact .unit index
  | bottom {index} (entry : artifact.types[index]? = some (.builtin "Never")) : RepresentsType program artifact .bottom index
  | integer {index signed width} (entry : artifact.types[index]? = some (.builtin (VM.scalarName signed width))) :
      RepresentsType program artifact (.scalar (.integer signed width)) index
  | character {index} (entry : artifact.types[index]? = some (.builtin "Char")) :
      RepresentsType program artifact (.scalar .character) index
  | floating {index width} (entry : artifact.types[index]? = some (.builtin (if width = .w32 then "F32" else "F64"))) :
      RepresentsType program artifact (.scalar (.floating width)) index
  | reference {index child mode region type}
      (entry : artifact.types[index]? = some (.reference (mode == .unique) child))
      (referent : RepresentsType program artifact type child) :
      RepresentsType program artifact (.reference mode region type) index
  | tuple {index types fields copy}
      (entry : artifact.types[index]? = some (.tuple fields copy))
      (children : Glorious.Proof.Forall₂ (RepresentsType program artifact) types fields)
      (copyCorrect : copy = true ↔ PrincipalOf program (.tuple types) .duplicable) :
      RepresentsType program artifact (.tuple types) index
  | array {index child element length}
      (entry : artifact.types[index]? = some (.array child))
      (elementType : RepresentsType program artifact element child) :
      RepresentsType program artifact (.array element length) index
  | aliasType {left right index} (same : Equal program left right)
      (underlying : RepresentsType program artifact right index) : RepresentsType program artifact left index

structure Interpretation (program : Program) (artifact : VM.Artifact) where
  types : List Term
  declarations : List DeclId
  typeCount : types.length = artifact.types.length
  functionCount : declarations.length = artifact.functions.length
  typeMeaning : ∀ index type, types[index]? = some type → RepresentsType program artifact type index

structure CallFrame where
  identity : Id
  function : Nat
  cursor : Nat
  destination : Option Nat
  registers : List Id
  deriving Repr

structure LabelFrame where
  owner : Id
  slot : Nat
  result : Nat
  target : Nat
  brand : Term
  deriving Repr

structure HandlerFrame where
  identity : Id
  definition : Nat
  clauses : List Value
  frame : CallFrame
  outer : List CallFrame
  destination : Nat
  deriving Repr

structure Suspension where
  identity : Id
  handler : HandlerFrame
  frames : List CallFrame
  labels : List LabelFrame
  world : World
  required : Nat
  remaining : Nat
  destination : Option Nat
  consumed : Bool
  deriving Repr

structure State where
  world : World
  current : CallFrame
  callers : List CallFrame := []
  labels : List LabelFrame := []
  handlers : List HandlerFrame := []
  suspensions : List Suspension := []
  nextFrame : Id := 1
  nextControl : Id := 0
  result : Option Result := none
  deriving Repr

def Register (state : State) (register : Nat) (place : Place) : Prop :=
  state.current.registers[register]? = some place.root ∧ place.projections = []

def Next (state : State) : State := { state with current.cursor := state.current.cursor + 1 }

def Fetch (artifact : VM.Artifact) (state : State) (instruction : VM.Instruction) : Prop :=
  ∃ function, artifact.functions[state.current.function]? = some function ∧
    state.current.cursor < function.length ∧
    artifact.code[function.start + state.current.cursor]? = some instruction ∧ state.result = none

def JumpTarget (artifact : VM.Artifact) (state : State) (cursor : Nat) : Prop :=
  ∃ function, artifact.functions[state.current.function]? = some function ∧
    cursor < function.length

def RegisterType (program : Program) (artifact : VM.Artifact) (state : State)
    (register : Nat) (type : Term) : Prop :=
  ∃ function index, artifact.functions[state.current.function]? = some function ∧
    function.registers[register]? = some index ∧ RepresentsType program artifact type index

inductive ReadsRegisters (program : Program) : State → List Nat → List Value → World → Prop where
  | nil {state} : ReadsRegisters program state [] [] state.world
  | cons {state index indices place value values middle after}
      (register : Register state index place)
      (move : Takes program state.world place value middle)
      (rest : ReadsRegisters program { state with world := middle } indices values after) :
      ReadsRegisters program state (index :: indices) (value :: values) after

inductive DeclaresRegisters (program : Program) (artifact : VM.Artifact) :
    World → List Nat → List Id → World → Prop where
  | nil {world} : DeclaresRegisters program artifact world [] [] world
  | cons {before middle after index indices identity identities type}
      (meaning : RepresentsType program artifact type index)
      (declaration : Declares before ⟨identity, type, true, {}⟩ middle)
      (rest : DeclaresRegisters program artifact middle indices identities after) :
      DeclaresRegisters program artifact before (index :: indices) (identity :: identities) after

inductive BindsRegisters (program : Program) : World → List Id → List Value → World → Prop where
  | nil {world} : BindsRegisters program world [] [] world
  | cons {before middle after identity identities value values}
      (head : Initializes program before ⟨identity, []⟩ value middle)
      (rest : BindsRegisters program middle identities values after) :
      BindsRegisters program before (identity :: identities) (value :: values) after

structure Enters (program : Program) (artifact : VM.Artifact) (index : Nat)
    (inputs : List Value) (before : State) (after : State) where
  function : VM.Function
  selected : artifact.functions[index]? = some function
  inputCount : inputs.length = function.signature.params.length
  types : Glorious.Proof.Forall₂ (fun value index => RepresentsType program artifact value.type index) inputs function.signature.params
  registerTypes : function.signature.params.IsPrefix (function.registers.drop 1)
  declared : ∃ world, DeclaresRegisters program artifact
    { before.world with frame := before.nextFrame, scope := before.nextFrame }
    function.registers after.current.registers world ∧
    BindsRegisters program world ((after.current.registers.drop 1).take inputs.length) inputs after.world
  current : after.current.identity = before.nextFrame ∧ after.current.function = index ∧ after.current.cursor = 0
  fresh : after.nextFrame = before.nextFrame + 1
  control : after.labels = before.labels ∧ after.handlers = before.handlers ∧ after.suspensions = before.suspensions

inductive ConstantValue (program : Program) : VM.Constant → Term → ValueHead → Prop where
  | unit : ConstantValue program .unit .unit .unit
  | scalar {value} (valid : ValidScalar program.target value) :
      ConstantValue program (.scalar value) (scalarValueType value) (.scalar value)

def ExitFrame (before after : State) (payload : List Value) (boundary : CleanupBoundary) : Prop :=
  ExitDisposition before.world after.world before.current.registers payload boundary ∧
  (∀ label ∈ after.labels, label.owner ≠ before.current.identity) ∧
  (∀ handler ∈ after.handlers, handler.frame.identity ≠ before.current.identity)

/-- Raw instruction transitions. Primitive, host, handler and cleanup rules are
separate obligations rather than an appeal to the receiving Rust verifier. -/
inductive Step (program : Program) (artifact : VM.Artifact) : State → Option Observation → State → Prop where
  | nop {state} (instruction : Fetch artifact state .nop) : Step program artifact state none (Next state)
  | constant {state index destination constant type head value created world place}
      (instruction : Fetch artifact state (.constant destination index))
      (selected : artifact.constants[index]? = some constant)
      (meaning : ConstantValue program constant type head)
      (typed : RegisterType program artifact state destination type)
      (register : Register state destination place)
      (createdValue : FreshValue program state.world type head [] value created)
      (write : Initializes program created place value world) :
      Step program artifact state none (Next { state with world })
  | move {state destination source dst src value middle world}
      (instruction : Fetch artifact state (.move destination source))
      (sourceRegister : Register state source src) (to : Register state destination dst)
      (read : Takes program state.world src value middle)
      (write : Initializes program middle dst value world) :
      Step program artifact state none (Next { state with world })
  | copy {state destination source dst src value middle world}
      (instruction : Fetch artifact state (.copy destination source))
      (sourceRegister : Register state source src) (to : Register state destination dst)
      (read : Reads program state.world src false value middle)
      (permission : value.capability = .duplicable)
      (write : Initializes program middle dst value world) :
      Step program artifact state none (Next { state with world })
  | borrow {state destination source unique reborrow dst src value middle world region}
      (instruction : Fetch artifact state (.borrow unique reborrow destination source))
      (sourceRegister : Register state source src) (to : Register state destination dst)
      (read : Borrows program state.world
        (if reborrow then { src with projections := [.dereference] } else src)
        (if unique then .unique else .shared) region value middle)
      (write : Initializes program middle dst value world) :
      Step program artifact state none (Next { state with world })
  | deref {state destination source mode dst src value middle world}
      (instruction : Fetch artifact state (.deref mode destination source))
      (sourceRegister : Register state source src) (to : Register state destination dst)
      (modeValid : mode = 0 ∨ mode = 1)
      (read : Reads program state.world { src with projections := [.dereference] } (mode == 1) value middle)
      (write : Initializes program middle dst value world) :
      Step program artifact state none (Next { state with world })
  | store {state destination source dst src value middle world}
      (instruction : Fetch artifact state (.store destination source))
      (sourceRegister : Register state source src) (to : Register state destination dst)
      (read : Takes program state.world src value middle)
      (write : Initializes program middle { dst with projections := [.dereference] } value world) :
      Step program artifact state none (Next { state with world })
  | project {state mode destination source field dst src value middle world}
      (instruction : Fetch artifact state (.project mode destination source field))
      (sourceRegister : Register state source src) (to : Register state destination dst)
      (modeValid : mode = 0 ∨ mode = 1)
      (read : Reads program state.world { src with projections := [.field field] } (mode == 1) value middle)
      (write : Initializes program middle dst value world) :
      Step program artifact state none (Next { state with world })
  | drop {state register place world}
      (instruction : Fetch artifact state (.drop register))
      (location : Register state register place)
      (dispose : Disposes program state.world place world) :
      Step program artifact state none (Next { state with world })
  | jump {state target}
      (instruction : Fetch artifact state (.jump target)) (bounded : JumpTarget artifact state target) :
      Step program artifact state none { state with current.cursor := target }
  | switch {state discriminant branches otherwise place value width selected}
      (instruction : Fetch artifact state (.switch discriminant branches otherwise))
      (register : Register state discriminant place)
      (stored : Stored state.world ⟨place.root, []⟩ value)
      (integer : value.head = .scalar (.integer false width (Int.ofNat selected)))
      (targets : ∀ pair ∈ branches, JumpTarget artifact state pair.2)
      (otherwiseValid : JumpTarget artifact state otherwise) :
      Step program artifact state none { state with current.cursor :=
        ((branches.find? (fun pair => pair.1 == selected)).map (·.2)).getD otherwise }
  | call {state destination function registers values moved entered}
      (instruction : Fetch artifact state (.call destination function registers))
      (inputs : ReadsRegisters program state registers values moved)
      (entry : Enters program artifact function values { state with world := moved } entered) :
      Step program artifact state none { entered with callers :=
        { state.current with cursor := state.current.cursor + 1, destination } :: state.callers }
  | tailCall {state function registers values moved disposed entered}
      (instruction : Fetch artifact state (.tailCall function registers))
      (inputs : ReadsRegisters program state registers values moved)
      (cleanup : ExitFrame { state with world := moved } disposed values .properTail)
      (entry : Enters program artifact function values disposed entered)
      (noGrowth : entered.callers.length ≤ state.callers.length) :
      Step program artifact state none { entered with callers := state.callers }
  | returnValue {state register place value moved disposed caller rest written}
      (instruction : Fetch artifact state (.ret (some register)))
      (sourceRegister : Register state register place)
      (read : Takes program state.world place value moved)
      (cleanup : ExitFrame { state with world := moved } disposed [value] .normalReturn)
      (stack : state.callers = caller :: rest)
      (write : ∃ destination target, caller.destination = some destination ∧
        caller.registers[destination]? = some target ∧
        Initializes program disposed.world ⟨target, []⟩ value written) :
      Step program artifact state none { disposed with world := written, current := caller, callers := rest }
  | returned {state register place value moved disposed}
      (instruction : Fetch artifact state (.ret (some register)))
      (sourceRegister : Register state register place) (read : Takes program state.world place value moved)
      (cleanup : ExitFrame { state with world := moved } disposed [value] .normalReturn)
      (entry : state.callers = []) :
      Step program artifact state none { disposed with result := some (.returned value) }
  | abort {state message} (instruction : Fetch artifact state (.abort message)) :
      Step program artifact state none { state with result := some (.fatal .abort) }
  | unreachable {state} (instruction : Fetch artifact state .unreachable) :
      Step program artifact state none { state with result := some (.fatal .runtimeFault) }

def Initial (program : Program) (artifact : VM.Artifact) (state : State) : Prop :=
  ∃ entry function world, artifact.entry = some entry ∧ artifact.functions[entry]? = some function ∧
    function.signature.params = [] ∧ function.receiver = none ∧
    DeclaresRegisters program artifact { frame := 1, scope := 1 } function.registers state.current.registers world ∧
    state.world = world ∧ state.current.function = entry ∧ state.current.cursor = 0 ∧
    state.current.identity = 1 ∧ state.current.destination = none ∧ state.nextFrame = 2 ∧
    state.callers = [] ∧ state.labels = [] ∧ state.handlers = [] ∧ state.suspensions = [] ∧ state.result = none

def System (program : Program) (artifact : VM.Artifact) : Glorious.Proof.TransitionSystem Observation Result where
  State := State
  initial := Initial program artifact
  step := Step program artifact
  final state result := state.result = some result
  fault state := ¬ WorldWellFormed state.world

structure WellFormed (program : Program) (artifact : VM.Artifact) : Prop where
  interpretation : Nonempty (Interpretation program artifact)
  functions : ∀ function ∈ artifact.functions,
    0 < function.length ∧ function.start + function.length ≤ artifact.code.length ∧
    function.signature.params.IsPrefix (function.registers.drop 1) ∧
    (∀ type ∈ function.registers, type < artifact.types.length)
  extents : ∀ a b : Nat, artifact.functions[a]? ≠ none → artifact.functions[b]? ≠ none → a ≠ b →
    ∀ first second : VM.Function, artifact.functions[a]? = some first → artifact.functions[b]? = some second →
      first.start + first.length ≤ second.start ∨ second.start + second.length ≤ first.start
  exports : ∀ exportEntry ∈ artifact.exports,
    ∃ function, artifact.functions[exportEntry.2.1]? = some function ∧ function.signature = exportEntry.2.2
  hooks : ∀ hook ∈ artifact.dropGlue, hook.1 < artifact.types.length ∧ hook.2 < artifact.functions.length
  references : ∀ contract ∈ artifact.referenceReturns,
    ∃ definition, artifact.functions[contract.1]? = some definition ∧
      ∀ route ∈ contract.2, route.2.1 < definition.signature.params.length

/-- Non-erased source owners are related by an injective renaming. This is a
memory injection, not permission to merge two equal-looking references. -/
structure Injection where
  owners : Id → Id
  loans : Id → Id
  slots : Id → Id
  ownerInjective : Function.Injective owners
  loanInjective : Function.Injective loans
  slotInjective : Function.Injective slots

mutual
inductive ValueRelated (injection : Injection) : Value → Value → Prop where
  | owned {left right}
      (owner : right.identity = injection.owners left.identity)
      (type : right.type = left.type)
      (capability : right.capability = left.capability)
      (hook : right.dropHook = left.dropHook)
      (shell : right.shellConsumed = left.shellConsumed)
      (head : (∃ identity, left.head = .reference identity ∧ right.head = .reference (injection.loans identity)) ∨
        (left.head = right.head ∧ ∀ identity, left.head ≠ .reference identity))
      (fields : FieldsRelated injection left.fields right.fields) :
      ValueRelated injection left right

inductive FieldsRelated (injection : Injection) : List (Option Value) → List (Option Value) → Prop where
  | nil : FieldsRelated injection [] []
  | vacant {left right} (rest : FieldsRelated injection left right) :
      FieldsRelated injection (none :: left) (none :: right)
  | value {a b left right} (head : ValueRelated injection a b) (rest : FieldsRelated injection left right) :
      FieldsRelated injection (some a :: left) (some b :: right)
end

structure StateRelated (injection : Injection) (source : Configuration) (target : State) : Prop where
  resident : ∀ address value, Stored source.machine.world address value →
    ∃ represented, Stored target.world ⟨injection.slots address.slot, address.fields⟩ represented ∧
      ValueRelated injection value represented
  loans : ∀ loan ∈ source.machine.world.loans, ∃ represented ∈ target.world.loans,
    represented.identity = injection.loans loan.identity ∧ represented.live = loan.live ∧
    represented.hole = loan.hole ∧ represented.mode = loan.mode ∧
    represented.origin = ⟨injection.slots loan.origin.slot, loan.origin.fields⟩
  noFabricatedSourceOwner : ∀ address value, Stored target.world address value →
    (∃ sourceValue, Resident source.machine.world sourceValue ∧ ValueRelated injection sourceValue value) ∨
    (value.capability = .duplicable ∧ value.dropHook = none ∧ value.fields = [])

structure Correct (source : CoreProgram) (entry : DeclId) (artifact : VM.Artifact) : Prop where
  receiving : WellFormed source.source artifact
  nonvacuous : ∃ initial, Initial source.source artifact initial
  behavior : Glorious.Proof.Preserves (CoreSystem source entry) (System source.source artifact)
  resources : ∀ target, (System source.source artifact).Reachable target →
    ∃ sourceState injection, (CoreSystem source entry).Reachable sourceState ∧ StateRelated injection sourceState target
  tailSpace : ∃ overhead, ∀ target, (System source.source artifact).Reachable target →
    ∃ sourceState, (CoreSystem source entry).Reachable sourceState ∧
      target.callers.length + target.handlers.length + target.labels.length ≤
        sourceState.machine.frames.length + overhead

end Glorious.Semantics.Spec.Target
