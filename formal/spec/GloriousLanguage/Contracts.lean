import GloriousLanguage.Typing

/-! Checked interfaces are abstractions of execution, not trusted annotations.
The meaning below is intentionally semantic; it does not claim that an
arbitrary exact control contract has a decidable inference procedure. -/
namespace Glorious.Language.Contracts

open Kernel Execution

inductive Outcome where
  | normal (result : Address)
  | label (brand : Identity) (result : ResolvedPlace)
  | operation (id : DeclId) (arguments : List Term) (payload : List ResolvedPlace)
  | suspended (continuation : Identity)
  | canceled (continuation : Identity)
  | fault (reason : Fatal)
  | divergent
  | unknown
  deriving Repr, Inhabited

inductive Guard where
  | always
  | constructor (origin : Identity) (path : List Nat) (variant : DeclId)
  | pattern (origin pattern : Identity) (positive : Bool)
  | and (left right : Guard)
  | or (left right : Guard)
  deriving Repr, Inhabited

def Guard.Holds (world : World) : Guard → Prop
  | .always => True
  | .constructor origin path variant => ∃ address value selected,
      world.Resident address value ∧ value.owner = origin ∧ value.atPath path = some selected ∧ selected.head = .constructor variant
  | .pattern origin patternId positive => ∃ address value pack,
      world.Resident address value ∧ value.shellLive = true ∧ value.head = .bindings pack ∧
      ⟨origin,patternId,positive⟩ ∈ pack.facts
  | .and left right => left.Holds world ∧ right.Holds world
  | .or left right => left.Holds world ∨ right.Holds world

structure Observation where
  input : List InvocationInput
  before : World
  events : List Event
  after : World
  outcome : Outcome

def InputsTyped (program : Kernel.Program) (inputs : List InvocationInput) (world : World) : Prop :=
  Typing.WorldTyped program world ∧
  (inputs.map (fun input => input.formal.id)).Nodup ∧
  (∀ input ∈ inputs, ∃ value, world.Stores input.storage value ∧ value.Initialized ∧ value.type = input.formal.type ∧
    Permitted world input.authority input.access input.storage) ∧
  (∀ left ∈ inputs, ∀ right ∈ inputs, left ≠ right → left.storage.Overlaps right.storage →
    left.access = .shared ∧ right.access = .shared)

def FunctionInputs (function : Function) (inputs : List InvocationInput) : Prop :=
  inputs.map (·.formal) = function.captures ++ function.parameters ∧
  (∀ index input, inputs[index]? = some input →
    (index < function.captures.length ∧ input.origin = .capture index) ∨
      (function.captures.length ≤ index ∧ input.origin = .argument (index-function.captures.length)))

def InitialInvocation (program : Kernel.Program) (function : Function) (inputs : List InvocationInput) (state : State) : Prop :=
  InputsTyped program inputs state.world ∧ FunctionInputs function inputs ∧ state.ResumptionsAccounted ∧
  ∃ caller, state.task = .enter caller function (.supplied inputs) false ∧ state.frames = [] ∧
    caller.region ∈ state.world.liveRegions ∧ caller.activation < state.nextActivation ∧
    (∀ id root, state.world.roots.get id = some root → OwnedByActivation root state.nextActivation → root.live = false)

def AtOutcome (state : State) : Outcome → Prop
  | .normal result => state.task = .stopped result
  | .label brand result => ∃ context, state.task = .leave context brand result
  | .operation id arguments payload => ∃ context, state.task = .perform context id arguments payload
  | .suspended id => ∃ suspension, state.resumptions.get id = some suspension ∧ suspension.active = true
  | .canceled id => ∃ suspension, state.resumptions.get id = some suspension ∧ suspension.active = false ∧ suspension.quantity.lower = 0
  | .fault reason => state.task = .fatal reason
  | .divergent | .unknown => False

def Observes (program : Kernel.Program) (host : Foreign.Model) (function : Function) (observation : Observation) : Prop :=
  ∃ start finish,
    InitialInvocation program function observation.input start ∧ start.world = observation.before ∧
    Run program host start observation.events finish ∧ finish.world = observation.after ∧ AtOutcome finish observation.outcome

def Diverges (program : Kernel.Program) (host : Foreign.Model) (function : Function) (inputs : List InvocationInput)
    (states : Nat → State) (events : Nat → Option Event) : Prop :=
  InitialInvocation program function inputs (states 0) ∧ ∀ n, Step program host (states n) (events n) (states (n+1))

structure Interface where
  finite : Observation → Prop
  infinite : List InvocationInput → (Nat → State) → (Nat → Option Event) → Prop

def Derived (program : Kernel.Program) (function : Function) (interface : Interface) : Prop :=
  (∀ host observation, Foreign.Model.Lawful program host →
    Observes program host function observation → interface.finite observation) ∧
  (∀ host inputs states events, Foreign.Model.Lawful program host →
    Diverges program host function inputs states events → interface.infinite inputs states events)

def ExactInterface (program : Kernel.Program) (function : Function) : Interface :=
  ⟨fun observation => ∃ host, Foreign.Model.Lawful program host ∧ Observes program host function observation,
   fun inputs states events => ∃ host, Foreign.Model.Lawful program host ∧ Diverges program host function inputs states events⟩

def MayAwait (program : Kernel.Program) (function : Function) (state : State) : Prop :=
  ∃ context id arguments payload operation signature,
    state.task = .perform context id arguments payload ∧ OperationInstance program id arguments operation signature ∧
    RowSubset program.declarations context.static signature.effects function.signature.effects ∧
    (∀ source ∈ payload, state.world.Initialized source.address ∧
      Permitted state.world source.authority .owned source.address) ∧
    (∀ inner handler owns arm outer, ¬ Routes program state id arguments payload inner handler owns arm outer) ∧
    Suspensible state.world (state.world.roots.map Prod.fst)

def StateProgress (program : Kernel.Program) (host : Foreign.Model) (function : Function) (state : State) : Prop :=
  (∃ result, state.task = .stopped result) ∨ (∃ reason, state.task = .fatal reason) ∨ MayAwait program function state ∨
    ∃ event after, Step program host state event after

/-- The remaining path-sensitive obligations. Storage typing is not a second
admission premise: `SemanticPreservation` derives it for every execution from
well-formed declarations, the body inventory and the host's actual laws. -/
def ResourceAdmissionAt (program : Kernel.Program) (function : Function) (access : Access) : Prop :=
  ∀ host inputs start trace finish,
    Foreign.Model.Lawful program host → InitialInvocation program function inputs start →
    (∀ input ∈ inputs, (∃ index, input.origin = .capture index) → input.access = access) → Run program host start trace finish →
    StateProgress program host function finish ∧
    (∀ result value, finish.task = .stopped result → finish.world.Stores result value →
      Subtype program.declarations ⟨[],[],0,default,false⟩ value.type function.signature.result) ∧
    (∀ result, finish.task = .stopped result →
      ∀ id root, finish.world.roots.get id = some root → root.live = true →
        (∃ old, start.world.roots.get id = some old) ∨ result.root = id ∨
        (∃ domain, root.home = .allocation domain ∨ root.home = .external domain))

def ResourceAdmission (program : Kernel.Program) (function : Function) : Prop := ResourceAdmissionAt program function .owned

def OriginalInputSurvives (before after : World) (input : InvocationInput) : Prop :=
  ∀ value, before.Stores input.storage value →
    ∃ current, after.Stores input.storage current ∧ current.owner = value.owner ∧ current.type = value.type ∧ current.Initialized

def ReceiverAccess (receiver : Term) (type : Term) (access : Access) : Prop :=
  (receiver = type ∧ access = .owned) ∨
  (∃ region, receiver = .reference .shared region type ∧ access = .shared) ∨
  (∃ region, receiver = .reference .unique region type ∧ access = .unique)

def RelationHolds (program : Kernel.Program) (function : Function) (relation : InvocationRelation) : Prop :=
  relation.arguments = function.signature.parameters ∧ relation.result = function.signature.result ∧
  relation.effects = function.signature.effects ∧ relation.unsafeAllowed = function.signature.unsafeAllowed ∧
  ∃ arguments access,
    ReceiverAccess relation.receiver (.callable function.declaration arguments) access ∧
    (∀ host observation, Foreign.Model.Lawful program host → Observes program host function observation →
      (∀ input ∈ observation.input, (∃ index, input.origin = .capture index) → input.access = access) →
      (∀ result, observation.outcome = .normal result →
        access ≠ .owned → relation.after = relation.access ∧
          ∀ input ∈ observation.input, (∃ index, input.origin = .capture index) → OriginalInputSurvives observation.before observation.after input)) ∧
    ResourceAdmissionAt program function access

def CheckedInterfaces (program : Kernel.Program) : Prop :=
  ∀ declaration, program.declarations.function declaration.header.id = some declaration →
    ∀ arguments function substitution relation,
      Instance program declaration.header.id arguments function → Instantiates declaration.signature.generics arguments substitution →
      relation ∈ declaration.invocations →
      RelationHolds program function
        ⟨relation.receiver.substitute substitution,relation.access.substitute substitution,
          relation.arguments.map (Term.substitute substitution),relation.result.substitute substitution,
          relation.effects.substitute substitution,relation.after.substitute substitution,relation.unsafeAllowed⟩

def PlainBoundary (world : World) (values : List Address) : Prop :=
  ∀ id available, world.availability.get id = some available → available.active = true →
    ∀ address ∈ values, ∀ value path resident, world.Stores address value → ResidentAt value path resident → resident.head ≠ .available id

def ClosedResult (observation : Observation) : Prop :=
  ∀ result, observation.outcome = .normal result → PlainBoundary observation.after [result] ∧
    ∀ id available, observation.after.availability.get id = some available → available.active = true →
      ∃ original, observation.before.availability.get id = some original ∧ original = available

def DropTraceSafe (before : World) (inputs : List InvocationInput) (events : List Event) : Prop :=
    (∀ event ∈ events,
      (∀ brand, event ≠ .leave brand) ∧ (∀ id, event ≠ .suspend id) ∧
      (∀ id last, event ≠ .replay id last) ∧ (∀ operation arguments, event ≠ .perform operation arguments)) ∧
    (∀ input ∈ inputs, ∀ value id loan, before.Stores input.storage value → value.head = .reference id →
      before.loans.get id = some loan →
      ∀ source destination, Event.move source destination ∈ events → ¬ source.Overlaps loan.referent)

/-- Destructor restrictions are safety properties of every actual execution
prefix, including a hook that subsequently diverges and has no final outcome. -/
def DropContract (program : Kernel.Program) (self region : Term) (function : Function) : Prop :=
  DropFunction self region function ∧
  (∀ host inputs start events finish, Foreign.Model.Lawful program host →
    InitialInvocation program function inputs start → Run program host start events finish →
    DropTraceSafe start.world inputs events) ∧
  ResourceAdmission program function

theorem exact_interface_is_derived (program : Kernel.Program) (function : Function) :
    Derived program function (ExactInterface program function) := by
  constructor
  · intro host observation lawful observed
    exact ⟨host,lawful,observed⟩
  · intro host inputs states events lawful infinite
    exact ⟨host,lawful,infinite⟩

theorem unknown_is_not_normal {state : State} : ¬ AtOutcome state .unknown := by
  intro impossible
  exact impossible

end Glorious.Language.Contracts
