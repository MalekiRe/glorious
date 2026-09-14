import GloriousLanguage.ForeignAccess

/-! External implementations remain semantic parameters. Contract-permitted
host mutations use authoritative storage producers, even in unsafe calls. -/
namespace Glorious.Language.Foreign

open Kernel Execution Memory

structure Signature where
  parameters : List (Term × Layout)
  result : Option (Term × Layout)
  convention : Identity
  variadic : Bool := false
  deriving Repr, Inhabited

def CSignature (program : Language.Program) (signature : Language.Signature) (foreign : Signature) : Prop :=
  program.input.target.supportsC = true ∧ signature.generics = [] ∧ foreign.variadic = false ∧
  signature.effects = .row [] [] ∧ foreign.parameters.map Prod.fst = signature.parameters ∧
  (∀ parameter ∈ foreign.parameters, CCompatible program ⟨[],[],0,default,false,{}⟩ parameter.1 parameter.2) ∧
  ((signature.result = .unit ∧ foreign.result = none) ∨
    ∃ layout, foreign.result = some (signature.result,layout) ∧ CCompatible program ⟨[],[],0,default,false,{}⟩ signature.result layout)

structure Import where
  declaration : DeclId
  symbol : String
  library : Identity
  signature : Signature
  capability : Option String
  domain : Option Identity
  reviewedSafe : Bool

/-- The registered owner is the actual callable and all its capture fields. -/
structure Registration where
  identity : Identity
  owner : Address
  authority : Authority
  access : Access
  function : DeclId
  arguments : List Term
  runtime : Identity
  entryAddress : Nat
  active : Bool
  retained : Bool
  extent : Identity

/-- The registration carries the exact callable authority that callbacks
will consume, including the shared view of a shared invocation. -/
def Registration.place (registration : Registration) : ResolvedPlace :=
  ⟨registration.owner,registration.authority.lend registration.access⟩

def Registration.Valid (program : Kernel.Program) (world : World) (runtimes : List Identity)
    (registration : Registration) : Prop :=
  registration.active = true →
    (∃ value, world.Stores registration.owner value ∧ value.Initialized ∧
      value.head = .callable registration.function registration.arguments) ∧
    (∃ function, Instance program registration.function registration.arguments function) ∧
    registration.runtime ∈ runtimes ∧
    registration.entryAddress < 2^program.declarations.input.target.pointerBits ∧
    (registration.retained = false → registration.extent ∈ world.liveRegions) ∧
    (registration.retained = true → ∃ root domain, world.root registration.owner = some root ∧
      (root.home = .external domain ∨ root.home = .allocation domain))

/-- The selected instantiated signature and original operands are immutable
throughout the protocol, including callback suspension and return. -/
def CallTyped (program : Kernel.Program) (world : World) (call : ForeignCall) : Prop :=
  (∃ substitution, Instantiates call.binding.signature.generics call.arguments substitution ∧
    ConstraintsHold program.declarations call.context.static substitution call.binding.signature.constraints ∧
    call.signature = call.binding.signature.instantiate substitution) ∧
  ListRel (fun type address => ∃ value, world.Stores address value ∧ value.Initialized ∧ value.type = type)
    call.signature.parameters call.operands ∧
  DestinationType world call.destination call.signature.result ∧
  (call.signature.unsafeAllowed = true → call.context.unsafeAllowed = true)

inductive HostAction where
  | result (value : Address)
  | callback (registration : Identity) (arguments : List ResolvedPlace)
  | continue
  | fault
  deriving Repr, Inhabited

structure Contract where
  declaration : DeclId
  precondition : World → ForeignSession → Prop
  session : World → ForeignSession → Prop
  transition : World → ForeignSession → World → HostAction → Prop
  normalPostcondition : World → ForeignSession → World → Address → Prop
  callbackPrecondition : World → ForeignSession → Identity → Prop
  callbackPostcondition : World → ForeignSession → List Nat → Identity → Address → Prop
  /-- Explicit imported storage grants are restricted to that binding's
  external allocation domain and root authority. Actual loan authority comes
  from handoff, registered authority or stored references, never a guessed ID. -/
  external : World → ForeignCall → ResolvedPlace → Prop
  writable : World → ForeignSession → Address → Prop
  retainable : World → ForeignSession → Address → Prop

/-- The host supplies this exact ordered action data to `Model.step`.
The mutation proof is indexed by it, and its output projection is the only
source of freshly published access. Equal endpoint worlds do not identify
transactions or permit substituting a less destructive history. -/
inductive MutationAction where
  | allocate (home : Home) (region : Identity) (type : Term) (layout : Layout)
      (mutable : Bool) (place : ResolvedPlace)
  | scalar (destination : Address) (value : ScalarValue)
  | unit (destination : Address)
  | pointer (destination : Address) (mode : Mutability) (type : Term) (pointer : RawPointer)
  | aggregate (destination : Address) (type : Term) (variant : Option DeclId) (sources : List ResolvedPlace)
  | acquire (source : ResolvedPlace) (force : Bool) (destination : Address)
  | borrow (source : ResolvedPlace) (mode : Mutability) (region : Identity) (destination : Address)
  | allocateBuffer (domain : Identity) (element : Term) (count base : Nat)
      (pointer : RawPointer) (allocation : ResolvedPlace)
  | reallocateBuffer (oldAllocation : ResolvedPlace) (old : RawPointer) (domain : Identity)
      (element : Term) (count base : Nat) (pointer : RawPointer) (allocation : ResolvedPlace)
  | releaseBuffer (allocation : ResolvedPlace) (pointer : RawPointer) (domain : Identity)
  | rawRead (source : ResolvedPlace) (pointer : RawPointer) (type : Term) (copy : Bool) (destination : Address)
  | rawWrite (source destination : ResolvedPlace) (pointer : RawPointer) (type : Term)
  | rawBorrow (source : ResolvedPlace) (pointer : RawPointer) (type : Term)
      (mode : Mutability) (region : Identity) (destination : Address)
  | bulkMove (sources destinations : List ResolvedPlace)
  | retire (address : Address)
  | endLoan (identity : Identity)
  deriving Repr, Inhabited

def MutationAction.produced (custody : ClaimCustody) : MutationAction → List ProducedResource
  | .allocate _ _ _ _ _ place => [⟨custody,place⟩]
  | .allocateBuffer _ _ _ _ _ allocation | .reallocateBuffer _ _ _ _ _ _ _ allocation => [⟨custody,allocation⟩]
  | _ => []

def TransactionOutputs (custody : ClaimCustody) (actions : List MutationAction) : List ProducedResource :=
  actions.flatMap (MutationAction.produced custody)

structure Model where
  imports : List Import
  contracts : List Contract
  /-- Registry and runtime liveness evolve, permitting unregister/shutdown. -/
  registrations : List Nat → List Registration
  runtimes : List Nat → List Identity
  start : DeclId → World → ForeignSession → List Nat → Prop
  step : DeclId → World → ForeignSession → List Nat → List MutationAction → World → HostAction → List Nat → Prop
  callbackReturned : DeclId → World → ForeignSession → List Nat → Identity → Address → List Nat → Prop

/-- Opaque host state may retain historical registrations, including retired
ones, but their loan authorities must already have actual table records.
This is admission for the initial registry; transitions derive it from the
same registration-origin relation used to authorize new callbacks. -/
def Model.AuthoritiesRecorded (model : Model) (world : World) (state : List Nat) : Prop :=
  ∀ registration ∈ model.registrations state, registration.authority.Recorded world.loans

/-- Authority seeds are actual protocol handoffs, retained callback owners,
explicit external grants and fresh roots of this host-only mutation chunk.
An arbitrary source frame or guessed allocation identity is not a seed. -/
def AccessSeed (program : Kernel.Program) (model : Model) (contract : Contract)
    (_initial current : World) (session : ForeignSession) (place : ResolvedPlace) : Prop :=
  (place ∈ session.known ∧ place.authority.Custodied current (.host session.call.destination.root)) ∨
  (∃ registration ∈ model.registrations session.state,
    registration.active = true ∧ registration.retained = true ∧
    place = registration.place ∧ place.authority.Custodied current (.registration registration.identity) ∧
    ∃ root domain, current.root registration.owner = some root ∧
      (root.home = .allocation domain ∨ root.home = .external domain)) ∨
  (contract.external current session.call place ∧ place.authority.carriers = [] ∧
    ∃ root domain, current.root place.address = some root ∧ root.home = .external domain ∧
      session.call.binding.domain = some domain ∧ domain ∈ program.declarations.input.manifest.allocationDomains)

def Accessible (program : Kernel.Program) (model : Model) (contract : Contract)
    (initial current : World) (session : ForeignSession) : ResolvedPlace → Prop :=
  Reachable program.declarations current (AccessSeed program model contract initial current session)

def Writable (program : Kernel.Program) (model : Model) (contract : Contract)
    (initial current : World) (session : ForeignSession) (address : Address) : Prop :=
  contract.writable current session address ∧
  ∃ authority, Accessible program model contract initial current session ⟨address,authority⟩ ∧
    Permitted current authority .unique address

def Retainable (program : Kernel.Program) (model : Model) (contract : Contract)
    (initial current : World) (session : ForeignSession) (address : Address) : Prop :=
  contract.retainable current session address ∧
  ∃ authority, Accessible program model contract initial current session ⟨address,authority⟩

def Policy (program : Kernel.Program) (model : Model) (contract : Contract)
    (initial : World) (session : ForeignSession) : AuthorityPolicy where
  place := fun current => Accessible program model contract initial current session
  write := fun current => Writable program model contract initial current session
  pointer := fun current => PointerAccess program.declarations current
    (Accessible program model contract initial current session)
  home := fun home region =>
    (home = .temporary session.call.context.activation session.call.context.scope ∧
      region = session.call.context.region) ∨
    ∃ domain, session.call.binding.domain = some domain ∧
      domain ∈ program.declarations.input.manifest.allocationDomains ∧
      (home = .allocation domain ∨ home = .external domain)
  domain := fun domain => session.call.binding.domain = some domain ∧
    domain ∈ program.declarations.input.manifest.allocationDomains
  custody := .host session.call.destination.root

/-- Host code consumes the actual handoff authority as well as the existing
resident producers. A producer's global validity is not permission to select
an otherwise inaccessible source, destination, pointer or allocation domain. -/
inductive Mutation (program : Kernel.Program) (policy : AuthorityPolicy) : World → MutationAction → World → Prop where
  | allocate {before after home region type layout mutable address} : policy.home home region →
      (∀ domain, home ≠ .allocation domain ∧ home ≠ .external domain) →
      Allocates program.declarations before home region type layout mutable address after → Mutation program policy before (.allocate home region type layout mutable ⟨address,.owner⟩) after
  | scalar {before after destination value} : policy.write before destination →
      StoresScalar program before destination value after → Mutation program policy before (.scalar destination value) after
  | unit {before after destination} : policy.write before destination →
      StoresUnit program before destination after → Mutation program policy before (.unit destination) after
  | pointer {before after destination mode type pointer} : policy.write before destination →
      policy.pointer before mode pointer →
      pointer.address < 2^program.declarations.input.target.pointerBits → pointer.Origin before →
      StoresPointer program before destination mode type pointer after → Mutation program policy before (.pointer destination mode type pointer) after
  | aggregate {before after destination type variant sources values head} : policy.write before destination →
      (∀ source ∈ sources, policy.place before source) →
      ListRel (fun source value => before.Stores source.address value) sources values →
      ConstructorHead program.declarations type variant (values.map Value.type) head →
      NewValue program before destination type head sources after → Mutation program policy before (.aggregate destination type variant sources) after
  | acquire {before after authority force source destination} : policy.place before ⟨source,authority⟩ →
      policy.write before destination →
      Acquires program before authority force source destination after → Mutation program policy before (.acquire ⟨source,authority⟩ force destination) after
  | borrow {before after authority mode region source destination} : policy.place before ⟨source,authority⟩ →
      policy.write before destination →
      Borrows program before authority mode region source destination after → Mutation program policy before (.borrow ⟨source,authority⟩ mode region destination) after
  | allocateBuffer {before after domain element count base pointer allocation} : policy.domain domain →
      AllocatesBuffer program.declarations policy.custody before domain element count base pointer allocation after →
      Mutation program policy before (.allocateBuffer domain element count base pointer allocation) after
  | reallocateBuffer {before after old oldAllocation domain element count base pointer allocation} : policy.domain domain →
      policy.pointer before .unique old →
      policy.place before oldAllocation →
      ReallocatesBuffer program policy.custody before oldAllocation old domain element count base pointer allocation after →
      Mutation program policy before (.reallocateBuffer oldAllocation old domain element count base pointer allocation) after
  | releaseBuffer {before after allocation pointer domain} : policy.domain domain → policy.pointer before .unique pointer →
      policy.place before allocation →
      ReleasesBuffer program.declarations before allocation pointer domain after → Mutation program policy before (.releaseBuffer allocation pointer domain) after
  | rawRead {before after source pointer type copy destination} :
      policy.pointer before (if copy then .shared else .unique) pointer → policy.write before destination →
      policy.place before source →
      RawRead program before source pointer type copy destination after → Mutation program policy before (.rawRead source pointer type copy destination) after
  | rawWrite {before after source destination pointer type} : policy.place before source →
      policy.pointer before .unique pointer →
      policy.place before destination →
      RawWrite program before source destination pointer type after → Mutation program policy before (.rawWrite source destination pointer type) after
  | rawBorrow {before after source pointer type mode region destination} : policy.pointer before mode pointer →
      policy.write before destination →
      policy.place before source →
      RawBorrow program before source pointer type mode region destination after → Mutation program policy before (.rawBorrow source pointer type mode region destination) after
  | bulkMove {before after sources destinations} :
      (∀ source ∈ sources, policy.place before source) →
      (∀ destination ∈ destinations, policy.place before destination ∧ policy.write before destination.address) →
      BulkMove program before sources destinations after → Mutation program policy before (.bulkMove sources destinations) after
  | retire {before after root resident} : before.roots.get root = some resident →
      policy.place before ⟨⟨root,resident.generation,[]⟩,.owner⟩ →
      Retires before root after → Mutation program policy before (.retire ⟨root,resident.generation,[]⟩) after
  | endLoan {before after loan} : EndsLoan program before loan after → Mutation program policy before (.endLoan loan) after

  | allocateExterior {before allocated home domain region type layout mutable address} :
      policy.home home region → (home = .allocation domain ∨ home = .external domain) →
      Allocates program.declarations before home region type layout mutable address allocated →
      Mutation program policy before
        (.allocate home region type layout mutable ⟨address,.loan before.nextLoan⟩)
        { allocated with
          loans := allocated.loans.set before.nextLoan
            ⟨before.nextLoan,none,address,.unique,region,true,.owning,[],false,some policy.custody⟩
          nextLoan := before.nextLoan+1 }

/-- Every prefix executes against exactly the output permissions published by
its earlier actions. The model supplies the list; lawfulness validates that
same list, not an existential mutation history selected from its endpoints. -/
inductive Mutations (program : Kernel.Program) (custody : ClaimCustody)
    (policy : List ProducedResource → AuthorityPolicy) :
    World → List ProducedResource → List MutationAction → World → Prop where
  | refl {world produced} : Mutations program custody policy world produced [] world
  | cons {before middle after produced action rest} :
      Mutation program (policy produced) before action middle →
      Mutations program custody policy middle (produced ++ action.produced custody) rest after →
      Mutations program custody policy before produced (action :: rest) after

def Selected (program : Kernel.Program) (model : Model) (call : ForeignCall) (imported : Import) (contract : Contract) : Prop :=
  call.binding ∈ program.declarations.input.manifest.bindings ∧ call.binding.primitive = none ∧
  imported ∈ model.imports ∧ imported.declaration = call.binding.declaration ∧ call.binding.symbol = some imported.symbol ∧
  imported.capability = call.binding.capability ∧ imported.domain = call.binding.domain ∧
  contract ∈ model.contracts ∧ contract.declaration = call.binding.declaration ∧
  (call.binding.cABI = true → CSignature program.declarations call.signature imported.signature) ∧
  (call.signature.unsafeAllowed = false → call.binding.safeReviewed = true ∧ imported.reviewedSafe = true)

def FramePreserved (program : Kernel.Program) (model : Model) (contract : Contract)
    (before : World) (session : ForeignSession) (after : World) : Prop :=
  ∀ address value, before.Resident address value →
    (∀ ancestor, ancestor.Overlaps address → ¬ Writable program model contract before before session ancestor) →
    after.Stores address value

def RegistrationsValid (program : Kernel.Program) (model : Model) (world : World) (state : List Nat) : Prop :=
  (model.registrations state |>.map (·.identity)).Nodup ∧
  ∀ registration ∈ model.registrations state, registration.Valid program world (model.runtimes state)

/-- Unregistering preserves a record's origin without requiring its expired
callable to remain accessible. Every genuinely new record, even an initially
inactive one, comes from actual handoff authority. A later activation cannot
turn guessed inactive metadata into a valid callback authority. -/
inductive RegistrationOrigin (program : Kernel.Program) (contract : Contract) (model : Model)
    (initial current : World) (session : ForeignSession) (previous : List Nat) : Registration → Prop where
  | existing {registration} : registration ∈ model.registrations previous →
      RegistrationOrigin program contract model initial current session previous registration
  | unregister {registration} : registration ∈ model.registrations previous →
      RegistrationOrigin program contract model initial current session previous { registration with active := false }
  | register {registration} : Accessible program model contract initial current session registration.place →
      (registration.retained = true → contract.retainable current session registration.owner) →
      RegistrationOrigin program contract model initial current session previous registration

/-- Registering a callback requires the exact authority later exposed by the
registry. Address reachability alone cannot upgrade a shared view to ownership.
Keeping that authority beyond synchronous extent additionally requires the
contract's retention permission. This is the one actual registry transition
contract, including unregister-only changes and inactive historical records. -/
structure HostStateEvolution (program : Kernel.Program) (contract : Contract) (model : Model)
    (initial current : World) (session : ForeignSession)
    (before after : List Nat) : Prop where
  registrations : ∀ registration ∈ model.registrations after,
    RegistrationOrigin program contract model initial current session before registration
  /-- Shutdown may not revoke a runtime held by this real callback handoff.
  The inventory remains the model's ordinary runtime state. -/
  runtimes : ∀ runtime ∈ session.heldRuntimes,
    runtime ∈ model.runtimes before → runtime ∈ model.runtimes after

/-- Laws constrain the model only on its declared contract domain. World
typing is derived from mutations; no post-world typing assumption occurs. -/
structure Model.Lawful (program : Kernel.Program) (model : Model) : Prop where
  imports : (model.imports.map (·.declaration)).Nodup
  contracts : (model.contracts.map (·.declaration)).Nodup
  start : ∀ initial imported contract world state,
    Selected program model initial.call imported contract → world.WellFormed → CallTyped program world initial.call →
    contract.precondition world initial → model.start initial.call.binding.declaration world initial state →
    contract.session world { initial with state } ∧ RegistrationsValid program model world state ∧
    HostStateEvolution program contract model world world initial initial.state state
  step : ∀ session imported contract before observation actions after action next,
    Selected program model session.call imported contract → before.WellFormed → contract.session before session →
    model.step session.call.binding.declaration before session observation actions after action next →
    Mutations program (.host session.call.destination.root)
      (fun produced => Policy program model contract before (session.advance produced session.state))
      before [] actions after ∧
    contract.transition before session after action ∧
    FramePreserved program model contract before session after ∧ RegistrationsValid program model after next ∧
    (action = .continue → contract.session after (session.advance (TransactionOutputs (.host session.call.destination.root) actions) next)) ∧
    (∀ result, action = .result result → contract.normalPostcondition before session after result ∧
      Accessible program model contract before after
        (session.advance (TransactionOutputs (.host session.call.destination.root) actions) session.state) ⟨result,.owner⟩ ∧
      ∃ value, after.Stores result value ∧ value.Initialized ∧ value.type = session.call.signature.result) ∧
    (∀ registration arguments, action = .callback registration arguments →
      contract.callbackPrecondition after (session.advance (TransactionOutputs (.host session.call.destination.root) actions) next) registration ∧
      ∀ argument ∈ arguments, Accessible program model contract before after
        (session.advance (TransactionOutputs (.host session.call.destination.root) actions) session.state) argument) ∧
    (∀ address value id loan, after.Resident address value → value.head = .reference id →
      after.loans.get id = some loan → ¬ before.References id →
      Retainable program model contract before after
        (session.advance (TransactionOutputs (.host session.call.destination.root) actions) session.state) loan.referent ∨ loan.region ∈ before.liveRegions) ∧
    HostStateEvolution program contract model before after
      (session.advance (TransactionOutputs (.host session.call.destination.root) actions) session.state) session.state next
  callbackReturned : ∀ session imported contract world current registration result next,
    Selected program model session.call imported contract → world.WellFormed →
    contract.callbackPostcondition world session current registration result →
    model.callbackReturned session.call.binding.declaration world session current registration result next →
    contract.session world (session.returned result next) ∧ RegistrationsValid program model world next ∧
    HostStateEvolution program contract model world world
      (session.returned result current) current next

/-- Actual dispatch owns a current ABI entry and callable permission. A lent
registration remains exact and active; an owning callback atomically consumes
its registry ownership before the source receiver is consumed. Runtime liveness
is checked in the host's new state, not its obsolete pre-action snapshot. -/
structure CallbackAdmission (program : Kernel.Program) (model : Model) (contract : Contract)
    (initial current : World) (session : ForeignSession) (state : List Nat) (id : Identity)
    (registration : Registration) (function : Function) : Prop where
  registered : registration ∈ model.registrations session.state
  identity : registration.identity = id
  active : registration.active = true
  accessible : Accessible program model contract initial current session registration.place
  receiver : CallableReceiver program current registration.owner registration.authority registration.access
    registration.function registration.arguments
  selected : Instance program registration.function registration.arguments function
  effects : function.signature.effects = .row [] []
  abi : session.call.binding.cABI = true → ∃ abi, CSignature program.declarations function.signature abi
  runtime : registration.runtime ∈ model.runtimes state
  entry : registration.entryAddress < 2^program.declarations.input.target.pointerBits
  lent : registration.access ≠ .owned → registration ∈ model.registrations state
  owned : registration.access = .owned → ∀ current ∈ model.registrations state, current.active = true →
    ¬ registration.owner.Overlaps current.owner

/-- Host payload adapter to ordinary invocation inputs. Captures still use
CaptureInputs from the actual registered receiver, under retained authority. -/
def CallbackInputs (world : World) (formals : List Local) (arguments : List ResolvedPlace)
    (inputs : List InvocationInput) : Prop :=
  inputs = (formals.zip arguments).zipIdx.map (fun ((formal,argument),index) =>
    ⟨.argument index,formal,argument.address,argument.authority,.owned⟩) ∧
  ListRel (fun formal argument => ∃ value, world.Stores argument.address value ∧ value.Initialized ∧
    value.type = formal.type ∧ Permitted world argument.authority .owned argument.address) formals arguments

/-- Callback completion goes through ordinary reference destruction, including
releaseChild's recursive retry of an unreferenced parent. The host protocol is
resumed only after that cleanup, against the resulting world and ambient state. -/
def CallbackReturnTask (session : ForeignSession) (registration : CallbackEntry) (result : Address)
    (lease : Option ReceiverLease) (next : Code) : Task :=
  let complete := Task.foreignCallbackReturned session registration result next
  match lease with
  | none => complete
  | some lease => .destroy session.call.context lease.handle .owner (.retire lease.handle.root complete)

inductive Step (program : Kernel.Program) (model : Model) : State → Option Event → State → Prop where
  | enter {before context destination binding arguments operands next imported contract state addresses prepared signature} :
      before.task = .primitive context destination binding arguments operands next →
      Selected program model ⟨context,destination,binding,arguments,signature,addresses⟩ imported contract →
      Protects program context before.world operands addresses prepared →
      CallTyped program prepared ⟨context,destination,binding,arguments,signature,addresses⟩ →
      contract.precondition prepared
        ⟨⟨context,destination,binding,arguments,signature,addresses⟩,before.hostState,AmbientExposed before.frames,AmbientRuntimes before.frames⟩ →
      model.start binding.declaration prepared
        ⟨⟨context,destination,binding,arguments,signature,addresses⟩,before.hostState,AmbientExposed before.frames,AmbientRuntimes before.frames⟩ state →
      Step program model before none
        { before with world := prepared, hostState := state, task := .foreign ⟨⟨context,destination,binding,arguments,signature,addresses⟩,state,AmbientExposed before.frames,AmbientRuntimes before.frames⟩ next }
  | host {before session next imported contract observation actions after nextState} :
      before.task = .foreign session next → before.hostState = session.state → Selected program model session.call imported contract →
      contract.session before.world session →
      model.step session.call.binding.declaration before.world session observation actions after .continue nextState →
      Step program model before (some (.host imported.symbol session.state observation))
        { before with world := after, hostState := nextState, task := .foreign (session.advance (TransactionOutputs (.host session.call.destination.root) actions) nextState) next }
  | result {before session next imported contract observation actions after result nextState transferred} :
      before.task = .foreign session next → before.hostState = session.state → Selected program model session.call imported contract →
      contract.session before.world session →
      model.step session.call.binding.declaration before.world session observation actions after (.result result) nextState →
      (∀ registration ∈ model.registrations nextState, registration.active = true →
        ¬ result.Overlaps registration.owner ∧ ¬ session.call.destination.Overlaps registration.owner) →
      Transfers program after .owner result session.call.destination transferred →
      Step program model before (some (.host imported.symbol session.state observation))
        { before with world := transferred, hostState := nextState, task := .retire result.root (.run session.call.context next) }
  | callback {before session next imported contract observation actions after id arguments nextState registration function inputs} :
      before.task = .foreign session next → before.hostState = session.state → Selected program model session.call imported contract →
      contract.session before.world session →
      model.step session.call.binding.declaration before.world session observation actions after (.callback id arguments) nextState →
      CallbackAdmission program model contract before.world after
        (session.advance (TransactionOutputs (.host session.call.destination.root) actions) session.state)
        nextState id registration function →
      CallbackInputs after function.parameters arguments inputs →
      Step program model before (some (.host imported.symbol session.state observation))
        { before with
          world := after
          hostState := nextState
          task := .enter session.call.context function (.resident ⟨registration.owner,registration.authority⟩ registration.access inputs) false,
          frames := .hostCallback (session.advance (TransactionOutputs (.host session.call.destination.root) actions) nextState)
            ⟨id,registration.runtime,registration.entryAddress⟩ function.signature.result none next :: before.frames }
  | callbackResult {before context result session registration resultType lease next rest value kept protectedWorld after} :
      before.task = .yield context result → before.frames = .hostCallback session registration resultType lease next :: rest →
      before.world.Stores result value → value.type = resultType →
      Protect program session.call.context before.world result .owner kept protectedWorld →
      Retires protectedWorld result.root after →
      Step program model before none
        { before with world := after, task := CallbackReturnTask session registration kept lease next }
  | callbackReturned {before session registration result next imported contract nextState resultType lease rest} :
      before.task = .foreignCallbackReturned session registration result next →
      before.frames = .hostCallback session registration resultType lease next :: rest →
      Selected program model session.call imported contract →
      contract.callbackPostcondition before.world session before.hostState registration.registration result →
      model.callbackReturned session.call.binding.declaration before.world session before.hostState registration.registration result nextState →
      Step program model before none
        { before with hostState := nextState, frames := rest, task := .foreign (session.returned result nextState) next }
  | fault {before session next imported contract observation actions after nextState} :
      before.task = .foreign session next → before.hostState = session.state → Selected program model session.call imported contract →
      contract.session before.world session →
      model.step session.call.binding.declaration before.world session observation actions after .fault nextState →
      Step program model before (some (.fatal .hostContract)) { before with world := after, hostState := nextState, task := .fatal .hostContract }

def NoForeignCapture (frames : List Frame) : Prop :=
  ∀ frame ∈ frames, frame.ForeignFree

/-- Callbacks enter through the ordinary resident recipe. The actual
registration admission supplies pre-entry readiness, not an already-entered
world or a separately consumed synthetic input list. -/
theorem Step.entry_ready {program : Kernel.Program} {model : Model} {before after : State}
    {event : Option Event} {caller : Execution.Context} {function : Function} {source : EntrySource} {tail : Bool}
    (stepped : Step program model before event after)
    (entry : after.task = .enter caller function source tail) : source.Ready program after.world function := by
  cases stepped with
  | enter => cases entry
  | host => cases entry
  | result => cases entry
  | callback _ _ _ _ _ admitted _ =>
      rcases Task.enter.inj entry with ⟨rfl,rfl,rfl,rfl⟩
      exact ⟨_,_,admitted.receiver,admitted.selected⟩
  | callbackResult =>
      simp only [CallbackReturnTask] at entry
      split at entry <;> cases entry
  | callbackReturned => cases entry
  | fault => cases entry

theorem callback_barrier_not_empty {session registration resultType lease next rest} :
    ¬ NoForeignCapture (.hostCallback session registration resultType lease next :: rest) := by
  intro safe
  exact safe (.hostCallback session registration resultType lease next) (by simp)

end Glorious.Language.Foreign
