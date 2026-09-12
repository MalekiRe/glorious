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
  (∀ parameter ∈ foreign.parameters, CCompatible program ⟨[],[],0,default,false⟩ parameter.1 parameter.2) ∧
  ((signature.result = .unit ∧ foreign.result = none) ∨
    ∃ layout, foreign.result = some (signature.result,layout) ∧ CCompatible program ⟨[],[],0,default,false⟩ signature.result layout)

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
  external allocation domain. Source-frame authority comes only from handoff. -/
  external : World → ForeignCall → ResolvedPlace → Prop
  writable : World → ForeignSession → Address → Prop
  retainable : World → ForeignSession → Address → Prop

structure Model where
  imports : List Import
  contracts : List Contract
  /-- Registry and runtime liveness evolve, permitting unregister/shutdown. -/
  registrations : List Nat → List Registration
  runtimes : List Nat → List Identity
  start : DeclId → World → ForeignSession → List Nat → Prop
  step : DeclId → World → ForeignSession → List Nat → World → HostAction → List Nat → Prop
  callbackReturned : DeclId → World → ForeignSession → List Nat → Identity → Address → List Nat → Prop

/-- Authority seeds are actual protocol handoffs, retained callback owners,
explicit external grants and fresh roots of this host-only mutation chunk.
An arbitrary source frame or guessed allocation identity is not a seed. -/
def AccessSeed (program : Kernel.Program) (model : Model) (contract : Contract)
    (initial current : World) (session : ForeignSession) (place : ResolvedPlace) : Prop :=
  place ∈ session.known ∨
  (∃ registration ∈ model.registrations session.state,
    registration.active = true ∧ registration.retained = true ∧
    place = ⟨registration.owner,registration.authority.lend registration.access⟩ ∧
    ∃ root domain, current.root registration.owner = some root ∧
      (root.home = .allocation domain ∨ root.home = .external domain)) ∨
  (contract.external current session.call place ∧
    ∃ root domain, current.root place.address = some root ∧ root.home = .external domain ∧
      session.call.binding.domain = some domain ∧ domain ∈ program.declarations.input.manifest.allocationDomains) ∨
  (initial.nextRoot ≤ place.address.root ∧ place.address.fields = [] ∧ place.authority = .owner ∧
    ∃ root, current.root place.address = some root)

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

/-- Host code consumes the actual handoff authority as well as the existing
resident producers. A producer's global validity is not permission to select
an otherwise inaccessible source, destination, pointer or allocation domain. -/
inductive Mutation (program : Kernel.Program) (policy : AuthorityPolicy) : World → World → Prop where
  | allocate {before after home region type layout mutable address} : policy.home home region →
      Allocates program.declarations before home region type layout mutable address after → Mutation program policy before after
  | scalar {before after destination value} : policy.write before destination →
      StoresScalar program before destination value after → Mutation program policy before after
  | unit {before after destination} : policy.write before destination →
      StoresUnit program before destination after → Mutation program policy before after
  | pointer {before after destination mode type pointer} : policy.write before destination →
      policy.pointer before mode pointer →
      pointer.address < 2^program.declarations.input.target.pointerBits → pointer.Origin before →
      StoresPointer program before destination mode type pointer after → Mutation program policy before after
  | aggregate {before after destination type variant sources values head} : policy.write before destination →
      (∀ source ∈ sources, policy.place before source) →
      ListRel (fun source value => before.Stores source.address value) sources values →
      ConstructorHead program.declarations type variant (values.map Value.type) head →
      NewValue program.declarations before destination type head sources after → Mutation program policy before after
  | acquire {before after authority force source destination} : policy.place before ⟨source,authority⟩ →
      policy.write before destination →
      Acquires program.declarations before authority force source destination after → Mutation program policy before after
  | borrow {before after authority mode region source destination} : policy.place before ⟨source,authority⟩ →
      policy.write before destination →
      Borrows program.declarations before authority mode region source destination after → Mutation program policy before after
  | allocateBuffer {before after domain element count base pointer} : policy.domain domain →
      AllocatesBuffer program.declarations before domain element count base pointer after → Mutation program policy before after
  | reallocateBuffer {before after old domain element count base pointer} : policy.domain domain →
      policy.pointer before .unique old →
      ReallocatesBuffer program.declarations before old domain element count base pointer after → Mutation program policy before after
  | releaseBuffer {before after pointer domain} : policy.domain domain → policy.pointer before .unique pointer →
      ReleasesBuffer program.declarations before pointer domain after → Mutation program policy before after
  | rawRead {before after pointer type copy destination} :
      policy.pointer before (if copy then .shared else .unique) pointer → policy.write before destination →
      RawRead program.declarations before pointer type copy destination after → Mutation program policy before after
  | rawWrite {before after authority source pointer type} : policy.place before ⟨source,authority⟩ →
      policy.pointer before .unique pointer →
      RawWrite program.declarations before authority source pointer type after → Mutation program policy before after
  | rawBorrow {before after pointer type mode region destination} : policy.pointer before mode pointer →
      policy.write before destination →
      RawBorrow program.declarations before pointer type mode region destination after → Mutation program policy before after
  | bulkMove {before after sources destinations} :
      (∀ source ∈ sources, policy.place before ⟨source,.owner⟩) →
      (∀ destination ∈ destinations, policy.write before destination) →
      BulkMove program.declarations before sources destinations after → Mutation program policy before after
  | retire {before after root resident} : before.roots.get root = some resident →
      policy.place before ⟨⟨root,resident.generation,[]⟩,.owner⟩ →
      Retires before root after → Mutation program policy before after
  | endLoan {before after loan} : EndsLoan before loan after → Mutation program policy before after

inductive Mutations (program : Kernel.Program) (policy : AuthorityPolicy) : World → World → Prop where
  | refl {world} : Mutations program policy world world
  | cons {before middle after} : Mutation program policy before middle → Mutations program policy middle after →
      Mutations program policy before after

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

/-- Keeping a newly registered owner is a contract capability, independently
of linking the callback's machine entry address. Existing registrations must
be the same records, not just reuse an old numeric registration identity. -/
def RetentionPermitted (program : Kernel.Program) (contract : Contract) (model : Model)
    (initial current : World) (session : ForeignSession)
    (before after : List Nat) : Prop :=
  ∀ registration ∈ model.registrations after, registration.active = true → registration.retained = true →
    registration ∈ model.registrations before ∨
      Retainable program model contract initial current session registration.owner

/-- Laws constrain the model only on its declared contract domain. World
typing is derived from mutations; no post-world typing assumption occurs. -/
structure Model.Lawful (program : Kernel.Program) (model : Model) : Prop where
  imports : (model.imports.map (·.declaration)).Nodup
  contracts : (model.contracts.map (·.declaration)).Nodup
  start : ∀ initial imported contract world state,
    Selected program model initial.call imported contract → world.WellFormed → CallTyped program world initial.call →
    contract.precondition world initial → model.start initial.call.binding.declaration world initial state →
    contract.session world { initial with state } ∧ RegistrationsValid program model world state ∧
    RetentionPermitted program contract model world world initial initial.state state
  step : ∀ session imported contract before observation after action next,
    Selected program model session.call imported contract → before.WellFormed → contract.session before session →
    model.step session.call.binding.declaration before session observation after action next →
    Mutations program (Policy program model contract before session) before after ∧
    contract.transition before session after action ∧
    FramePreserved program model contract before session after ∧ RegistrationsValid program model after next ∧
    (action = .continue → contract.session after (session.advance before after next)) ∧
    (∀ result, action = .result result → contract.normalPostcondition before session after result ∧
      Accessible program model contract before after session ⟨result,.owner⟩ ∧
      ∃ value, after.Stores result value ∧ value.Initialized ∧ value.type = session.call.signature.result) ∧
    (∀ registration arguments, action = .callback registration arguments →
      contract.callbackPrecondition after (session.advance before after next) registration ∧
      ∀ argument ∈ arguments, Accessible program model contract before after session argument) ∧
    (∀ address value id loan, after.Resident address value → value.head = .reference id →
      after.loans.get id = some loan → ¬ before.References id →
      Retainable program model contract before after session loan.referent ∨ loan.region ∈ before.liveRegions) ∧
    RetentionPermitted program contract model before after session session.state next
  callbackReturned : ∀ session imported contract world current registration result next,
    Selected program model session.call imported contract → world.WellFormed →
    contract.callbackPostcondition world session current registration result →
    model.callbackReturned session.call.binding.declaration world session current registration result next →
    contract.session world (session.returned result next) ∧ RegistrationsValid program model world next ∧
    RetentionPermitted program contract model world world
      (session.returned result current) current next

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
def CallbackReturnTask (session : ForeignSession) (registration : Identity) (result : Address)
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
        ⟨⟨context,destination,binding,arguments,signature,addresses⟩,before.hostState,AmbientExposed before.frames⟩ →
      model.start binding.declaration prepared
        ⟨⟨context,destination,binding,arguments,signature,addresses⟩,before.hostState,AmbientExposed before.frames⟩ state →
      Step program model before none
        { before with world := prepared, hostState := state, task := .foreign ⟨⟨context,destination,binding,arguments,signature,addresses⟩,state,AmbientExposed before.frames⟩ next }
  | host {before session next imported contract observation after nextState} :
      before.task = .foreign session next → before.hostState = session.state → Selected program model session.call imported contract →
      contract.session before.world session →
      model.step session.call.binding.declaration before.world session observation after .continue nextState →
      Step program model before (some (.host imported.symbol session.state observation))
        { before with world := after, hostState := nextState, task := .foreign (session.advance before.world after nextState) next }
  | result {before session next imported contract observation after result nextState transferred} :
      before.task = .foreign session next → before.hostState = session.state → Selected program model session.call imported contract →
      contract.session before.world session →
      model.step session.call.binding.declaration before.world session observation after (.result result) nextState →
      (∀ registration ∈ model.registrations nextState, registration.active = true →
        ¬ result.Overlaps registration.owner ∧ ¬ session.call.destination.Overlaps registration.owner) →
      Transfers program.declarations after .owner result session.call.destination transferred →
      Step program model before (some (.host imported.symbol session.state observation))
        { before with world := transferred, hostState := nextState, task := .retire result.root (.run session.call.context next) }
  | callback {before session next imported contract observation after id arguments nextState registration function lease authority lent captures inputs consumed} :
      before.task = .foreign session next → before.hostState = session.state → Selected program model session.call imported contract →
      contract.session before.world session →
      model.step session.call.binding.declaration before.world session observation after (.callback id arguments) nextState →
      registration ∈ model.registrations session.state → registration.identity = id → registration.active = true →
      Accessible program model contract before.world after session
        ⟨registration.owner,registration.authority.lend registration.access⟩ →
      (registration.access = .owned → ∀ current ∈ model.registrations nextState, current.active = true →
        ¬ registration.owner.Overlaps current.owner) →
      CallableReceiver after registration.owner registration.authority registration.access registration.function registration.arguments →
      Instance program registration.function registration.arguments function → function.signature.effects = .row [] [] →
      (session.call.binding.cABI = true → ∃ abi, CSignature program.declarations function.signature abi) →
      LendsReceiver program session.call.context after registration.owner registration.authority registration.access lease authority lent →
      CaptureInputs lent registration.owner authority registration.access function.captures captures →
      CallbackInputs lent function.parameters arguments inputs →
      ConsumesReceiver lent registration.owner authority registration.access consumed →
      Step program model before (some (.host imported.symbol session.state observation))
        { before with world := consumed, hostState := nextState, task := .enter session.call.context function (.supplied (captures ++ inputs)) false, frames := .hostCallback (session.advance before.world after nextState) id function.signature.result lease next :: before.frames }
  | callbackResult {before context result session registration resultType lease next rest value kept protectedWorld after} :
      before.task = .yield context result → before.frames = .hostCallback session registration resultType lease next :: rest →
      before.world.Stores result value → value.type = resultType →
      Protect program session.call.context before.world result .owner kept protectedWorld →
      Retires protectedWorld result.root after →
      Step program model before none
        { before with world := after, frames := rest, task := CallbackReturnTask session registration kept lease next }
  | callbackReturned {before session registration result next imported contract nextState} :
      before.task = .foreignCallbackReturned session registration result next →
      Selected program model session.call imported contract →
      contract.callbackPostcondition before.world session before.hostState registration result →
      model.callbackReturned session.call.binding.declaration before.world session before.hostState registration result nextState →
      Step program model before none
        { before with hostState := nextState, task := .foreign (session.returned result nextState) next }
  | fault {before session next imported contract observation after nextState} :
      before.task = .foreign session next → before.hostState = session.state → Selected program model session.call imported contract →
      contract.session before.world session →
      model.step session.call.binding.declaration before.world session observation after .fault nextState →
      Step program model before (some (.fatal .hostContract)) { before with world := after, hostState := nextState, task := .fatal .hostContract }

def NoForeignCapture (frames : List Frame) : Prop :=
  ∀ frame ∈ frames, (∀ identity, frame ≠ .foreign identity) ∧
    ∀ session registration resultType lease next, frame ≠ .hostCallback session registration resultType lease next

theorem callback_barrier_not_empty {session registration resultType lease next rest} :
    ¬ NoForeignCapture (.hostCallback session registration resultType lease next :: rest) := by
  intro safe
  exact (safe (.hostCallback session registration resultType lease next) (by simp)).2
    session registration resultType lease next rfl

end Glorious.Language.Foreign
