import GloriousLanguage.Primitives

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

/-- Host code explains actual changes using existing resident producers. It
cannot forge references, callables, proof brands, owners or pointer origins. -/
inductive Mutation (program : Kernel.Program) : World → World → Prop where
  | allocate {before after home region type layout mutable address} :
      Allocates program.declarations before home region type layout mutable address after → Mutation program before after
  | scalar {before after destination value} : StoresScalar program before destination value after → Mutation program before after
  | unit {before after destination} : StoresUnit program before destination after → Mutation program before after
  | pointer {before after destination mode type pointer} :
      pointer.address < 2^program.declarations.input.target.pointerBits → pointer.Origin before →
      StoresPointer program before destination mode type pointer after → Mutation program before after
  | aggregate {before after destination type variant sources values head} :
      ListRel (fun source value => before.Stores source.address value) sources values →
      ConstructorHead program.declarations type variant (values.map Value.type) head →
      NewValue program.declarations before destination type head sources after → Mutation program before after
  | acquire {before after authority force source destination} :
      Acquires program.declarations before authority force source destination after → Mutation program before after
  | borrow {before after authority mode region source destination} :
      Borrows program.declarations before authority mode region source destination after → Mutation program before after
  | allocateBuffer {before after domain element count base pointer} :
      AllocatesBuffer program.declarations before domain element count base pointer after → Mutation program before after
  | reallocateBuffer {before after old domain element count base pointer} :
      ReallocatesBuffer program.declarations before old domain element count base pointer after → Mutation program before after
  | releaseBuffer {before after pointer domain} : ReleasesBuffer program.declarations before pointer domain after → Mutation program before after
  | rawRead {before after pointer type copy destination} :
      RawRead program.declarations before pointer type copy destination after → Mutation program before after
  | rawWrite {before after authority source pointer type} :
      RawWrite program.declarations before authority source pointer type after → Mutation program before after
  | rawBorrow {before after pointer type mode region destination} :
      RawBorrow program.declarations before pointer type mode region destination after → Mutation program before after
  | bulkMove {before after sources destinations} :
      BulkMove program.declarations before sources destinations after → Mutation program before after
  | retire {before after root} : Retires before root after → Mutation program before after
  | endLoan {before after loan} : EndsLoan before loan after → Mutation program before after

inductive Mutations (program : Kernel.Program) : World → World → Prop where
  | refl {world} : Mutations program world world
  | cons {before middle after} : Mutation program before middle → Mutations program middle after → Mutations program before after

structure Contract where
  declaration : DeclId
  precondition : World → ForeignCall → List Nat → Prop
  session : World → ForeignSession → Prop
  transition : World → ForeignSession → World → HostAction → Prop
  normalPostcondition : World → ForeignSession → World → Address → Prop
  callbackPrecondition : World → ForeignSession → Identity → Prop
  callbackPostcondition : World → ForeignSession → List Nat → Identity → Address → Prop
  writable : World → ForeignCall → Address → Prop
  retainable : World → ForeignCall → Address → Prop

structure Model where
  imports : List Import
  contracts : List Contract
  /-- Registry and runtime liveness evolve, permitting unregister/shutdown. -/
  registrations : List Nat → List Registration
  runtimes : List Nat → List Identity
  start : DeclId → World → ForeignCall → List Nat → List Nat → Prop
  step : DeclId → World → ForeignSession → List Nat → World → HostAction → List Nat → Prop
  callbackReturned : DeclId → World → ForeignSession → List Nat → Identity → Address → List Nat → Prop

def Selected (program : Kernel.Program) (model : Model) (call : ForeignCall) (imported : Import) (contract : Contract) : Prop :=
  call.binding ∈ program.declarations.input.manifest.bindings ∧ call.binding.primitive = none ∧
  imported ∈ model.imports ∧ imported.declaration = call.binding.declaration ∧ call.binding.symbol = some imported.symbol ∧
  imported.capability = call.binding.capability ∧ imported.domain = call.binding.domain ∧
  contract ∈ model.contracts ∧ contract.declaration = call.binding.declaration ∧
  (call.binding.cABI = true → CSignature program.declarations call.signature imported.signature) ∧
  (call.signature.unsafeAllowed = false → call.binding.safeReviewed = true ∧ imported.reviewedSafe = true)

def FramePreserved (contract : Contract) (before : World) (call : ForeignCall) (after : World) : Prop :=
  ∀ address value, before.Resident address value →
    (∀ ancestor, ancestor.Overlaps address → ¬ contract.writable before call ancestor) → after.Stores address value

def RegistrationsValid (program : Kernel.Program) (model : Model) (world : World) (state : List Nat) : Prop :=
  (model.registrations state |>.map (·.identity)).Nodup ∧
  ∀ registration ∈ model.registrations state, registration.Valid program world (model.runtimes state)

/-- Keeping a newly registered owner is a contract capability, independently
of linking the callback's machine entry address. Existing registrations must
be the same records, not just reuse an old numeric registration identity. -/
def RetentionPermitted (contract : Contract) (model : Model) (world : World) (call : ForeignCall)
    (before after : List Nat) : Prop :=
  ∀ registration ∈ model.registrations after, registration.active = true → registration.retained = true →
    registration ∈ model.registrations before ∨ contract.retainable world call registration.owner

/-- Laws constrain the model only on its declared contract domain. World
typing is derived from mutations; no post-world typing assumption occurs. -/
structure Model.Lawful (program : Kernel.Program) (model : Model) : Prop where
  imports : (model.imports.map (·.declaration)).Nodup
  contracts : (model.contracts.map (·.declaration)).Nodup
  start : ∀ call imported contract world previous state,
    Selected program model call imported contract → world.WellFormed → CallTyped program world call →
    contract.precondition world call previous → model.start call.binding.declaration world call previous state →
    contract.session world ⟨call,state⟩ ∧ RegistrationsValid program model world state ∧
    RetentionPermitted contract model world call previous state
  step : ∀ session imported contract before observation after action next,
    Selected program model session.call imported contract → before.WellFormed → contract.session before session →
    model.step session.call.binding.declaration before session observation after action next →
    Mutations program before after ∧ contract.transition before session after action ∧
    FramePreserved contract before session.call after ∧ RegistrationsValid program model after next ∧
    (action = .continue → contract.session after ⟨session.call,next⟩) ∧
    (∀ result, action = .result result → contract.normalPostcondition before session after result ∧
      ∃ value, after.Stores result value ∧ value.Initialized ∧ value.type = session.call.signature.result) ∧
    (∀ registration arguments, action = .callback registration arguments →
      contract.callbackPrecondition after ⟨session.call,next⟩ registration) ∧
    (∀ address value id loan, after.Resident address value → value.head = .reference id →
      after.loans.get id = some loan → ¬ before.References id →
      contract.retainable before session.call loan.referent ∨ loan.region ∈ before.liveRegions) ∧
    RetentionPermitted contract model before session.call session.state next
  callbackReturned : ∀ session imported contract world current registration result next,
    Selected program model session.call imported contract → world.WellFormed →
    contract.callbackPostcondition world session current registration result →
    model.callbackReturned session.call.binding.declaration world session current registration result next →
    contract.session world ⟨session.call,next⟩ ∧ RegistrationsValid program model world next ∧
    RetentionPermitted contract model world session.call current next

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
      contract.precondition prepared ⟨context,destination,binding,arguments,signature,addresses⟩ before.hostState →
      model.start binding.declaration prepared ⟨context,destination,binding,arguments,signature,addresses⟩ before.hostState state →
      Step program model before none
        { before with world := prepared, hostState := state, task := .foreign ⟨⟨context,destination,binding,arguments,signature,addresses⟩,state⟩ next }
  | host {before session next imported contract observation after nextState} :
      before.task = .foreign session next → before.hostState = session.state → Selected program model session.call imported contract →
      contract.session before.world session →
      model.step session.call.binding.declaration before.world session observation after .continue nextState →
      Step program model before (some (.host imported.symbol session.state observation))
        { before with world := after, hostState := nextState, task := .foreign ⟨session.call,nextState⟩ next }
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
        { before with world := consumed, hostState := nextState, task := .enter session.call.context function (.supplied (captures ++ inputs)) false, frames := .hostCallback ⟨session.call,nextState⟩ id function.signature.result lease next :: before.frames }
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
        { before with hostState := nextState, task := .foreign ⟨session.call,nextState⟩ next }
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
