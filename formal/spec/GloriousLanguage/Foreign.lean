import GloriousLanguage.Primitives

/-! The external world is an explicit semantic parameter, not an invented
implementation of library services. Reviewed safety contracts and linkage
are separate. C callbacks execute real source bodies between foreign frames. -/
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

structure Registration where
  identity : Identity
  owner : Address
  function : DeclId
  arguments : List Term
  captures : List Address
  runtime : Identity
  entryAddress : Nat
  active : Bool
  retained : Bool
  extent : Identity

def Registration.Valid (program : Kernel.Program) (world : World) (registration : Registration) : Prop :=
  registration.active = true →
    world.Initialized registration.owner ∧
    (∃ function, Instance program registration.function registration.arguments function) ∧
    (∀ address ∈ registration.captures, world.Initialized address) ∧
    (registration.retained = false → registration.extent ∈ world.liveRegions)

inductive HostAction where
  | result (value : Address)
  | callback (function : DeclId) (arguments : List Term) (inputs : List InvocationInput)
  | continue
  | fault
  deriving Repr, Inhabited

structure Contract where
  declaration : DeclId
  precondition : World → List Address → Prop
  transition : World → List Address → World → HostAction → Prop
  normalPostcondition : World → List Address → World → Address → Prop
  writable : World → List Address → Address → Prop
  retainable : World → List Address → Address → Prop

structure Model where
  imports : List Import
  contracts : List Contract
  registrations : List Registration
  start : DeclId → World → List Address → List Nat → Prop
  step : DeclId → World → List Address → List Nat →
    List Nat → World → HostAction → List Nat → Prop

def Selected (program : Kernel.Program) (model : Model) (binding : RuntimeBinding) (imported : Import) (contract : Contract) : Prop :=
  binding ∈ program.declarations.input.manifest.bindings ∧ binding.primitive = none ∧
  imported ∈ model.imports ∧ imported.declaration = binding.declaration ∧ binding.symbol = some imported.symbol ∧
  imported.capability = binding.capability ∧ imported.domain = binding.domain ∧
  contract ∈ model.contracts ∧ contract.declaration = binding.declaration ∧
  (binding.cABI = true → CSignature program.declarations binding.signature imported.signature) ∧
  (binding.signature.unsafeAllowed = false → binding.safeReviewed = true ∧ imported.reviewedSafe = true)

def FramePreserved (contract : Contract) (before : World) (operands : List Address) (after : World) : Prop :=
  ∀ address value, before.Resident address value →
    (∀ ancestor, ancestor.Overlaps address → ¬ contract.writable before operands ancestor) → after.Stores address value

def Model.Lawful (program : Kernel.Program) (model : Model) : Prop :=
  (model.imports.map (·.declaration)).Nodup ∧ (model.contracts.map (·.declaration)).Nodup ∧
  ∀ binding imported contract before operands state observation after action next,
    Selected program model binding imported contract → before.WellFormed → contract.precondition before operands →
    model.step binding.declaration before operands state observation after action next →
    after.WellFormed ∧ contract.transition before operands after action ∧ FramePreserved contract before operands after ∧
    (∀ result, action = .result result → contract.normalPostcondition before operands after result) ∧
    (∀ registration ∈ model.registrations, registration.Valid program after) ∧
    (∀ address value id loan, after.Resident address value → value.head = .reference id →
      after.loans.get id = some loan → ¬ before.References id →
      contract.retainable before operands loan.referent ∨ loan.region ∈ before.liveRegions)

inductive Step (program : Kernel.Program) (model : Model) : State → Option Event → State → Prop where
  | enter {before context destination binding arguments operands next imported contract state addresses prepared} :
      before.task = .primitive context destination binding arguments operands next →
      Selected program model binding imported contract →
      Protects program context before.world operands addresses prepared →
      contract.precondition prepared addresses → model.start binding.declaration prepared addresses state →
      Step program model before none { before with world := prepared, task := .foreign context destination binding addresses state next }
  | host {before context destination binding operands state next imported contract observation after nextState} :
      before.task = .foreign context destination binding operands state next → Selected program model binding imported contract →
      model.step binding.declaration before.world operands state observation after .continue nextState →
      Step program model before (some (.host imported.symbol state observation))
        { before with world := after, task := .foreign context destination binding operands nextState next }
  | result {before context destination binding operands state next imported contract observation after result nextState transferred} :
      before.task = .foreign context destination binding operands state next → Selected program model binding imported contract →
      model.step binding.declaration before.world operands state observation after (.result result) nextState →
      Transfers program.declarations after .owner result destination transferred →
      Step program model before (some (.host imported.symbol state observation))
        { before with world := transferred, task := .run context next }
  | callback {before context destination binding operands state next imported contract observation after id arguments inputs nextState function} :
      before.task = .foreign context destination binding operands state next → Selected program model binding imported contract →
      model.step binding.declaration before.world operands state observation after (.callback id arguments inputs) nextState →
      Instance program id arguments function → function.signature.effects = .row [] [] →
      Step program model before (some (.host imported.symbol state observation)) { before with world := after, task := .enter context function inputs false, frames := .hostCallback context destination binding operands nextState next :: before.frames }
  | callbackResult {before context result outer destination binding operands state next rest value} :
      before.task = .yield context result → before.frames = .hostCallback outer destination binding operands state next :: rest →
      before.world.Stores result value →
      (∀ address resident loanId loan, before.world.Resident address resident → resident.head = .reference loanId →
        before.world.loans.get loanId = some loan → loan.referent.root = result.root → loan.region = outer.region) →
      Step program model before none { before with frames := rest, task := .foreign outer destination binding (operands ++ [result]) state next }
  | fault {before context destination binding operands state next imported contract observation after nextState} :
      before.task = .foreign context destination binding operands state next → Selected program model binding imported contract →
      model.step binding.declaration before.world operands state observation after .fault nextState →
      Step program model before (some (.fatal .hostContract)) { before with world := after, task := .fatal .hostContract }

def NoForeignCapture (frames : List Frame) : Prop :=
  ∀ frame ∈ frames, (∀ identity, frame ≠ .foreign identity) ∧
    ∀ context destination binding operands state next, frame ≠ .hostCallback context destination binding operands state next

theorem callback_barrier_not_empty {context destination binding operands state next rest} :
    ¬ NoForeignCapture (.hostCallback context destination binding operands state next :: rest) := by
  intro safe
  exact (safe (.hostCallback context destination binding operands state next) (by simp)).2
    context destination binding operands state next rfl

end Glorious.Language.Foreign
