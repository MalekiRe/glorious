import GloriousLanguage.Foreign

/-! Lexical transfers and sealed control witnesses. Reservations name actual
storage in the one world; closing a proof-only witness schedules real cleanup.
Pattern environments contain exactly the fields justified by that match. -/
namespace Glorious.Language.Execution

open Kernel

def LabelBarrier (frame : Frame) : Prop := frame.ForeignFree

def LabelRoute (frames : List Frame) (brand : Identity) (inner : List Frame)
    (outerContext : Context) (region : Identity) (type : Term) (outer : List Frame) : Prop :=
  frames = inner ++ .label outerContext brand region type :: outer ∧
  (∀ frame ∈ inner, LabelBarrier frame) ∧
  (∀ context region type, Frame.label context brand region type ∉ inner)

def AbandonedRoots (world : World) (frames : List Frame) (kept roots : List Identity) : Prop :=
  RootsWhere world (fun id root => root.live = true ∧ id ∉ kept ∧ ∃ frame ∈ frames, FrameOwns frame root) roots

def DisposesReservations (context : Context) (places : List ResolvedPlace) (next : Task) : Task :=
  places.foldr (fun place task => .destroy context place.address place.authority task) next

/-- The frozen reservation ledger supplies both storage and its exact resident
type product. Invocation cannot recover a different capture shape from an
independent environment declaration or an unrelated subtype view. -/
def ReservationInputs (world : World) (available : Availability) (access : Access)
    (formals : List Local) (inputs : List InvocationInput) : Prop :=
  available.reserved.length = formals.length ∧ formals.map (·.type) = available.residents ∧
  inputs = (formals.zip available.reserved).zipIdx.map
    (fun (entry,index) => ⟨.capture index,entry.1,entry.2.address,entry.2.authority,access⟩) ∧
  ∀ input ∈ inputs, Permitted world input.authority access input.storage ∧
    ∃ value, world.Stores input.storage value ∧ value.Initialized ∧ value.type = input.formal.type

inductive ConsumesAvailability : World → Address → Identity → Access → World → Prop where
  | lent {world address id access} : access ≠ .owned → ConsumesAvailability world address id access world
  | owned {before address id available cleared} : before.availability.get id = some available →
      before.write address none = some cleared →
      ConsumesAvailability before address id .owned
        { cleared with availability := cleared.availability.set id { available with active := false } }

def ReservationCanClose (program : Kernel.Program) (world : World) (available : Availability) : Prop :=
  available.active = true ∧
  (∀ place ∈ available.reserved, ∀ value, world.Stores place.address value →
    MayDispose program.declarations value ∧ Permitted world place.authority .owned place.address) ∧
  Suspensible world (available.reserved.map (fun place => place.address.root))

mutual
  inductive ObservedBindings (program : Kernel.Program) :
      World → Address → Authority → Pattern → List (Local × Address × Authority) → Prop where
    | wildcard {world address authority} : ObservedBindings program world address authority .wildcard []
    | literal {world address authority scalar} : ObservedBindings program world address authority (.scalar scalar) []
    | unit {world address authority} : ObservedBindings program world address authority .unit []
    | bind {world address authority localSlot} : ObservedBindings program world address authority (.bind localSlot) [(localSlot,address,authority)]
    | aggregate {world address authority pattern fields bindings} :
        (pattern = .tuple fields ∨ pattern = .array fields ∨ ∃ id, pattern = .constructor id fields) →
        ObservedFields program world address authority 0 fields bindings →
        ObservedBindings program world address authority pattern bindings
    | reference {world address authority value id loan mode pattern bindings view access} : world.Stores address value → value.head = .reference id →
        world.loans.get id = some loan → loan.mode = mode → loan.live = true →
        value.Initialized → Permitted world authority .shared address →
        ReferenceView world address authority id mode view access →
        ObservedBindings program world loan.referent view pattern bindings →
        ObservedBindings program world address authority (.reference mode pattern) bindings

  inductive ObservedFields (program : Kernel.Program) :
      World → Address → Authority → Nat → List Pattern → List (Local × Address × Authority) → Prop where
    | nil {world address authority index} : ObservedFields program world address authority index [] []
    | cons {world address authority index first rest bindings more} :
        ObservedBindings program world (address.child index) authority first bindings →
        ObservedFields program world address authority (index+1) rest more →
        ObservedFields program world address authority index (first :: rest) (bindings ++ more)
end

inductive CopiesObservations (program : Kernel.Program) (context : Context) :
    World → List (Local × Address × Authority) → List (Local × Address) → World → Prop where
  | nil {world} : CopiesObservations program context world [] [] world
  | copy {before localSlot source authority rest destination allocated copied bindings after value} :
      before.Stores source value → localSlot.type = value.type → Temporary program context localSlot.type before destination allocated →
      Copies program.declarations allocated authority source destination copied →
      CopiesObservations program context copied rest bindings after →
      CopiesObservations program context before ((localSlot,source,authority) :: rest) ((localSlot,destination) :: bindings) after
  | borrow {before localSlot source authority rest destination allocated borrowed bindings after value mode} :
      before.Stores source value → localSlot.type = .reference mode (.runtimeRegion context.region) value.type →
      Temporary program context localSlot.type before destination allocated →
      Borrows program.declarations allocated authority mode context.region source destination borrowed →
      CopiesObservations program context borrowed rest bindings after →
      CopiesObservations program context before ((localSlot,source,authority) :: rest) ((localSlot,destination) :: bindings) after

def PacksBindings (program : Kernel.Program) (context : Context) (before : World) (pattern : Identity)
    (resultOrigin : Identity) (positive : Bool) (bindings : List (Local × Address))
    (pack : Address) (after : World) : Prop :=
  ∃ allocated created type,
    type = .bindings (.runtimeBrand (.proof before.nextProof)) (.runtimeRegion context.region) (bindings.map (fun entry => entry.1.type)) ∧
    Temporary program context type before pack allocated ∧
    (bindings.map (fun entry => entry.1.id)).Nodup ∧
    NewValue program.declarations allocated pack type
      (.bindings ⟨before.nextProof,context.region,bindings.map (fun entry => entry.1.id),[⟨resultOrigin,pattern,positive⟩]⟩)
      (bindings.map (fun entry => ⟨entry.2,.owner⟩)) created ∧
    after = { created with nextProof := before.nextProof+1 }

inductive UnitFields (program : Kernel.Program) (context : Context) :
    World → List Term → Option Nat → Address → List Address → World → Prop where
  | done {world pack} : UnitFields program context world [] none pack [] world
  | selected {before type types pack rest after value} : before.Stores pack value → value.type = type →
      UnitFields program context before types none pack rest after →
      UnitFields program context before (type :: types) (some 0) pack (pack :: rest) after
  | unitBefore {before types index pack address allocated created rest after} :
      Temporary program context .unit before address allocated → StoresUnit program allocated address created →
      UnitFields program context created types (some index) pack rest after →
      UnitFields program context before (.unit :: types) (some (index+1)) pack (address :: rest) after
  | unitAfter {before types pack address allocated created rest after} :
      Temporary program context .unit before address allocated → StoresUnit program allocated address created →
      UnitFields program context created types none pack rest after →
      UnitFields program context before (.unit :: types) none pack (address :: rest) after

def CarrierFields (program : Kernel.Program) (context : Context) (before : World) (type : Term) (variant : DeclId)
    (pack : Address) (packIndex : Nat) (fields : List Address) (after : World) : Prop :=
  ∃ types,
    ConstructorHead program.declarations type (some variant) types (.constructor variant) ∧ fields.length = types.length ∧
    fields[packIndex]? = some pack ∧
    (∀ index address type, fields[index]? = some address → types[index]? = some type →
      index = packIndex ∨ type = .unit ∧ ∃ value, after.Stores address value ∧ value.type = .unit ∧ value.head = .unit) ∧
    UnitFields program context before types (some packIndex) pack fields after

inductive TestResult (program : Kernel.Program) (context : Context) :
    World → Address → Term → Identity → Bool → List (Local × Address × Authority) → World → Prop where
  | result {before destination type pattern positive observations carrier dataArguments copied bindings packed pack fields assembled after} :
      program.declarations.input.manifest.testCarrier = some carrier → type = .nominal carrier.declaration dataArguments →
      CopiesObservations program context before observations bindings copied →
      PacksBindings program context copied pattern assembled.nextOwner positive bindings pack packed →
      CarrierFields program context packed type (if positive then carrier.positive else carrier.negative) pack
        (if positive then carrier.positiveBindings else carrier.negativeBindings) fields assembled →
      NewValue program.declarations assembled destination type
        (.constructor (if positive then carrier.positive else carrier.negative))
        (fields.map (fun address => ⟨address,.owner⟩)) after →
      TestResult program context before destination type pattern positive observations after

inductive ControlStep (program : Kernel.Program) : State → Option Event → State → Prop where
  | labelCall {before context call tail receiver authority value brand argument permission} : before.task = .apply context call tail →
      call.environment = none →
      ResolvesPlace before.world context.environment call.callee receiver authority → before.world.Stores receiver value →
      value.head = .label brand → Permitted before.world authority .shared receiver →
      (∃ place, call.arguments = [place] ∧ ResolvesPlace before.world context.environment place argument permission) →
      ControlStep program before (some (.leave brand)) { before with task := .leave context brand ⟨argument,permission⟩ }
  | leave {before context brand argument inner outerContext region type outer kept after roots} :
      before.task = .leave context brand argument → LabelRoute before.frames brand inner outerContext region type outer →
      Protect program outerContext before.world argument.address argument.authority kept after →
      AbandonedRoots after inner [kept.root] roots → Cancelable program.declarations after roots →
      ControlStep program before none { before with world := after, frames := outer, task := .cleanup context roots (CloseRegions (inner.flatMap Frame.ownedRegions) (.yield outerContext kept)) }
  | reserve {before context lexical bound localSlot brand places next reserved types allocated destination after layout} :
      before.task = .run context (.reserve lexical brand places next) →
      bound = context.bindBrand brand (.proof before.world.nextProof) → localSlot = bound.local lexical →
      ResolvedOperands before.world context.environment places reserved →
      ListRel (fun place type => AddressType program.declarations before.world place.address type) reserved types →
      (reserved.map ResolvedPlace.address).Nodup →
      (∀ a ∈ reserved, ∀ b ∈ reserved, a.address ≠ b.address → ¬ a.address.Overlaps b.address) →
      (∀ id available, before.world.availability.get id = some available → available.active = true →
        ∀ a ∈ available.reserved, ∀ b ∈ reserved, ¬ a.address.Overlaps b.address) →
      localSlot.type = .available (.runtimeBrand (.proof before.world.nextProof)) (.runtimeRegion context.region) types →
      Allocates program.declarations before.world (.localSlot context.activation context.scope) context.region localSlot.type layout
        localSlot.mutable destination allocated →
      NewValue program.declarations allocated destination localSlot.type (.available before.world.nextProof) [] after →
      ControlStep program before none { before with world := { after with nextProof := before.world.nextProof+1, availability := after.availability.set before.world.nextProof ⟨before.world.nextProof,.runtimeBrand (.proof before.world.nextProof),context.region,reserved,types,true⟩ }, task := .run (bound.bind localSlot destination) next }
  | available {before context destination place id next source authority value after} :
      before.task = .atom context destination (.available place) next →
      ResolvesPlace before.world context.environment place source authority →
      before.world.Stores source value → value.head = .available id →
      Transfers program.declarations before.world authority source destination after →
      ControlStep program before (some (.move source destination)) { before with world := after, task := .run context next }
  | closeAvailable {before context place next address authority value id} :
      before.task = .run context (.closeAvailable place next) → ResolvesPlace before.world context.environment place address authority →
      before.world.Stores address value → value.head = .available id →
      ControlStep program before none { before with task := .destroy context address authority (.run context next) }
  | primitiveCloseAvailable {before context destination binding arguments source next value id} :
      before.task = .primitive context destination binding arguments [source] next → binding.primitive = some .availableClose →
      before.world.Stores source.address value → value.head = .available id →
      ControlStep program before none
        { before with task := .destroy context source.address source.authority (.atom context destination (.constant (.constantTuple [])) next) }
  | destroyAvailable {before context address authority next value id available cleared} :
      before.task = .destroy context address authority next → before.world.Stores address value → value.head = .available id →
      before.world.availability.get id = some available → ReservationCanClose program before.world available →
      Permitted before.world authority .owned address → before.world.write address none = some cleared →
      ControlStep program before none { before with world := { cleared with availability := cleared.availability.set id { available with active := false } }, task := DisposesReservations context available.reserved.reverse next }
  | destroySpentAvailable {before context address authority next value id available cleared} :
      before.task = .destroy context address authority next → before.world.Stores address value → value.head = .available id →
      before.world.availability.get id = some available → available.active = false →
      Permitted before.world authority .owned address → before.world.write address none = some cleared →
      ControlStep program before none { before with world := cleared, task := next }
  | contextualCall {before context call tail receiver authority id arguments function selected token witness permission
      available witnessValue captures inputs consumed after value} :
      before.task = .apply context call tail → call.environment = some selected →
      ResolvesPlace before.world context.environment call.callee receiver authority → before.world.Stores receiver value →
      value.head = .callable id arguments → value.fields = [] → Instance program id arguments function →
      function.signature = call.signature → Permitted before.world authority call.receiver receiver →
      ResolvesPlace before.world context.environment selected.witness witness permission →
      before.world.Stores witness witnessValue → witnessValue.Initialized → witnessValue.head = .available token →
      Permitted before.world permission selected.access witness →
      before.world.availability.get token = some available → available.active = true → available.region ∈ before.world.liveRegions →
      witnessValue.type = .available available.brand (.runtimeRegion available.region) available.residents →
      RunsInEnvironment program.declarations context.static call (.callable id arguments)
        available.brand (.runtimeRegion available.region) available.residents →
      ReservationInputs before.world available selected.access function.captures captures →
      ArgumentInputs before.world context 0 function.parameters call.arguments inputs →
      ConsumesReceiver before.world receiver authority call.receiver consumed →
      ConsumesAvailability consumed witness token selected.access after →
      ControlStep program before (some (.call id (captures ++ inputs)))
        { before with world := after, task := .enter context function (.contextual ⟨receiver,authority⟩ call.receiver ⟨witness,permission⟩ selected.access (captures ++ inputs)) tail }
  | positiveTest {before context lexical bound localSlot subject sourcePattern pattern patternId next source authority bindings destination allocated after layout} :
      before.task = .run context (.test lexical subject sourcePattern patternId next) →
      bound = context.bindBrand patternId (.proof before.world.nextProof) → localSlot = bound.local lexical →
      pattern = sourcePattern.mapTerms bound.term →
      ResolvesPlace before.world context.environment subject source authority →
      Matches program.declarations before.world source pattern → ObservedBindings program before.world source authority pattern bindings →
      Allocates program.declarations before.world (.localSlot context.activation context.scope) context.region
        localSlot.type layout localSlot.mutable destination allocated →
      TestResult program bound allocated destination localSlot.type patternId true bindings after →
      ControlStep program before (some (.branch patternId true))
        { before with world := after, task := .run (bound.bind localSlot destination) next }
  | negativeTest {before context lexical bound localSlot subject sourcePattern pattern patternId next source authority destination allocated after layout} :
      before.task = .run context (.test lexical subject sourcePattern patternId next) →
      bound = context.bindBrand patternId (.proof before.world.nextProof) → localSlot = bound.local lexical →
      pattern = sourcePattern.mapTerms bound.term →
      ResolvesPlace before.world context.environment subject source authority → before.world.Initialized source →
      Permitted before.world authority .shared source → ¬ Matches program.declarations before.world source pattern →
      Allocates program.declarations before.world (.localSlot context.activation context.scope) context.region
        localSlot.type layout localSlot.mutable destination allocated →
      TestResult program bound allocated destination localSlot.type patternId false [] after →
      ControlStep program before (some (.branch patternId false))
        { before with world := after, task := .run (bound.bind localSlot destination) next }
  | bindings {before context destination place id next source authority value after} : before.task = .atom context destination (.bindings place) next →
      ResolvesPlace before.world context.environment place source authority →
      before.world.Stores source value → value.head = .bindings id →
      Transfers program.declarations before.world authority source destination after →
      ControlStep program before (some (.move source destination)) { before with world := after, task := .run context next }

/-- This is the sole executable transition relation consumed by typing,
control contracts, source behavior and target refinement. -/
def Step (program : Kernel.Program) (host : Foreign.Model) (before : State) (event : Option Event) (after : State) : Prop :=
  LocalStep program before event after ∨ AtomStep program before event after ∨
  EffectStep program before event after ∨ ControlStep program before event after ∨
  PrimitiveStep program before event after ∨ Foreign.Step program host before event after

inductive Run (program : Kernel.Program) (host : Foreign.Model) : State → List Event → State → Prop where
  | refl {state} : Run program host state [] state
  | silent {before middle after trace} : Step program host before none middle → Run program host middle trace after →
      Run program host before trace after
  | visible {before middle after event trace} : Step program host before (some event) middle → Run program host middle trace after →
      Run program host before (event :: trace) after

theorem Run.append {program : Kernel.Program} {host : Foreign.Model}
    {before middle after : State} {first last : List Event}
    (left : Run program host before first middle) (right : Run program host middle last after) :
    Run program host before (first ++ last) after := by
  induction left with
  | refl => exact right
  | silent step _ ih => exact .silent step (ih right)
  | visible step _ ih => exact .visible step (ih right)

end Glorious.Language.Execution
