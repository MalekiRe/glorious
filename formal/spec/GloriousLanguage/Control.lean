import GloriousLanguage.Foreign

/-! Lexical transfers and sealed control witnesses. Reservations name actual
storage in the one world; closing a proof-only witness schedules real cleanup.
Pattern environments contain exactly the fields justified by that match. -/
namespace Glorious.Language.Execution

open Kernel

def LabelBarrier : Frame → Prop
  | .foreign .. | .hostCallback .. => False
  | _ => True

def LabelRoute (frames : List Frame) (brand : Identity) (inner : List Frame)
    (outerContext : Context) (region : Identity) (type : Term) (outer : List Frame) : Prop :=
  frames = inner ++ .label outerContext brand region type :: outer ∧
  (∀ frame ∈ inner, LabelBarrier frame) ∧
  (∀ context region type, Frame.label context brand region type ∉ inner)

def AbandonedRoots (world : World) (frames : List Frame) (kept roots : List Identity) : Prop :=
  NewestFirst world roots ∧ ∀ id, id ∈ roots ↔ ∃ root,
    world.roots.get id = some root ∧ root.live = true ∧ id ∉ kept ∧ ∃ frame ∈ frames, FrameOwns frame root

def Disposes (context : Context) (addresses : List Address) (next : Task) : Task :=
  addresses.foldr (fun address task => .destroy context address .owner task) next

def ReservedTypes (world : World) (addresses : List Address) (types : List Term) : Prop :=
  ListRel (fun address type => ∃ value, world.Stores address value ∧ value.type = type) addresses types

def ReservationCanClose (program : Kernel.Program) (world : World) (available : Availability) : Prop :=
  available.active = true ∧
  (∀ address ∈ available.reserved, ∀ value, world.Stores address value →
    MayDispose program.declarations value ∧ Permitted world .owner .owned address) ∧
  Suspensible world (available.reserved.map Address.root)

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
    | reference {world address authority value id loan mode pattern bindings} : world.Stores address value → value.head = .reference id →
        world.loans.get id = some loan → loan.mode = mode → loan.live = true →
        ObservedBindings program world loan.referent (.loan id) pattern bindings →
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
    World → List (Local × Address × Authority) → List (Local × Address) → List Identity → World → Prop where
  | nil {world} : CopiesObservations program context world [] [] [] world
  | copy {before localSlot source authority rest destination allocated copied bindings loans after value} :
      before.Stores source value → localSlot.type = value.type → Temporary program context localSlot.type before destination allocated →
      Copies program.declarations allocated authority source destination copied →
      CopiesObservations program context copied rest bindings loans after →
      CopiesObservations program context before ((localSlot,source,authority) :: rest) ((localSlot,destination) :: bindings) loans after
  | borrow {before localSlot source authority rest destination allocated borrowed bindings loans after value mode} :
      before.Stores source value → localSlot.type = .reference mode (.runtimeRegion context.region) value.type →
      Temporary program context localSlot.type before destination allocated →
      Borrows program.declarations allocated authority mode context.region source destination borrowed →
      CopiesObservations program context borrowed rest bindings loans after →
      CopiesObservations program context before ((localSlot,source,authority) :: rest) ((localSlot,destination) :: bindings)
        (allocated.nextLoan :: loans) after

def PacksBindings (program : Kernel.Program) (context : Context) (before : World) (pattern : Identity)
    (positive : Bool) (bindings : List (Local × Address)) (loans : List Identity)
    (pack : Address) (after : World) : Prop :=
  ∃ allocated created type,
    type = .bindings (.runtimeBrand (.proof before.nextProof)) (.runtimeRegion context.region) (bindings.map (fun entry => entry.1.type)) ∧
    Temporary program context type before pack allocated ∧
    NewValue program.declarations allocated pack type (.bindings before.nextProof) (bindings.map Prod.snd) created ∧
    after = { created with nextProof := before.nextProof+1, bindings := created.bindings.set before.nextProof ⟨before.nextProof,pattern,before.nextProof,positive,context.region, bindings.zipIdx.map (fun (entry,index) => (entry.1.id,pack.child index)),loans⟩ }

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

def CarrierFields (program : Kernel.Program) (context : Context) (before : World) (variant : DeclId)
    (arguments : List Term) (pack : Address) (packIndex : Nat) (fields : List Address) (after : World) : Prop :=
  ∃ data constructor substitution types,
    program.declarations.Constructor variant data constructor ∧ Instantiates data.generics arguments substitution ∧
    ListRel (Substitutes substitution) (constructor.fields.map (·.type)) types ∧ fields.length = types.length ∧
    fields[packIndex]? = some pack ∧
    (∀ index address type, fields[index]? = some address → types[index]? = some type →
      index = packIndex ∨ type = .unit ∧ ∃ value, after.Stores address value ∧ value.type = .unit ∧ value.head = .unit) ∧
    UnitFields program context before types (some packIndex) pack fields after

inductive TestResult (program : Kernel.Program) (context : Context) :
    World → Address → Term → Identity → Bool → List (Local × Address × Authority) → World → Prop where
  | result {before destination type pattern positive observations carrier dataArguments copied bindings loans packed pack fields assembled after} :
      program.declarations.input.manifest.testCarrier = some carrier → type = .nominal carrier.declaration dataArguments →
      CopiesObservations program context before observations bindings loans copied →
      PacksBindings program context copied pattern positive bindings loans pack packed →
      CarrierFields program context packed (if positive then carrier.positive else carrier.negative) dataArguments pack
        (if positive then carrier.positiveBindings else carrier.negativeBindings) fields assembled →
      NewValue program.declarations assembled destination type
        (.constructor (if positive then carrier.positive else carrier.negative)) fields after →
      TestResult program context before destination type pattern positive observations after

inductive ControlStep (program : Kernel.Program) : State → Option Event → State → Prop where
  | labelCall {before context call tail receiver authority value brand argument permission} : before.task = .apply context call tail →
      ResolvesPlace before.world context.environment call.callee receiver authority → before.world.Stores receiver value →
      value.head = .label brand → Permitted before.world authority .shared receiver →
      (∃ place, call.arguments = [place] ∧ ResolvesPlace before.world context.environment place argument permission) →
      ControlStep program before (some (.leave brand)) { before with task := .leave context brand argument }
  | leave {before context brand argument inner outerContext region type outer kept after roots} :
      before.task = .leave context brand argument → LabelRoute before.frames brand inner outerContext region type outer →
      Protect program outerContext before.world argument .owner kept after →
      AbandonedRoots after inner [kept.root] roots → Cancelable program.declarations after roots →
      ControlStep program before none { before with world := after, frames := outer, task := .cleanup context roots (CloseRegions (inner.flatMap Frame.ownedRegions) (.yield outerContext kept)) }
  | reserve {before context lexical bound localSlot brand places next addresses allocated destination after layout} :
      before.task = .run context (.reserve lexical brand places next) →
      bound = context.bindBrand brand (.proof before.world.nextProof) → localSlot = bound.local lexical →
      Addresses before.world context.environment places addresses →
      addresses.Nodup → (∀ a ∈ addresses, ∀ b ∈ addresses, a ≠ b → ¬ a.Overlaps b) →
      (∀ id available, before.world.availability.get id = some available → available.active = true →
        ∀ a ∈ available.reserved, ∀ b ∈ addresses, ¬ a.Overlaps b) →
      localSlot.type = .available (.runtimeBrand (.proof before.world.nextProof)) (.runtimeRegion context.region) →
      Allocates program.declarations before.world (.localSlot context.activation context.scope) context.region localSlot.type layout
        localSlot.mutable destination allocated →
      NewValue program.declarations allocated destination localSlot.type (.available before.world.nextProof) [] after →
      ControlStep program before none { before with world := { after with nextProof := before.world.nextProof+1, availability := after.availability.set before.world.nextProof ⟨before.world.nextProof,.runtimeBrand (.proof before.world.nextProof),context.region,addresses,true⟩ }, task := .run (bound.bind localSlot destination) next }
  | available {before context destination id next source authority after} :
      before.task = .atom context destination (.available id) next →
      (∃ binding ∈ context.environment, binding.address = source ∧ binding.authority = authority ∧
        ∃ value, before.world.Stores source value ∧ value.head = .available id) →
      Transfers before.world authority source destination after →
      ControlStep program before (some (.move source destination)) { before with world := after, task := .run context next }
  | closeAvailable {before context place next address authority value id available cleared} :
      before.task = .run context (.closeAvailable place next) → ResolvesPlace before.world context.environment place address authority →
      before.world.Stores address value → value.head = .available id → before.world.availability.get id = some available →
      ReservationCanClose program before.world available → Permitted before.world authority .owned address →
      before.world.write address none = some cleared →
      ControlStep program before none { before with world := { cleared with availability := cleared.availability.set id { available with active := false } }, task := Disposes context available.reserved.reverse (.run context next) }
  | destroyAvailable {before context address authority next value id available cleared} :
      before.task = .destroy context address authority next → before.world.Stores address value → value.head = .available id →
      before.world.availability.get id = some available → ReservationCanClose program before.world available →
      Permitted before.world authority .owned address → before.world.write address none = some cleared →
      ControlStep program before none { before with world := { cleared with availability := cleared.availability.set id { available with active := false } }, task := Disposes context available.reserved.reverse next }
  | destroySpentAvailable {before context address authority next value id available cleared} :
      before.task = .destroy context address authority next → before.world.Stores address value → value.head = .available id →
      before.world.availability.get id = some available → available.active = false →
      Permitted before.world authority .owned address → before.world.write address none = some cleared →
      ControlStep program before none { before with world := cleared, task := next }
  | contextualCall {before context call tail receiver authority id arguments function token available captures inputs after value} :
      before.task = .apply context call tail → call.environment = some token →
      ResolvesPlace before.world context.environment call.callee receiver authority → before.world.Stores receiver value →
      value.head = .callable id arguments → value.fields = [] → Instance program id arguments function →
      before.world.availability.get token = some available → available.active = true → available.region ∈ before.world.liveRegions →
      captures = (function.captures.zip available.reserved).zipIdx.map
        (fun (entry,index) => ⟨.capture index,entry.1,entry.2,.owner,call.receiver⟩) →
      function.captures.length = available.reserved.length → ArgumentInputs before.world context 0 function.parameters call.arguments inputs →
      after = { before.world with availability := before.world.availability.set token { available with active := if call.receiver = .owned then false else true } } →
      ControlStep program before (some (.call id (captures ++ inputs)))
        { before with world := after, task := .enter context function (captures ++ inputs) tail }
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
  | bindings {before context destination id next source authority after} : before.task = .atom context destination (.bindings id) next →
      (∃ binding ∈ context.environment, binding.address = source ∧ binding.authority = authority ∧
        ∃ value, before.world.Stores source value ∧ value.head = .bindings id) →
      Transfers before.world authority source destination after →
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

end Glorious.Language.Execution
