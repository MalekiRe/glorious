import Glorious.Semantics.Storage
import Glorious.Proof.Static

namespace Glorious.Semantics.Spec

inductive ResidentAt : Value → List Nat → Value → Prop where
  | root {value} : ResidentAt value [] value
  | field {parent child result index path}
      (present : parent.fields[index]? = some (some child))
      (nested : ResidentAt child path result) : ResidentAt parent (index :: path) result

def Stored (world : World) (address : Address) (value : Value) : Prop :=
  ∃ slot root, slot ∈ world.slots ∧ slot.declaration.id = address.slot ∧
    slot.value = some root ∧ ResidentAt root address.fields value

def Resident (world : World) (value : Value) : Prop :=
  (∃ address, Stored world address value) ∨
  ∃ allocation ∈ world.allocations, ∃ offset root path,
    (offset, root) ∈ allocation.residents ∧ ResidentAt root path value

def AddressOverlaps (a b : Address) : Prop :=
  a.slot = b.slot ∧ (a.fields.IsPrefix b.fields ∨ b.fields.IsPrefix a.fields)

inductive Ancestor (loans : List Loan) : Id → Id → Prop where
  | refl {identity} : Ancestor loans identity identity
  | parent {ancestor child loan}
      (declared : loan ∈ loans) (identity : loan.identity = child)
      (parent : loan.parent = some ancestor) : Ancestor loans ancestor child
  | trans {a b c} : Ancestor loans a b → Ancestor loans b c → Ancestor loans a c

def Mutates : Access → Prop
  | .read | .sharedBorrow => False
  | _ => True

structure AccessAllowed (world : World) (located : Located) (access : Access) : Prop where
  through : ∀ identity, located.throughLoan = some identity →
    ∃ loan ∈ world.loans, loan.identity = identity ∧ loan.live = true ∧
      (Mutates access → loan.mode = .unique) ∧ (loan.hole = true → access = .write)
  excludes : ∀ loan ∈ world.loans, loan.live = true → AddressOverlaps located.address loan.origin →
    (∃ identity, located.throughLoan = some identity ∧ Ancestor world.loans loan.identity identity) ∨
      (¬ Mutates access ∧ loan.mode = .shared)

def FullyInitialized (value : Value) : Prop :=
  ∀ path resident, ResidentAt value path resident → resident.shellConsumed = false ∧
    ∀ field ∈ resident.fields, field.isSome = true

def HandleValid (world : World) (value : Value) : Prop :=
  ∀ identity, value.head = .reference identity →
    ∃ loan ∈ world.loans, loan.identity = identity ∧ loan.live = true ∧ loan.hole = false

structure WorldWellFormed (world : World) : Prop where
  slotIdentities : (world.slots.map (·.declaration.id)).Nodup
  storageIdentities : (world.slots.map (·.storage)).Nodup
  loanIdentities : (world.loans.map (·.identity)).Nodup
  ownerUnique : ∀ a b x y, Stored world a x → Stored world b y → x.identity = y.identity → a = b
  ownersAllocated : ∀ value, Resident world value → value.identity < world.nextOwner
  loansAllocated : ∀ loan ∈ world.loans, loan.identity < world.nextLoan
  loanOrigins : ∀ loan ∈ world.loans, loan.live = true →
    loan.hole = true ∨ ∃ value, Stored world loan.origin value ∧ value.type = loan.referent
  parents : ∀ loan ∈ world.loans, loan.live = true → ∀ parent, loan.parent = some parent →
    ∃ ancestor ∈ world.loans, ancestor.identity = parent ∧ ancestor.live = true ∧
      AddressOverlaps ancestor.origin loan.origin
  handles : ∀ value, Resident world value → ∀ identity, value.head = .reference identity →
    ∃ loan ∈ world.loans, loan.identity = identity ∧ loan.live = true

inductive UpdatesField : Value → List Nat → Option Value → Value → Prop where
  | direct {parent index replacement old}
      (present : parent.fields[index]? = some old) :
      UpdatesField parent [index] replacement (parent.withFields (parent.fields.set index replacement))
  | nested {parent child changed index path replacement}
      (present : parent.fields[index]? = some (some child))
      (update : UpdatesField child path replacement changed) :
      UpdatesField parent (index :: path) replacement
        (parent.withFields (parent.fields.set index (some changed)))

inductive UpdatesAddress : World → Address → Option Value → World → Prop where
  | root {before slot replacement}
      (present : slot ∈ before.slots) :
      UpdatesAddress before ⟨slot.declaration.id, []⟩ replacement
        { before with slots := before.slots.map fun current =>
          if current.declaration.id == slot.declaration.id then { slot with value := replacement } else current }
  | field {before slot root updated path replacement}
      (present : slot ∈ before.slots) (initialized : slot.value = some root)
      (update : UpdatesField root path replacement updated) :
      UpdatesAddress before ⟨slot.declaration.id, path⟩ replacement
        { before with slots := before.slots.map fun current =>
          if current.declaration.id == slot.declaration.id then { slot with value := some updated } else current }

inductive FieldTypes (program : Program) : Term → ValueHead → List Term → Prop where
  | unit : FieldTypes program .unit .unit []
  | tuple {types} : FieldTypes program (.tuple types) (.constructor none) types
  | array {element width count} (length : 0 ≤ count) :
      FieldTypes program (.array element (.constant (.integer false width count))) (.constructor none)
        (List.replicate count.toNat element)
  | nominal {data variant arguments substitution types}
      (declared : data ∈ program.dataTypes) (member : variant ∈ data.variants)
      (instantiated : Instantiates data.generics arguments substitution)
      (fields : Glorious.Proof.Forall₂ (Substitutes substitution) (variant.fields.map (·.type)) types) :
      FieldTypes program (.nominal data.header.id arguments) (.constructor (some variant.header.id)) types

inductive Denotes (program : Program) (world : World) : Place → Located → Prop where
  | root {slot} (present : slot ∈ world.slots) :
      Denotes program world ⟨slot.declaration.id, []⟩ ⟨⟨slot.declaration.id, []⟩, slot.declaration.type, none⟩
  | field {place located value fields index type}
      (base : Denotes program world place located) (stored : Stored world located.address value)
      (shape : FieldTypes program located.type value.head fields) (selected : fields[index]? = some type) :
      Denotes program world { place with projections := place.projections ++ [.field index] }
        { located with address.fields := located.address.fields ++ [index], type }
  | index {place located value element width count index}
      (base : Denotes program world place located) (stored : Stored world located.address value)
      (shape : located.type = .array element (.constant (.integer false width count)))
      (bounds : 0 ≤ count ∧ index < count.toNat) :
      Denotes program world { place with projections := place.projections ++ [.index index] }
        { located with address.fields := located.address.fields ++ [index], type := element }
  | dynamicIndex {place : Place} {located identity index slot scalar}
      (base : Denotes program world { place with projections := place.projections ++ [.index index] } located)
      (present : slot ∈ world.slots) (id : slot.declaration.id = identity) (value : slot.value = some scalar)
      (integer : scalar.head = .scalar (.integer false .pointer (Int.ofNat index))) :
      Denotes program world { place with projections := place.projections ++ [.dynamicIndex identity] } located
  | variant {place located value declaration}
      (base : Denotes program world place located) (stored : Stored world located.address value)
      (selected : value.head = .constructor (some declaration)) :
      Denotes program world { place with projections := place.projections ++ [.variant declaration] } located
  | dereference {place located value loan}
      (base : Denotes program world place located) (stored : Stored world located.address value)
      (reference : value.head = .reference loan.identity) (present : loan ∈ world.loans)
      (live : loan.live = true) :
      Denotes program world { place with projections := place.projections ++ [.dereference] }
        ⟨loan.origin, loan.referent, some loan.identity⟩

def MayMoveField (world : World) (address : Address) : Prop :=
  ∀ ancestor value, ancestor.slot = address.slot → ancestor.fields.IsPrefix address.fields →
    ancestor.fields ≠ address.fields → Stored world ancestor value → value.dropHook = none

inductive Takes (program : Program) : World → Place → Value → World → Prop where
  | move {before after located source value}
      (place : Denotes program before source located) (stored : Stored before located.address value)
      (initialized : FullyInitialized value) (handle : HandleValid before value)
      (access : AccessAllowed before located .move) (field : MayMoveField before located.address)
      (removed : UpdatesAddress before located.address none after) :
      Takes program before source value
        { after with loans := after.loans.map fun loan =>
          if located.throughLoan == some loan.identity then { loan with hole := true } else loan }

inductive Initializes (program : Program) : World → Place → Value → World → Prop where
  | store {before intermediate located destination value}
      (place : Denotes program before destination located)
      (type : value.type = located.type)
      (vacant : ¬ ∃ old, Stored before located.address old)
      (access : AccessAllowed before located .write)
      (update : UpdatesAddress before located.address (some value) intermediate) :
      Initializes program before destination value
        { intermediate with loans := intermediate.loans.map fun loan =>
          if loan.live && loan.origin == located.address then { loan with hole := false } else loan }

mutual
  inductive Copies : Value → Id → Value → Id → Prop where
    | owned {source fields next stop}
        (permission : source.capability = .duplicable)
        (children : CopiesFields source.fields next fields stop) :
        Copies source next
          (.owned stop source.type .duplicable source.dropHook source.shellConsumed source.head fields) (stop + 1)
  inductive CopiesFields : List (Option Value) → Id → List (Option Value) → Id → Prop where
    | nil {next} : CopiesFields [] next [] next
    | vacant {rest next fields stop} (tail : CopiesFields rest next fields stop) :
        CopiesFields (none :: rest) next (none :: fields) stop
    | resident {source rest copied fields next middle stop}
        (head : Copies source next copied middle) (tail : CopiesFields rest middle fields stop) :
        CopiesFields (some source :: rest) next (some copied :: fields) stop
end

inductive Reads (program : Program) : World → Place → Bool → Value → World → Prop where
  | move {before after source value force}
      (selected : force = true ∨ value.capability ≠ .duplicable)
      (transition : Takes program before source value after) : Reads program before source force value after
  | copy {before source located value copied stop}
      (place : Denotes program before source located) (stored : Stored before located.address value)
      (initialized : FullyInitialized value) (handle : HandleValid before value)
      (access : AccessAllowed before located .read) (copy : Copies value before.nextOwner copied stop) :
      Reads program before source false copied { before with nextOwner := stop }

inductive Borrows (program : Program) : World → Place → Mutability → Term → Value → World → Prop where
  | create {before source located value mode region}
      (place : Denotes program before source located) (stored : Stored before located.address value)
      (initialized : FullyInitialized value)
      (access : AccessAllowed before located (if mode = .shared then .sharedBorrow else .uniqueBorrow)) :
      Borrows program before source mode region
        (.owned before.nextOwner (.reference mode region located.type)
          (if mode = .shared then .duplicable else .affine) none false (.reference before.nextLoan) [])
        { before with
          nextOwner := before.nextOwner + 1, nextLoan := before.nextLoan + 1,
          loans := before.loans ++ [⟨before.nextLoan, located.address, located.type, region, mode, located.throughLoan, true, false⟩] }

inductive EndsLoan : World → Id → World → Prop where
  | end_ {before loan} (present : loan ∈ before.loans) (live : loan.live = true)
      (restored : loan.hole = false)
      (noChildren : ∀ child ∈ before.loans, child.live = true → child.parent ≠ some loan.identity) :
      EndsLoan before loan.identity { before with loans := before.loans.map fun current =>
        if current.identity == loan.identity then { current with live := false } else current }

mutual
  inductive RepresentsResident (world : World) : StorageId → Value → Glorious.Resident → Prop where
    | hole {storage value identity loan}
        (reference : value.head = .reference identity) (present : loan ∈ world.loans)
        (same : loan.identity = identity) (live : loan.live = true) (hole : loan.hole = true) :
        RepresentsResident world storage value (.openLoan storage ⟨identity⟩)
    | owned {storage value fields}
        (notHole : ∀ identity loan, value.head = .reference identity → loan ∈ world.loans →
          loan.identity = identity → loan.live = true → loan.hole = false)
        (children : RepresentsFields world storage 0 value.fields fields) :
        RepresentsResident world storage value
          (.owned storage ⟨value.identity⟩ (if value.shellConsumed then .duplicable else value.capability) value.dropHook fields)
  inductive RepresentsFields (world : World) :
      StorageId → Nat → List (Option Value) → List Glorious.Resident → Prop where
    | nil {storage index} : RepresentsFields world storage index [] []
    | vacant {storage index values fields} (rest : RepresentsFields world storage (index + 1) values fields) :
        RepresentsFields world storage index (none :: values)
          (.vacant { storage with path := storage.path ++ [index] } :: fields)
    | resident {storage index value values field fields}
        (head : RepresentsResident world { storage with path := storage.path ++ [index] } value field)
        (rest : RepresentsFields world storage (index + 1) values fields) :
        RepresentsFields world storage index (some value :: values) (field :: fields)
end

inductive Disposes (program : Program) : World → Place → World → Prop where
  | destroy {before after place located value slot resident events}
      (location : Denotes program before place located) (stored : Stored before located.address value)
      (access : AccessAllowed before located .destroy)
      (declared : slot ∈ before.slots) (identity : slot.declaration.id = located.address.slot)
      (representation : RepresentsResident before
        { slot.storage with path := slot.storage.path ++ located.address.fields } value resident)
      (destruction : Destroys resident events)
      (removed : UpdatesAddress before located.address none after) :
      Disposes program before place { after with cleanup := before.cleanup ++ events }

structure ExitDisposition (before after : World) (ending : List Id) (payload : List Value)
    (boundary : CleanupBoundary) : Prop where
  payloadDetached : ∀ value ∈ payload, ∀ path resident, ResidentAt value path resident → ¬ Resident before resident
  restored : ∀ loan ∈ before.loans, loan.live = true → loan.origin.slot ∈ ending → loan.hole = false
  noEscape : ∀ loan ∈ before.loans, loan.live = true → loan.origin.slot ∈ ending →
    ∀ value, ((∃ root ∈ payload, ∃ path, ResidentAt root path value) ∨ Resident after value) →
      value.head ≠ .reference loan.identity
  owners : ∀ slot ∈ before.slots, slot.declaration.id ∈ ending → ∀ value, slot.value = some value →
    ∃ resident events, RepresentsResident before slot.storage value resident ∧ Destroys resident events
  remaining : after.slots = before.slots.filter (fun slot => !ending.contains slot.declaration.id)
  ended : ∀ loan ∈ after.loans, loan.origin.slot ∈ ending → loan.live = false
  ordered : ∃ residents events,
    Glorious.Proof.Forall₂ (fun slot resident =>
      match slot.value with
      | none => resident = .vacant slot.storage
      | some value => RepresentsResident before slot.storage value resident)
      (before.slots.filter (fun slot => ending.contains slot.declaration.id)) residents ∧
    DestroysFields residents events ∧ after.cleanup = before.cleanup ++ events

theorem move_preserves_logical_owner (proof : Takes program before place value after) :
    ∃ located, Denotes program before place located ∧ Stored before located.address value := by
  cases proof with
  | move place stored _ _ _ _ _ => exact ⟨_, place, stored⟩

theorem copy_requires_duplicable (proof : Copies source next copy stop) :
    source.capability = .duplicable := by cases proof; assumption

theorem ending_hole_impossible (proof : EndsLoan before identity after)
    (unique : (before.loans.map (·.identity)).Nodup)
    (loan : Loan) (present : loan ∈ before.loans) (same : loan.identity = identity)
    (hole : loan.hole = true) : False := by
  cases proof with
  | end_ declared live restored noChildren =>
    have equality := Glorious.Proof.eq_of_nodup_map unique present declared same
    subst loan
    simp_all

end Glorious.Semantics.Spec
