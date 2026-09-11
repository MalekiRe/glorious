import GloriousLanguage.Static

/-! One initialized-storage model for locals, captures, temporaries and raw
allocations. Every executable value lives in this world; control frames carry
addresses, not a second collection of invisible owning values. -/
namespace Glorious.Language

structure Address where
  root : Identity
  generation : Nat
  fields : List Nat := []
  deriving DecidableEq, BEq, Repr, Inhabited

def Address.child (address : Address) (field : Nat) : Address :=
  { address with fields := address.fields ++ [field] }

def Address.Overlaps (a b : Address) : Prop :=
  a.root = b.root ∧ a.generation = b.generation ∧
    ((∃ suffix, a.fields = b.fields ++ suffix) ∨ ∃ suffix, b.fields = a.fields ++ suffix)

structure RawPointer where
  address : Nat
  allocation : Option Identity
  generation : Nat
  offset : Nat
  domain : Option Identity
  deriving DecidableEq, BEq, Repr, Inhabited

inductive ValueHead where
  | unit
  | scalar (value : ScalarValue)
  | tuple | array
  | constructor (variant : DeclId)
  | reference (loan : Identity)
  | pointer (value : RawPointer)
  | callable (declaration : DeclId) (arguments : List Term)
  | operation (declaration : DeclId) (arguments : List Term)
  | label (brand : Identity)
  | continuation (identity : Identity)
  | available (identity : Identity)
  | bindings (identity : Identity)
  deriving Repr, Inhabited

inductive Value where
  | resident (owner : Identity) (type : Term) (head : ValueHead)
      (shellLive : Bool) (fields : List (Option Value))
  deriving Repr, Inhabited

def Value.owner : Value → Identity | .resident owner _ _ _ _ => owner
def Value.type : Value → Term | .resident _ type _ _ _ => type
def Value.head : Value → ValueHead | .resident _ _ head _ _ => head
def Value.shellLive : Value → Bool | .resident _ _ _ live _ => live
def Value.fields : Value → List (Option Value) | .resident _ _ _ _ fields => fields

def Value.withFields (value : Value) (fields : List (Option Value)) : Value :=
  .resident value.owner value.type value.head value.shellLive fields

def Value.atPath : Value → List Nat → Option Value
  | value, [] => some value
  | value, field :: rest => (value.fields[field]?).join >>= fun child => child.atPath rest

def Value.replace : Value → List Nat → Option Value → Option Value
  | _, [], value => value
  | parent, field :: rest, value => do
    let slot ← parent.fields[field]?
    if rest.isEmpty then some (parent.withFields (parent.fields.set field value)) else do
      let child ← slot
      let changed ← child.replace rest value
      some (parent.withFields (parent.fields.set field (some changed)))

inductive ResidentAt : Value → List Nat → Value → Prop where
  | root {value} : ResidentAt value [] value
  | field {value index child path resident} : value.fields[index]? = some (some child) →
      ResidentAt child path resident → ResidentAt value (index :: path) resident

def Value.Initialized (value : Value) : Prop :=
  ∀ path resident, ResidentAt value path resident → resident.shellLive = true ∧
    ∀ field ∈ resident.fields, field.isSome = true

inductive Home where
  | localSlot (activation scope : Identity)
  | temporary (activation scope : Identity)
  | capture (owner : Identity)
  | suspended (continuation : Identity)
  | allocation (domain : Identity)
  | staticData (segment : Identity)
  | external (domain : Identity)
  deriving DecidableEq, BEq, Repr, Inhabited

structure Root where
  home : Home
  generation : Nat
  region : Identity
  base : Nat
  layout : Layout
  type : Term
  value : Option Value
  mutable : Bool
  born : Nat
  live : Bool
  bytes : List (Option Nat) := []
  deriving Repr, Inhabited

structure Loan where
  identity : Identity
  parent : Option Identity
  referent : Address
  mode : Mutability
  region : Identity
  live : Bool
  deriving Repr, Inhabited

inductive Authority where
  | owner | loan (identity : Identity)
  deriving DecidableEq, BEq, Repr, Inhabited

structure ReservedPlace where
  address : Address
  authority : Authority
  deriving Repr, Inhabited

structure Availability where
  identity : Identity
  brand : Term
  region : Identity
  reserved : List ReservedPlace
  active : Bool
  deriving Repr, Inhabited

structure BindingPack where
  identity : Identity
  pattern : Identity
  resultOrigin : Identity
  positive : Bool
  region : Identity
  fields : List (Identity × Address)
  protectingLoans : List Identity
  deriving Repr, Inhabited

structure World where
  roots : Table Root := []
  loans : Table Loan := []
  availability : Table Availability := []
  bindings : Table BindingPack := []
  liveRegions : List Identity := []
  nextRoot : Identity := 0
  nextOwner : Identity := 0
  nextLoan : Identity := 0
  nextRegion : Identity := 0
  nextProof : Identity := 0
  clock : Nat := 0
  deriving Repr, Inhabited

def World.root (world : World) (address : Address) : Option Root := do
  let root ← world.roots.get address.root
  if root.live && root.generation == address.generation then some root else none

def World.read (world : World) (address : Address) : Option Value := do
  let root ← world.root address
  let value ← root.value
  value.atPath address.fields

def World.write (world : World) (address : Address) (value : Option Value) : Option World := do
  let root ← world.root address
  if address.fields.isEmpty then
    some { world with roots := world.roots.set address.root { root with value := value } }
  else do
    let resident ← root.value
    let changed ← resident.replace address.fields value
    some { world with roots := world.roots.set address.root { root with value := some changed } }

def World.Stores (world : World) (address : Address) (value : Value) : Prop := world.read address = some value
def World.Initialized (world : World) (address : Address) : Prop := ∃ value, world.Stores address value ∧ value.Initialized

def World.Vacant (world : World) (address : Address) : Prop :=
  ∃ root, world.root address = some root ∧
    (address.fields = [] ∧ root.value = none ∨
     ∃ parent index value, address.fields = parent ++ [index] ∧ root.value = some value ∧
       ∃ container, value.atPath parent = some container ∧ container.fields[index]? = some none)

def World.Resident (world : World) (address : Address) (value : Value) : Prop :=
  ∃ root whole, world.roots.get address.root = some root ∧ root.live = true ∧
    address.generation = root.generation ∧ root.value = some whole ∧ ResidentAt whole address.fields value

def World.References (world : World) (identity : Identity) : Prop :=
  ∃ address value, world.Resident address value ∧ value.head = .reference identity

inductive AncestorLoan (world : World) : Identity → Identity → Prop where
  | refl {identity} : AncestorLoan world identity identity
  | parent {ancestor parent child loan} : world.loans.get child = some loan → loan.parent = some parent →
      AncestorLoan world ancestor parent → AncestorLoan world ancestor child

def Conflict (requested : Access) (existing : Mutability) : Prop :=
  requested ≠ .shared ∨ existing = .unique

def Permitted (world : World) (authority : Authority) (requested : Access) (address : Address) : Prop :=
  (∃ root, world.root address = some root) ∧
  (match authority with
   | .owner => ∀ id loan, world.loans.get id = some loan → loan.live = true →
       address.Overlaps loan.referent → ¬ Conflict requested loan.mode
   | .loan id => ∃ active, world.loans.get id = some active ∧ active.live = true ∧
       active.referent.root = address.root ∧ active.referent.generation = address.generation ∧
       (∃ suffix, address.fields = active.referent.fields ++ suffix) ∧
       (requested ≠ .shared → active.mode = .unique) ∧
       ∀ other loan, world.loans.get other = some loan → loan.live = true → other ≠ id →
         address.Overlaps loan.referent → Conflict requested loan.mode → AncestorLoan world other id)

def World.WellFormed (world : World) : Prop :=
  world.roots.Unique ∧ world.loans.Unique ∧ world.availability.Unique ∧ world.bindings.Unique ∧
  world.liveRegions.Nodup ∧
  (∀ id available, world.availability.get id = some available →
    id = available.identity ∧ id < world.nextProof ∧ available.brand = .runtimeBrand (.proof id) ∧
    (available.active = true → available.region ∈ world.liveRegions ∧
      ∀ place ∈ available.reserved, (world.root place.address).isSome = true)) ∧
  (∀ id pack, world.bindings.get id = some pack → id = pack.identity ∧ id < world.nextProof) ∧
  (∀ address value, world.Resident address value → value.owner < world.nextOwner) ∧
  (∀ a b x y, world.Resident a x → world.Resident b y → x.owner = y.owner → a = b) ∧
  (∀ id root, world.roots.get id = some root → id < world.nextRoot ∧
    (root.live = true → root.region ∈ world.liveRegions) ∧ root.layout.Valid ∧
    root.bytes.length = root.layout.size ∧ ∀ byte ∈ root.bytes, ∀ n, byte = some n → n < 256) ∧
  (∀ region ∈ world.liveRegions, region < world.nextRegion) ∧
  (∀ id root, world.roots.get id = some root → root.live = true →
    0 < root.base ∧ root.base % root.layout.alignment = 0) ∧
  (∀ a b left right, world.roots.get a = some left → world.roots.get b = some right →
    a ≠ b → left.live = true → right.live = true →
    left.layout.size = 0 ∨ right.layout.size = 0 ∨
      left.base+left.layout.size ≤ right.base ∨ right.base+right.layout.size ≤ left.base) ∧
  (∀ id loan, world.loans.get id = some loan → id = loan.identity ∧ id < world.nextLoan ∧
    (loan.live = true → loan.region ∈ world.liveRegions ∧ (world.root loan.referent).isSome = true)) ∧
  (∀ address value id, world.Resident address value → value.head = .reference id →
    ∃ loan, world.loans.get id = some loan ∧ loan.live = true) ∧
  (∀ a b left right, world.loans.get a = some left → world.loans.get b = some right →
    left.live = true → right.live = true → left.referent.Overlaps right.referent →
    left.mode = .unique ∨ right.mode = .unique → AncestorLoan world a b ∨ AncestorLoan world b a)

theorem World.freshProof {world : World} (valid : world.WellFormed) :
    world.availability.get world.nextProof = none ∧ world.bindings.get world.nextProof = none := by
  rcases valid with ⟨_,_,_,_,_,availableBounds,packBounds,_⟩
  constructor
  · cases found : world.availability.get world.nextProof with
    | none => rfl
    | some available =>
      have impossible := (availableBounds world.nextProof available found).2.1
      exact False.elim (Nat.lt_irrefl world.nextProof impossible)
  · cases found : world.bindings.get world.nextProof with
    | none => rfl
    | some pack =>
      have impossible := (packBounds world.nextProof pack found).2
      exact False.elim (Nat.lt_irrefl world.nextProof impossible)

mutual
  inductive CopyValue (program : Program) : Nat → Value → Nat → Value → Prop where
    | resident {next owner type head fields copied finish} : PrincipalOf program type .duplicable →
        CopyFields program (next+1) fields finish copied →
        CopyValue program next (.resident owner type head true fields) finish (.resident next type head true copied)

  inductive CopyFields (program : Program) : Nat → List (Option Value) → Nat → List (Option Value) → Prop where
    | nil {next} : CopyFields program next [] next []
    | cons {next middle finish value copied rest copies} : CopyValue program next value middle copied →
        CopyFields program middle rest finish copies → CopyFields program next (some value :: rest) finish (some copied :: copies)
end

def DisjointStorage (world : World) (base size : Nat) : Prop :=
  ∀ id root, world.roots.get id = some root → root.live = true →
    size = 0 ∨ root.layout.size = 0 ∨ base+size ≤ root.base ∨ root.base+root.layout.size ≤ base

/-- Allocation introduces a storage home at a fresh, aligned physical extent,
never an initialized owner. Zero-sized homes retain separate logical identity. -/
inductive Allocates (program : Program) : World → Home → Identity → Term → Layout → Bool → Address → World → Prop where
  | fresh {before home region type layout mutable base} : region ∈ before.liveRegions → layout.Valid →
      layout.size ≤ program.input.target.maximumObjectBytes →
      (∃ context, LayoutOf program context type layout) →
      0 < base → base % layout.alignment = 0 → base + layout.size < 2^program.input.target.pointerBits →
      DisjointStorage before base layout.size →
      Allocates program before home region type layout mutable ⟨before.nextRoot,0,[]⟩
        { before with
          roots := before.roots.set before.nextRoot
            ⟨home,0,region,base,layout,type,none,mutable,before.clock,true,List.replicate layout.size none⟩
          nextRoot := before.nextRoot+1
          clock := before.clock+1 }

inductive Clears : World → List Address → World → Prop where
  | nil {world} : Clears world [] world
  | cons {before address rest middle after} : before.write address none = some middle →
      Clears middle rest after → Clears before (address :: rest) after

inductive NewValue (program : Program) : World → Address → Term → ValueHead → List Address → World → Prop where
  | construct {before destination type head sources residents taken after} : before.Vacant destination →
      ListRel (World.Stores before) sources residents →
      (∀ resident ∈ residents, resident.Initialized) →
      (sources.map (fun address => (address.root,address.fields))).Nodup →
      (∀ source ∈ sources, Permitted before .owner .owned source ∧ source ≠ destination) →
      Clears before sources taken →
      taken.write destination (some (.resident before.nextOwner type head true (residents.map some))) = some after →
      NewValue program before destination type head sources { after with nextOwner := before.nextOwner+1 }

inductive Transfers : World → Authority → Address → Address → World → Prop where
  | move {before authority source destination value cleared after} :
      before.Stores source value → value.Initialized → Permitted before authority .owned source →
      before.Vacant destination → ¬ source.Overlaps destination →
      before.write source none = some cleared → cleared.write destination (some value) = some after →
      Transfers before authority source destination after

inductive Copies (program : Program) : World → Authority → Address → Address → World → Prop where
  | copy {before authority source destination value cloned next after} :
      before.Stores source value → value.Initialized → Permitted before authority .shared source →
      before.Vacant destination → CopyValue program before.nextOwner value next cloned →
      before.write destination (some cloned) = some after →
      Copies program before authority source destination { after with nextOwner := next }

inductive Acquires (program : Program) : World → Authority → Bool → Address → Address → World → Prop where
  | explicitMove {before authority source destination after} : Transfers before authority source destination after →
      Acquires program before authority true source destination after
  | copy {before authority source destination after} : Copies program before authority source destination after →
      Acquires program before authority false source destination after
  | move {before authority source destination after value principal} : before.Stores source value →
      PrincipalOf program value.type principal → principal ≠ .duplicable → Transfers before authority source destination after →
      Acquires program before authority false source destination after

inductive Borrows (program : Program) :
    World → Authority → Mutability → Identity → Address → Address → World → Prop where
  | borrow {before authority mode region referent destination value after parent} :
      before.Stores referent value →
      (mode = .shared → value.Initialized) → region ∈ before.liveRegions →
      Addressable program ⟨[],[],0,default,false⟩ value.type →
      Permitted before authority (if mode = .shared then .shared else .unique) referent →
      before.Vacant destination →
      parent = (match authority with | .owner => none | .loan id => some id) →
      before.write destination (some (.resident before.nextOwner
        (.reference mode (.runtimeRegion region) value.type) (.reference before.nextLoan) true [])) = some after →
      Borrows program before authority mode region referent destination
        { after with
          loans := before.loans.set before.nextLoan ⟨before.nextLoan,parent,referent,mode,region,true⟩
          nextOwner := before.nextOwner+1
          nextLoan := before.nextLoan+1 }

inductive EndsLoan : World → Identity → World → Prop where
  | restored {before id loan} : before.loans.get id = some loan → loan.live = true →
      before.Initialized loan.referent → ¬ before.References id →
      (∀ child, before.loans.get child.identity = some child → child.parent = some id → child.live = false) →
      EndsLoan before id { before with loans := before.loans.set id { loan with live := false } }

inductive Deconstructs (program : Program) (context : Context) : World → Authority → Address → World → Prop where
  | shell {before authority address value after} : before.Stores address value → value.shellLive = true →
      Permitted before authority .owned address →
      (value.head = .tuple ∨ value.head = .array ∨
        ∃ id data variant args, program.Constructor id data variant ∧ value.type = .nominal data.header.id args ∧
          value.head = .constructor id ∧ data.dropHook = none ∧
          (data.nonExhaustive = true → context.module.package = data.header.module.package) ∧
          ∀ field ∈ variant.fields, Visible field.header context.module) →
      before.write address (some (.resident value.owner value.type value.head false value.fields)) = some after →
      Deconstructs program context before authority address after

def DropHook (program : Program) (type : Term) (hook : Option DeclId) : Prop :=
  (∃ id args data, type = .nominal id args ∧ program.data id = some data ∧ data.dropHook = hook) ∨
  ((∀ id args, type ≠ .nominal id args) ∧ hook = none)

def MayDispose (program : Program) (value : Value) : Prop :=
  ∀ path resident, ResidentAt value path resident →
    (resident.shellLive = true → ∃ principal, PrincipalOf program resident.type principal ∧ principal.MayDiscard) ∧
    (∀ hook, DropHook program resident.type (some hook) → resident.Initialized)

def CanEndStorage (world : World) (rootId : Identity) : Prop :=
  ∀ id loan, world.loans.get id = some loan → loan.live = true → loan.referent.root ≠ rootId

inductive Retires : World → Identity → World → Prop where
  | vacant {before id root} : before.roots.get id = some root → root.live = true → root.value = none →
      CanEndStorage before id →
      Retires before id { before with roots := before.roots.set id { root with live := false, generation := root.generation+1 } }

def RawRange (program : Program) (world : World) (pointer : RawPointer) (length alignment : Nat) : Prop :=
  ∃ id root domain,
    pointer.allocation = some id ∧ world.roots.get id = some root ∧ root.live = true ∧
    root.generation = pointer.generation ∧ pointer.domain = some domain ∧
    (root.home = .allocation domain ∨ root.home = .external domain) ∧
    pointer.address = root.base + pointer.offset ∧ pointer.offset + length ≤ root.layout.size ∧
    0 < alignment ∧ pointer.address % alignment = 0 ∧
    pointer.address + length < 2^program.input.target.pointerBits

def FreshRegion (before : World) (region : Identity) (after : World) : Prop :=
  region = before.nextRegion ∧ after = { before with
    liveRegions := region :: before.liveRegions, nextRegion := region+1 }

def Suspensible (world : World) (roots : List Identity) : Prop :=
  ∀ id loan, world.loans.get id = some loan → loan.live = true →
    (loan.referent.root ∈ roots ∨ ∃ address value, address.root ∈ roots ∧ world.Resident address value ∧ value.head = .reference id) →
    world.Initialized loan.referent

def Cancelable (program : Program) (world : World) (roots : List Identity) : Prop :=
  Suspensible world roots ∧ ∀ address value, address.root ∈ roots → world.Resident address value → MayDispose program value

def Replayable (program : Program) (world : World) (roots : List Identity) : Prop :=
  Suspensible world roots ∧
  (∀ address value, address.root ∈ roots → world.Resident address value →
    (value.shellLive = true → PrincipalOf program value.type .duplicable) ∧
    (∀ brand, value.head ≠ .label brand) ∧ (∀ id, value.head ≠ .available id)) ∧
  (∀ address value id loan, address.root ∈ roots → world.Resident address value → value.head = .reference id →
    world.loans.get id = some loan → loan.mode = .shared) ∧
  (∀ id loan, world.loans.get id = some loan → loan.live = true → loan.referent.root ∈ roots → loan.mode = .shared)

theorem hole_cannot_end {before after : World} {id loan}
    (found : before.loans.get id = some loan) (hole : ¬ before.Initialized loan.referent) : ¬ EndsLoan before id after := by
  intro ended
  cases ended with
  | restored selected _ initialized _ _ =>
    have same : loan = _ := Option.some.inj (found.symm.trans selected)
    subst same
    exact hole initialized

theorem move_preserves_owner {before after : World} {authority source destination value}
    (found : before.Stores source value) (moved : Transfers before authority source destination after) :
    ∃ cleared, before.write source none = some cleared ∧ cleared.write destination (some value) = some after := by
  cases moved with
  | move selected _ _ _ _ clear install =>
    have same := Option.some.inj (found.symm.trans selected)
    subst same
    exact ⟨_,clear,install⟩

end Glorious.Language
