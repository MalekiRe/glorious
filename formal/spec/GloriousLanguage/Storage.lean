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

structure PatternFact where
  resultOrigin : Identity
  pattern : Identity
  positive : Bool
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Sealed metadata travels with the resident binding fields. Field identities
are relative positions, never addresses of a previous carrier. Copy preserves
the context brand, just as copying any other branded value preserves its type. -/
structure BindingPack where
  brand : Identity
  region : Identity
  fields : List Identity
  facts : List PatternFact
  deriving DecidableEq, BEq, Repr, Inhabited

def BindingPack.mapOrigins (map : Identity → Identity) (pack : BindingPack) : BindingPack :=
  { pack with facts := pack.facts.map (fun fact => { fact with resultOrigin := map fact.resultOrigin }) }

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
  | bindings (pack : BindingPack)
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

mutual
  def Value.mapBindingOrigins (map : Identity → Identity) : Value → Value
    | .resident owner type head live fields => .resident owner type
        (match head with | .bindings pack => .bindings (pack.mapOrigins map) | head => head)
        live (Value.mapFieldOrigins map fields)

  def Value.mapFieldOrigins (map : Identity → Identity) : List (Option Value) → List (Option Value)
    | [] => []
    | none :: rest => none :: Value.mapFieldOrigins map rest
    | some value :: rest => some (value.mapBindingOrigins map) :: Value.mapFieldOrigins map rest
end

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
  /-- A lent shared place retains its backing authority, but never its
  permission to mutate or consume. This is an access view, not a new owner
  or a source reference loan. -/
  | shared (backing : Authority)
  deriving DecidableEq, BEq, Repr, Inhabited

def Authority.lend (authority : Authority) (access : Access) : Authority :=
  if access = .shared then .shared authority else authority

def Authority.parentLoan : Authority → Option Identity
  | .owner => none
  | .loan id => some id
  | .shared backing => backing.parentLoan

/-- A resolved storage location always travels with its access authority.
An address alone is not permission to consume the resident. -/
structure ResolvedPlace where
  address : Address
  authority : Authority
  deriving Repr, Inhabited

structure Availability where
  identity : Identity
  brand : Term
  region : Identity
  reserved : List ResolvedPlace
  active : Bool
  deriving Repr, Inhabited

structure World where
  roots : Table Root := []
  loans : Table Loan := []
  availability : Table Availability := []
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
         address.Overlaps loan.referent → Conflict requested loan.mode → AncestorLoan world other id
   | .shared backing => requested = .shared ∧ Permitted world backing requested address)

/-- Loading a unique handle through a shared place does not recover unique
referent access. All dereference consumers use this same view selection. -/
def ReferenceView (world : World) (handle : Address) (authority : Authority)
    (id : Identity) (mode : Mutability) (permission : Authority) (access : Access) : Prop :=
  (mode = .shared ∧ permission = .loan id ∧ access = .shared) ∨
  (mode = .unique ∧ Permitted world authority .unique handle ∧ permission = .loan id ∧ access = .unique) ∨
  (mode = .unique ∧ ¬ Permitted world authority .unique handle ∧ permission = .shared (.loan id) ∧ access = .shared)

theorem shared_authority_cannot_strengthen {world backing requested address}
    (permission : Permitted world (.shared backing) requested address) : requested = .shared :=
  permission.2.1

theorem reference_view_shared_carrier {world handle backing id mode permission access}
    (view : ReferenceView world handle (.shared backing) id mode permission access) : access = .shared := by
  rcases view with ⟨_,_,shared⟩ | ⟨_,writable,_,_⟩ | ⟨_,_,_,shared⟩
  · exact shared
  · cases shared_authority_cannot_strengthen writable
  · exact shared

def World.WellFormed (world : World) : Prop :=
  world.roots.Unique ∧ world.loans.Unique ∧ world.availability.Unique ∧
  world.liveRegions.Nodup ∧
  (∀ id available, world.availability.get id = some available →
    id = available.identity ∧ id < world.nextProof ∧ available.brand = .runtimeBrand (.proof id) ∧
    (available.active = true → available.region ∈ world.liveRegions ∧
      ∀ place ∈ available.reserved, (world.root place.address).isSome = true)) ∧
  (∀ address value pack, world.Resident address value → value.head = .bindings pack →
    pack.brand < world.nextProof ∧ pack.region ∈ world.liveRegions ∧
    pack.fields.length = value.fields.length ∧ pack.fields.Nodup ∧
    ∀ fact ∈ pack.facts, fact.resultOrigin < world.nextOwner) ∧
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
    world.availability.get world.nextProof = none ∧
    ∀ address value pack, world.Resident address value → value.head = .bindings pack → pack.brand ≠ world.nextProof := by
  rcases valid with ⟨_,_,_,_,availableBounds,packBounds,_⟩
  constructor
  · cases found : world.availability.get world.nextProof with
    | none => rfl
    | some available =>
      have impossible := (availableBounds world.nextProof available found).2.1
      exact False.elim (Nat.lt_irrefl world.nextProof impossible)
  · intro address value pack resident head equal
    have bound := (packBounds address value pack resident head).1
    rw [equal] at bound
    exact Nat.lt_irrefl world.nextProof bound

mutual
  inductive CopyTree (program : Program) : Nat → Value → Nat → Value → Table Identity → Prop where
    | resident {next owner type head fields copied finish origins} : PrincipalOf program type .duplicable →
        CopyFields program (next+1) fields finish copied origins →
        CopyTree program next (.resident owner type head true fields) finish (.resident next type head true copied)
          ((owner,next) :: origins)

  inductive CopyFields (program : Program) : Nat → List (Option Value) → Nat → List (Option Value) → Table Identity → Prop where
    | nil {next} : CopyFields program next [] next [] []
    | cons {next middle finish value copied rest copies first later} : CopyTree program next value middle copied first →
        CopyFields program middle rest finish copies later →
        CopyFields program next (some value :: rest) finish (some copied :: copies) (first ++ later)
end

/-- The copy traversal produces the owner renaming used by sealed result
facts. A fact referring outside the copied subtree keeps its original origin;
copying a whole result updates the origin together with that result's owner. -/
inductive CopyValue (program : Program) : Nat → Value → Nat → Value → Prop where
  | copy {next value finish raw origins} : CopyTree program next value finish raw origins → origins.Unique →
      CopyValue program next value finish (raw.mapBindingOrigins (fun id => (origins.get id).getD id))

theorem Value.mapBindingOrigins_type (value : Value) (map : Identity → Identity) :
    (value.mapBindingOrigins map).type = value.type := by cases value; rfl

theorem CopyValue.type_eq {program : Program} {next value finish copied}
    (copy : CopyValue program next value finish copied) : copied.type = value.type := by
  cases copy with
  | copy tree _ => cases tree; rfl

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

inductive NewValue (program : Program) : World → Address → Term → ValueHead → List ResolvedPlace → World → Prop where
  | construct {before destination type head sources residents taken after} : before.Vacant destination →
      ListRel (fun source value => before.Stores source.address value) sources residents →
      (∀ resident ∈ residents, resident.Initialized) →
      sources.Pairwise (fun left right => ¬ left.address.Overlaps right.address) →
      (∀ source ∈ sources, Permitted before source.authority .owned source.address ∧ ¬ source.address.Overlaps destination) →
      Clears before (sources.map ResolvedPlace.address) taken →
      taken.write destination (some (.resident before.nextOwner type head true (residents.map some))) = some after →
      NewValue program before destination type head sources { after with nextOwner := before.nextOwner+1 }

inductive Transfers : World → Authority → Address → Address → World → Prop where
  | move {before authority source destination value cleared after} :
      before.Stores source value → value.Initialized → Permitted before authority .owned source →
      before.Vacant destination → ¬ source.Overlaps destination →
      before.write source none = some cleared → cleared.write destination (some value) = some after →
      Transfers before authority source destination after

theorem Transfers.permission {before authority source destination after}
    (transfer : Transfers before authority source destination after) :
    Permitted before authority .owned source := by cases transfer; assumption

theorem NewValue.inputPermission {program before destination type head sources after}
    (constructed : NewValue program before destination type head sources after)
    {source : ResolvedPlace} (member : source ∈ sources) :
    Permitted before source.authority .owned source.address := by
  cases constructed with
  | construct _ _ _ _ permissions _ _ => exact (permissions source member).1

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
      parent = authority.parentLoan →
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
