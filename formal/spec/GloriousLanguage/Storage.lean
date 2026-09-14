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

/-- Geometric relations on the existing storage path, with generation and
root identity retained. These are not new runtime identities. -/
def Address.Prefix (ancestor descendant : Address) : Prop :=
  ancestor.root = descendant.root ∧ ancestor.generation = descendant.generation ∧
    ∃ suffix, descendant.fields = ancestor.fields ++ suffix

def Address.ProperPrefix (ancestor descendant : Address) : Prop :=
  ancestor.Prefix descendant ∧ ancestor.fields.length < descendant.fields.length

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

inductive Authority where
  | owner | loan (identity : Identity)
  /-- A shared view never carries permission to mutate or consume its backing. -/
  | shared (backing : Authority)
  /-- Opening an owning invariant through a borrowed carrier retains that
  carrier's actual loan, independently of the pointee's containment parent. -/
  | guarded (backing : Authority) (carrier : Identity)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Named values and erased unsafe obligations inhabit one resource domain.
An obligation identity is not a source local or a raw-pointer representation. -/
inductive BindingKey where
  | localSlot (identity : Identity)
  | resourceInput (identity : Identity)
  | obligation (identity : Identity)
  deriving DecidableEq, BEq, Repr, Inhabited

instance : Coe Identity BindingKey := ⟨BindingKey.localSlot⟩

structure StorageBinding where
  key : BindingKey
  address : Address
  authority : Authority
  deriving Repr, Inhabited

def StorageBinding.ReadOnly (binding : StorageBinding) : Prop :=
  ∃ backing, binding.authority = .shared backing

def StorageBinding.Implicit (binding : StorageBinding) : Prop :=
  (∃ identity, binding.key = .obligation identity) ∨
    ∃ identity, binding.key = .resourceInput identity

/-- A resolved location includes authority; address provenance alone cannot
introduce this resource. -/
structure ResolvedPlace where
  address : Address
  authority : Authority
  deriving Repr, Inhabited

def StorageBinding.place (binding : StorageBinding) : ResolvedPlace :=
  ⟨binding.address,binding.authority⟩

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

/-- Erased ownership invariants belong to the actual resident, not its pointer
fields. Transfer moves this product; Copy can retain only shared views. Opening
and closing an invariant use the common input relation. -/
inductive Value where
  | resident (owner : Identity) (type : Term) (head : ValueHead)
      (shellLive : Bool) (fields : List (Option Value))
      (resources : List StorageBinding := [])
  deriving Repr, Inhabited

def Value.owner : Value → Identity | .resident owner _ _ _ _ _ => owner
def Value.type : Value → Term | .resident _ type _ _ _ _ => type
def Value.head : Value → ValueHead | .resident _ _ head _ _ _ => head
def Value.shellLive : Value → Bool | .resident _ _ _ live _ _ => live
def Value.fields : Value → List (Option Value) | .resident _ _ _ _ fields _ => fields
def Value.resources : Value → List StorageBinding | .resident _ _ _ _ _ resources => resources

def Value.withFields (value : Value) (fields : List (Option Value)) : Value :=
  .resident value.owner value.type value.head value.shellLive fields value.resources

def Value.withResources (value : Value) (resources : List StorageBinding) : Value :=
  .resident value.owner value.type value.head value.shellLive value.fields resources

mutual
  def Value.mapBindingOrigins (map : Identity → Identity) : Value → Value
    | .resident owner type head live fields resources => .resident owner type
        (match head with | .bindings pack => .bindings (pack.mapOrigins map) | head => head)
        live (Value.mapFieldOrigins map fields) resources

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

/-- All lifecycles use the same exclusion tree. A restoring borrow must finish
initialized. A storage borrow may return a typed hole, including after moving
T. An owning claim is the distinct exact allocation obligation; consuming T
alone does not transfer or discharge it. -/
inductive LoanKind where
  | restoring | destructor | storageBorrow | owning
  deriving DecidableEq, BEq, Repr, Inhabited

/-- The recipient of a resource handoff is an existing semantic identity.
Custody is attached to the claim node, not to a physical root or pointer.
Structural descendants can therefore have distinct recipients. -/
inductive ClaimCustody where
  | activation (identity : Identity)
  | resident (owner : Identity)
  | host (callDestination : Identity)
  | registration (identity : Identity)
  deriving DecidableEq, BEq, Repr, Inhabited

structure Loan where
  identity : Identity
  parent : Option Identity
  referent : Address
  mode : Mutability
  region : Identity
  live : Bool
  kind : LoanKind := .restoring
  guards : List Identity := []
  returnRequested : Bool := false
  custody : Option ClaimCustody := none
  deriving Repr, Inhabited

/-- Custody and a requested return change administration, not the loan's
exclusion geometry. Retention consumers compare this projection of the actual
record, never claim that a handed-off loan retains its old custodian. -/
def Loan.permissionState (loan : Loan) : Loan :=
  { loan with returnRequested := false, custody := none }

theorem Loan.permissionState_eq_iff {current original : Loan} :
    current.permissionState = original.permissionState ↔
      current.identity = original.identity ∧ current.parent = original.parent ∧
      current.referent = original.referent ∧ current.mode = original.mode ∧
      current.region = original.region ∧ current.live = original.live ∧
      current.kind = original.kind ∧ current.guards = original.guards := by
  simp only [Loan.permissionState,Loan.mk.injEq,and_true]

/-- Raw ownership is exclusive, and raw owning/borrowed obligations always
have an actual custodian. Ordinary source loans use their resident handles. -/
def LoanKind.Allows (kind : LoanKind) (mode : Mutability) (custody : Option ClaimCustody) : Prop :=
  (kind = .owning → mode = .unique) ∧
  (kind = .owning ∨ kind = .storageBorrow → custody.isSome = true)

def Loan.KindValid (loan : Loan) : Prop := loan.kind.Allows loan.mode loan.custody

def Authority.lend (authority : Authority) (access : Access) : Authority :=
  if access = .shared then .shared authority else authority

def Authority.parentLoan : Authority → Option Identity
  | .owner => none
  | .loan id => some id
  | .shared backing => backing.parentLoan
  | .guarded backing _ => backing.parentLoan

/-- Historical authority provenance, distinct from permission or liveness.
A saved authority can outlive its loan, but cannot name a loan not yet made. -/
def Authority.Recorded : Authority → Table Loan → Prop
  | .owner, _ => True
  | .loan id, loans => ∃ loan, loans.get id = some loan
  | .shared backing, loans => backing.Recorded loans
  | .guarded backing carrier, loans => backing.Recorded loans ∧ ∃ loan, loans.get carrier = some loan

theorem Authority.Recorded.transport {authority : Authority} {before after : Table Loan}
    (recorded : authority.Recorded before)
    (retained : ∀ id loan, before.get id = some loan → ∃ current, after.get id = some current) :
    authority.Recorded after := by
  induction authority with
  | owner => trivial
  | loan id => obtain ⟨loan,found⟩ := recorded; exact retained id loan found
  | shared backing ih => exact ih recorded
  | guarded backing carrier ih =>
      exact ⟨ih recorded.1,by obtain ⟨loan,found⟩ := recorded.2; exact retained carrier loan found⟩

theorem Authority.Recorded.parentLoan {authority : Authority} {loans : Table Loan} {id : Identity}
    (recorded : authority.Recorded loans) (parent : authority.parentLoan = some id) :
    ∃ loan, loans.get id = some loan := by
  induction authority with
  | owner => cases parent
  | loan identity => cases parent; exact recorded
  | shared backing ih => exact ih recorded parent
  | guarded backing carrier ih => exact ih recorded.1 parent

theorem Authority.Recorded.set {authority : Authority} {loans : Table Loan}
    (recorded : authority.Recorded loans) (id : Identity) (loan : Loan) :
    authority.Recorded (loans.set id loan) := by
  apply recorded.transport
  intro key original found
  by_cases same : key = id
  · subst key
    exact ⟨loan,Table.get_set _ _ _⟩
  · exact ⟨original,by simpa only [Table.get_set_other _ _ _ _ same] using found⟩

structure Availability where
  identity : Identity
  brand : Term
  region : Identity
  reserved : List ResolvedPlace
  residents : List Term
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

/-- Every live allocation retains the layout admitted for its declared type.
Vacant roots are included: physical typing cannot depend on a resident being
present. This is part of world typing, not an independent source certificate. -/
def World.LayoutRealized (program : Program) (world : World) (module : ModuleId) (unsafeAllowed : Bool) : Prop :=
  ∀ id root, world.roots.get id = some root → root.live = true →
    LayoutOf program ⟨[],[],0,module,unsafeAllowed,{}⟩ root.type root.layout

/-- Value, home and identity changes may preserve the same admitted layout. -/
theorem World.LayoutRealized.roots_congr {program : Program} {before after : World}
    {module : ModuleId} {unsafeAllowed : Bool}
    (realized : World.LayoutRealized program before module unsafeAllowed)
    (retained : ∀ id root, after.roots.get id = some root → root.live = true →
      ∃ original, before.roots.get id = some original ∧ original.live = true ∧
        original.type = root.type ∧ original.layout = root.layout) :
    World.LayoutRealized program after module unsafeAllowed := by
  intro id root found live
  obtain ⟨original,originalFound,originalLive,typeEq,layoutEq⟩ := retained id root found live
  rw [← typeEq,← layoutEq]
  exact realized id original originalFound originalLive


/-- Existing unsafe input/output obligations are semantic contracts on the
actual common binding product. They cannot introduce a storage permission. -/
structure UnsafeResourceContract where
  inputs : World → List StorageBinding → Prop
  outputs : World → List StorageBinding → Address → List StorageBinding → Prop

/-- Dependency identities are inherited from the actual loan resource, not
inferred from pointer fields or physical addresses. -/
def Authority.guardLoans : Authority → World → List Identity
  | .owner, _ => []
  | .loan identity, world => ((world.loans.get identity).map Loan.guards).getD []
  | .shared backing, world => backing.guardLoans world
  | .guarded backing carrier, world =>
      (carrier :: ((world.loans.get carrier).map Loan.guards).getD []) ++ backing.guardLoans world

/-- The loans explicitly authorizing this source view. Inherited guards are
already dependencies of these loans; requiring the original carriers again
would reject access through the very child that freezes them. -/
def Authority.carriers : Authority → List Identity
  | .owner => []
  | .loan identity => [identity]
  | .shared backing => backing.carriers
  | .guarded backing carrier => carrier :: backing.carriers

theorem Authority.Recorded.carriers {authority : Authority} {loans : Table Loan}
    (recorded : authority.Recorded loans) : ∀ identity ∈ authority.carriers, ∃ loan, loans.get identity = some loan := by
  induction authority with
  | owner => intro identity member; cases member
  | loan identity => intro current member; cases List.mem_singleton.mp member; exact recorded
  | shared backing ih => exact ih recorded
  | guarded backing carrier ih =>
    intro identity member
    rcases List.mem_cons.mp member with rfl | member
    · exact recorded.2
    · exact ih recorded.1 identity member

/-- Dereferencing retains every explicit source authority, without turning a
loan's inherited liveness dependencies into fresh caller permission checks. -/
def Authority.throughReference (authority : Authority) (identity : Identity) : Authority :=
  authority.carriers.foldr (fun carrier backing => .guarded backing carrier) (.loan identity)


def ReferenceAccess (incoming : Access) (mode : Mutability) : Access :=
  if incoming = .shared ∨ mode = .shared then .shared else .unique

def Authority.referenceView (authority : Authority) (identity : Identity) (access : Access) : Authority :=
  (authority.throughReference identity).lend access

def ResourceAccess (incoming : Access) (binding : StorageBinding) : Access :=
  match binding.authority with
  | .shared _ => .shared
  | _ => incoming

def Authority.resourceView (authority : Authority) (binding : StorageBinding) (access : Access) : Authority :=
  (authority.carriers.foldr (fun carrier backing => .guarded backing carrier) binding.authority).lend (ResourceAccess access binding)

theorem Authority.carriers_lend (authority : Authority) (access : Access) :
    (authority.lend access).carriers = authority.carriers := by
  unfold Authority.lend
  split <;> rfl

theorem Authority.carriers_guarded_fold (authority : Authority) (carriers : List Identity) :
    (carriers.foldr (fun carrier backing => Authority.guarded backing carrier) authority).carriers =
      carriers ++ authority.carriers := by
  induction carriers with
  | nil => rfl
  | cons carrier rest ih => simp only [List.foldr_cons,Authority.carriers,ih,List.cons_append]

theorem Authority.carriers_referenceView (authority : Authority) (identity : Identity) (access : Access) :
    (authority.referenceView identity access).carriers = authority.carriers ++ [identity] := by
  simp only [Authority.referenceView,Authority.carriers_lend,Authority.throughReference,
    Authority.carriers_guarded_fold,Authority.carriers]

theorem Authority.carriers_resourceView (authority : Authority) (binding : StorageBinding) (access : Access) :
    (authority.resourceView binding access).carriers = authority.carriers ++ binding.authority.carriers := by
  simp only [Authority.resourceView,Authority.carriers_lend,Authority.carriers_guarded_fold]


/-- The referent's lifetime is distinct from the temporary home of an
invocation's reference handle. A callee-owned handle may be cleared while an
outgoing child keeps this actual source-region loan alive. -/
def Authority.BorrowRegion (world : World) (address : Address) (region : Identity) : Authority → Prop
  | .owner => ∃ root, world.roots.get address.root = some root ∧ root.region = region
  | .loan identity => ∃ loan, world.loans.get identity = some loan ∧ loan.region = region
  | .shared backing | .guarded backing _ => backing.BorrowRegion world address region

/-- Owning and unique implicit claims belong to their actual handoff recipient.
Source reference loans retain their ordinary handle authority; a shared view
can be copied but cannot recover exclusive custody. -/
def Authority.Custodied (world : World) (custody : ClaimCustody) : Authority → Prop
  | .owner => True
  | .loan id => ∃ loan, world.loans.get id = some loan ∧
      (loan.kind = .restoring ∨ loan.kind = .destructor ∨ loan.custody = some custody)
  | .shared backing => backing.Recorded world.loans
  | .guarded backing _ => backing.Custodied world custody

/-- Provenance-bearing pointers retain the allocation's physical extent,
including one-past and stale pointers. This is representation coherence, not
permission to access: liveness, generation, domain, initialization and aliasing
are checked separately by `RawRange` and `PointsTo`. Address-only pointers
carry no allocation claim. Retiring storage retains its historical metadata. -/
def RawPointer.Origin (pointer : RawPointer) (world : World) : Prop :=
  ∀ id, pointer.allocation = some id → ∃ root,
    world.roots.get id = some root ∧ pointer.address = root.base + pointer.offset ∧
    pointer.offset ≤ root.layout.size

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

/-- A live loan may point at a hole, but not beneath a missing ancestor.
Both alternatives reuse the actual read/write storage model. -/
def World.Located (world : World) (address : Address) : Prop :=
  (∃ value, world.Stores address value) ∨ world.Vacant address

def World.Resident (world : World) (address : Address) (value : Value) : Prop :=
  ∃ root whole, world.roots.get address.root = some root ∧ root.live = true ∧
    address.generation = root.generation ∧ root.value = some whole ∧ ResidentAt whole address.fields value

def World.References (world : World) (identity : Identity) : Prop :=
  ∃ address value, world.Resident address value ∧ value.head = .reference identity

/-- Closed invariants retain their actual loan resources, independently of
whether any source reference handle names that loan. -/
def World.ResourceReferences (world : World) (identity : Identity) : Prop :=
  ∃ address value binding, world.Resident address value ∧ binding ∈ value.resources ∧
    binding.authority.parentLoan = some identity

inductive FieldOffset (program : Language.Program) (world : World) :
    Address → Term → Nat → Term → Nat → Prop where
  | tuple {address fields index type layouts layout offset} : fields[index]? = some type →
      ListRel (LayoutOf program ⟨[],[],0,default,false,{}⟩) fields layouts → AggregateLayout layouts layout →
      layout.offsets[index]? = some offset → FieldOffset program world address (.tuple fields) index type offset
  | bindings {address brand region fields index type layouts layout offset} : fields[index]? = some type →
      ListRel (LayoutOf program ⟨[],[],0,default,false,{}⟩) fields layouts → AggregateLayout layouts layout →
      layout.offsets[index]? = some offset → FieldOffset program world address (.bindings brand region fields) index type offset
  | callable {address id arguments fields index type layouts layout offset} : CallableFields program id arguments fields →
      fields[index]? = some type → ListRel (LayoutOf program ⟨[],[],0,default,false,{}⟩) fields layouts →
      AggregateLayout (program.input.target.codeIdentityLayout :: layouts) layout →
      layout.offsets[index+1]? = some offset → FieldOffset program world address (.callable id arguments) index type offset
  | array {address element sign width count index layout} : 0 ≤ count → index < count.toNat →
      LayoutOf program ⟨[],[],0,default,false,{}⟩ element layout →
      FieldOffset program world address (.array element (.constant (.integer sign width count))) index element
        (index * alignUp layout.size layout.alignment)
  | nominal {address id arguments data variant substitution types index type layout offset value} :
      program.Constructor variant.header.id data variant → data.header.id = id →
      Instantiates data.generics arguments substitution → ListRel (Substitutes substitution) (variant.fields.map (·.type)) types →
      types[index]? = some type → LayoutOf program ⟨[],[],0,data.header.module,false,{}⟩ (.nominal id arguments) layout →
      world.Stores address value → value.head = .constructor variant.header.id →
      (data.isEnum = false ∧ layout.offsets[index]? = some offset ∨
        ∃ (tag : Nat) (offsets : List Nat), data.variants[tag]? = some variant ∧ layout.variants[tag]? = some offsets ∧ offsets[index]? = some offset) →
      FieldOffset program world address (.nominal id arguments) index type offset

  /-- A declared container that is an alias application has the physical field
  offsets of its actual expansion. The program's own alias declaration fixes
  that expansion and the checked substitution edge that reaches it, exactly as
  `DefinitionalStep.alias` does; `LayoutOf.alias` then gives container and
  expansion the same layout, so every offset the layout determines is shared.
  This is the alias-headed case of the same ordered-layout derivation, not a
  second field walker, and the selected field keeps the expansion's - the
  actually stored - type. -/
  | alias {address id declaration arguments substitution expanded index type offset} :
      program.alias id = some declaration →
      Instantiates declaration.generics arguments substitution →
      Substitutes substitution declaration.value expanded →
      FieldOffset program world address expanded index type offset →
      FieldOffset program world address (.alias id arguments) index type offset

inductive AddressOffset (program : Language.Program) (world : World) : Address → Term → Nat → Prop where
  | root {id root} : world.roots.get id = some root → root.live = true →
      AddressOffset program world ⟨id,root.generation,[]⟩ root.type 0
  | child {address container offset index type childOffset} : AddressOffset program world address container offset →
      FieldOffset program world address container index type childOffset →
      AddressOffset program world (address.child index) type (offset+childOffset)

/-- The declared location type survives a vacant resident. This is a view of
the same address-layout derivation used by physical addressing, not a second
field-shape walker or a guess based on initialized contents. -/
def AddressType (program : Program) (world : World) (address : Address) (type : Term) : Prop :=
  ∃ offset, AddressOffset program world address type offset

inductive AncestorLoan (world : World) : Identity → Identity → Prop where
  | refl {identity} : AncestorLoan world identity identity
  | parent {ancestor parent child loan} : world.loans.get child = some loan → loan.parent = some parent →
      AncestorLoan world ancestor parent → AncestorLoan world ancestor child

def Conflict (requested : Access) (existing : Mutability) : Prop :=
  requested ≠ .shared ∨ existing = .unique

/-- A carrier loan is frozen by its dependent invariant accesses. Dependencies
also retain the carrier's lifetime; they do not give permission to its storage. -/
def LoanPermission (world : World) (id : Identity) (requested : Access) (address : Address) : Prop :=
  ∃ active, world.loans.get id = some active ∧ active.live = true ∧
    active.referent.root = address.root ∧ active.referent.generation = address.generation ∧
    (∃ suffix, address.fields = active.referent.fields ++ suffix) ∧
    (requested ≠ .shared → active.mode = .unique) ∧
    (∀ other loan, world.loans.get other = some loan → loan.live = true → other ≠ id →
      address.Overlaps loan.referent → Conflict requested loan.mode → AncestorLoan world other id) ∧
    (∀ guard ∈ active.guards, ∃ loan, world.loans.get guard = some loan ∧ loan.live = true) ∧
    (∀ other loan, world.loans.get other = some loan → loan.live = true → id ∈ loan.guards →
      requested = .shared)

def Permitted (world : World) (authority : Authority) (requested : Access) (address : Address) : Prop :=
  (∃ root, world.root address = some root) ∧
  (match authority with
   | .owner => ∀ id loan, world.loans.get id = some loan → loan.live = true →
       address.Overlaps loan.referent → ¬ Conflict requested loan.mode
   | .loan id => LoanPermission world id requested address
   | .shared backing => requested = .shared ∧ Permitted world backing requested address
   | .guarded backing carrier => Permitted world backing requested address ∧
       ∃ loan, world.loans.get carrier = some loan ∧ LoanPermission world carrier requested loan.referent)

/-- Source-state compatibility with one new live loan. Shared access can
overlap a shared loan; a carrier newly used as a guard becomes shared-only.
Guarded authority observes its actual carrier's referent, not the address
of the backing access. No future permission or second resource walk is used. -/
def Authority.LoanCompatible (world : World) (authority : Authority) (requested : Access)
    (address referent : Address) (mode : Mutability) (guards : List Identity) : Prop :=
  match authority with
  | .owner => address.Overlaps referent → ¬ Conflict requested mode
  | .loan identity => (address.Overlaps referent → ¬ Conflict requested mode) ∧
      (identity ∈ guards → requested = .shared)
  | .shared backing => backing.LoanCompatible world requested address referent mode guards
  | .guarded backing carrier => backing.LoanCompatible world requested address referent mode guards ∧
      ∀ loan, world.loans.get carrier = some loan →
        (loan.referent.Overlaps referent → ¬ Conflict requested mode) ∧
        (carrier ∈ guards → requested = .shared)

/-- The current allocation owner is the latest live owning node for the whole
physical allocation. Ordinary reference/storage descendants can exist without
changing that owner; an owning successor makes its ancestor historical. -/
def AllocationClaim (world : World) (authority : Authority) (address : Address) : Prop :=
  ∃ identity loan root domain,
    authority.parentLoan = some identity ∧ world.loans.get identity = some loan ∧
    loan.live = true ∧ loan.kind = .owning ∧ loan.referent = address ∧ address.fields = [] ∧
    world.root address = some root ∧ (root.home = .allocation domain ∨ root.home = .external domain) ∧
    (∀ child successor, world.loans.get child = some successor → successor.live = true →
      successor.kind = .owning → AncestorLoan world identity child → child = identity)

/-- A closed owner contains actual allocation or storage-loan resources.
Shared resources are real shared loans, never a shared wrapper around an
allocation-owner token. Copying them therefore cannot evade loan exclusion. -/
def StorageBinding.HeldBy (world : World) (owner : Identity) (binding : StorageBinding) : Prop :=
  binding.authority.Custodied world (.resident owner) ∧
  (AllocationClaim world binding.authority binding.address ∧ ¬ binding.ReadOnly ∨
    ∃ identity loan, binding.authority.parentLoan = some identity ∧
      world.loans.get identity = some loan ∧ loan.live = true ∧ loan.kind = .storageBorrow ∧
      loan.referent = binding.address ∧ (binding.ReadOnly → loan.mode = .shared))

/-- One actual resident graph supplies reference readiness and invariant
support. It follows structural fields, source reference loans, and the erased
resources retained by nominal residents. A raw pointer is not such an edge.
Finite derivations represent cyclic graphs without guessing a pointee shape. -/
inductive Value.ReachableResident (world : World) (value : Value)
    (authority : Authority) (incoming : Access) : Value → Authority → Access → Prop where
  | resident {path resident} : ResidentAt value path resident →
      value.ReachableResident world authority incoming resident authority incoming
  | referent {carrier parent parentAuthority parentAccess loan target path resident} :
      value.ReachableResident world authority incoming carrier parentAuthority parentAccess →
      carrier.head = .reference parent → world.loans.get parent = some loan →
      world.Stores loan.referent target → ResidentAt target path resident →
      value.ReachableResident world authority incoming resident
        (parentAuthority.referenceView parent (ReferenceAccess parentAccess loan.mode))
        (ReferenceAccess parentAccess loan.mode)
  | resource {carrier current access binding target path resident} :
      value.ReachableResident world authority incoming carrier current access → binding ∈ carrier.resources →
      world.Stores binding.address target → ResidentAt target path resident →
      value.ReachableResident world authority incoming resident (current.resourceView binding access)
        (ResourceAccess access binding)

def Value.ReachableReference (world : World) (value : Value) (authority : Authority) (incoming : Access)
    (identity : Identity) (current : Authority) (access : Access) : Prop :=
  ∃ resident, value.ReachableResident world authority incoming resident current access ∧ resident.head = .reference identity

theorem Value.ReachableReference.resident {world : World} {value resident : Value}
    {authority : Authority} {incoming : Access} {identity : Identity} {path : List Nat}
    (located : ResidentAt value path resident) (reference : resident.head = .reference identity) :
    value.ReachableReference world authority incoming identity authority incoming :=
  ⟨resident,.resident located,reference⟩

theorem Value.ReachableReference.referent {world : World} {value target resident : Value}
    {authority current : Authority} {incoming access : Access} {parent identity : Identity}
    {loan : Loan} {path : List Nat}
    (prior : value.ReachableReference world authority incoming parent current access)
    (found : world.loans.get parent = some loan) (stored : world.Stores loan.referent target)
    (located : ResidentAt target path resident) (reference : resident.head = .reference identity) :
    value.ReachableReference world authority incoming identity
      (current.referenceView parent (ReferenceAccess access loan.mode)) (ReferenceAccess access loan.mode) := by
  obtain ⟨carrier,reached,head⟩ := prior
  exact ⟨resident,.referent reached head found stored located,reference⟩

theorem ResidentAt.append {value child resident : Value} {first rest : List Nat}
    (outer : ResidentAt value first child) (inner : ResidentAt child rest resident) :
    ResidentAt value (first ++ rest) resident := by
  induction outer with
  | root => exact inner
  | field found _ ih => exact .field found (ih inner)

theorem Value.Initialized.resident {value resident : Value} {path : List Nat}
    (initialized : value.Initialized) (inside : ResidentAt value path resident) : resident.Initialized :=
  fun _ _ nested => initialized _ _ (inside.append nested)

/-- Rebasing follows the same graph once and retains its exact carrier suffix.
The initial authority changes, but no inherited dependency is introduced and
matching initial access yields matching access at every reached node. -/
theorem Value.ReachableResident.rebase_carriers {world : World} {value resident : Value}
    {authority current : Authority} {incoming access : Access}
    (reachable : value.ReachableResident world authority incoming resident current access)
    (base : Authority) (requested : Access) :
    ∃ next nextAccess, value.ReachableResident world base requested resident next nextAccess ∧
      (∃ trail, current.carriers = authority.carriers ++ trail ∧ next.carriers = base.carriers ++ trail) ∧
      (requested = incoming → nextAccess = access) ∧ (requested = .shared → nextAccess = .shared) := by
  induction reachable with
  | resident located => exact ⟨_,_,.resident located,⟨[],by simp,by simp⟩,id,id⟩
  | @referent carrier parent parentAuthority parentAccess loan target path resident prior reference found stored located ih =>
    obtain ⟨next,nextAccess,reached,⟨trail,original,rebased⟩,same,shared⟩ := ih
    refine ⟨_,_,.referent reached reference found stored located,⟨trail ++ [parent],?_,?_⟩,?_,?_⟩
    · rw [Authority.carriers_referenceView,original,List.append_assoc]
    · rw [Authority.carriers_referenceView,rebased,List.append_assoc]
    · intro equal
      exact congrArg (fun access => ReferenceAccess access loan.mode) (same equal)
    · intro equal
      simp only [ReferenceAccess,shared equal,true_or,ite_true]
  | @resource carrier current access binding target path resident prior member stored located ih =>
    obtain ⟨next,nextAccess,reached,⟨trail,original,rebased⟩,same,shared⟩ := ih
    refine ⟨_,_,.resource reached member stored located,⟨trail ++ binding.authority.carriers,?_,?_⟩,?_,?_⟩
    · rw [Authority.carriers_resourceView,original,List.append_assoc]
    · rw [Authority.carriers_resourceView,rebased,List.append_assoc]
    · intro equal
      exact congrArg (fun access => ResourceAccess access binding) (same equal)
    · intro equal
      rw [shared equal]
      unfold ResourceAccess
      split <;> rfl

theorem Value.ReachableResident.rebase {world : World} {value resident : Value}
    {authority current : Authority} {incoming access : Access}
    (reachable : value.ReachableResident world authority incoming resident current access)
    (base : Authority) (requested : Access) :
    ∃ next nextAccess, value.ReachableResident world base requested resident next nextAccess := by
  obtain ⟨next,nextAccess,reached,_⟩ := reachable.rebase_carriers base requested
  exact ⟨next,nextAccess,reached⟩

theorem Value.ReachableResident.resident_prefix {world : World} {value child resident : Value}
    {authority current : Authority} {incoming access : Access} {path : List Nat}
    (located : ResidentAt value path child)
    (reachable : child.ReachableResident world authority incoming resident current access) :
    value.ReachableResident world authority incoming resident current access := by
  induction reachable with
  | resident nested => exact .resident (located.append nested)
  | referent _ reference found stored nested ih => exact .referent ih reference found stored nested
  | resource _ member stored nested ih => exact .resource ih member stored nested

theorem Value.ReachableResident.referent_prefix {world : World} {value target resident : Value}
    {authority parentAuthority current : Authority} {incoming parentAccess access : Access}
    {parent : Identity} {loan : Loan}
    (prior : value.ReachableReference world authority incoming parent parentAuthority parentAccess)
    (found : world.loans.get parent = some loan) (stored : world.Stores loan.referent target)
    (reachable : target.ReachableResident world
      (parentAuthority.referenceView parent (ReferenceAccess parentAccess loan.mode))
      (ReferenceAccess parentAccess loan.mode) resident current access) :
    value.ReachableResident world authority incoming resident current access := by
  obtain ⟨carrier,reached,head⟩ := prior
  induction reachable with
  | resident located => exact .referent reached head found stored located
  | referent _ reference nextFound nextStored located ih => exact .referent ih reference nextFound nextStored located
  | resource _ member nextStored located ih => exact .resource ih member nextStored located

/-- Requested views do not change the actual reachable identities. -/
theorem Value.ReachableReference.rebase {world : World} {value : Value}
    {authority current : Authority} {incoming access : Access} {identity : Identity}
    (reachable : value.ReachableReference world authority incoming identity current access)
    (base : Authority) (requested : Access) :
    ∃ next nextAccess, value.ReachableReference world base requested identity next nextAccess := by
  obtain ⟨resident,reached,reference⟩ := reachable
  obtain ⟨next,nextAccess,reached⟩ := reached.rebase base requested
  exact ⟨next,nextAccess,resident,reached,reference⟩

theorem Value.ReachableReference.resident_prefix {world : World} {value child : Value}
    {authority current : Authority} {incoming access : Access} {identity : Identity} {path : List Nat}
    (located : ResidentAt value path child)
    (reachable : child.ReachableReference world authority incoming identity current access) :
    value.ReachableReference world authority incoming identity current access := by
  obtain ⟨resident,reached,reference⟩ := reachable
  exact ⟨resident,reached.resident_prefix located,reference⟩

theorem Value.ReachableReference.referent_prefix {world : World} {value target : Value}
    {authority parentAuthority current : Authority} {incoming parentAccess access : Access}
    {parent identity : Identity} {loan : Loan}
    (prior : value.ReachableReference world authority incoming parent parentAuthority parentAccess)
    (found : world.loans.get parent = some loan) (stored : world.Stores loan.referent target)
    (reachable : target.ReachableReference world
      (parentAuthority.referenceView parent (ReferenceAccess parentAccess loan.mode))
      (ReferenceAccess parentAccess loan.mode) identity current access) :
    value.ReachableReference world authority incoming identity current access := by
  obtain ⟨resident,reached,reference⟩ := reachable
  exact ⟨resident,Value.ReachableResident.referent_prefix prior found stored reached,reference⟩

/-- The actual storage observed by a resident's explicit resources. A raw
hole is still supported even though no stored value can be followed from it. -/
def Value.Support (world : World) (value : Value) (address : Address) : Prop :=
  ∃ resident authority access, value.ReachableResident world .owner .shared resident authority access ∧
    ((∃ identity loan, resident.head = .reference identity ∧ world.loans.get identity = some loan ∧ loan.referent = address) ∨
      ∃ binding, binding ∈ resident.resources ∧ binding.address = address)

def Value.SupportOutside (world : World) (value : Value) (mutation : Address) : Prop :=
  ∀ address, value.Support world address → ¬ mutation.Overlaps address

def Root.location (root : Root) : Root := { root with value := none }

/-- Observation agreement is a proof boundary, not another runtime ledger.
Only actual reachable storage can be observed by a declared invariant. -/
def Value.SupportFramed (before after : World) (value : Value) : Prop :=
  ∀ address, value.Support before address →
    after.read address = before.read address ∧
    (after.roots.get address.root).map Root.location = (before.roots.get address.root).map Root.location

mutual
  inductive CopyTree (program : Program) : Nat → Value → Nat → Value → Table Identity → Prop where
    | resident {next owner type head fields resources copied finish origins} : PrincipalOf program type .duplicable →
        (∀ resource ∈ resources, resource.ReadOnly) →
        CopyFields program (next+1) fields finish copied origins →
        CopyTree program next (.resident owner type head true fields resources) finish (.resident next type head true copied resources)
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


/-- Reborrows retain a live containing parent and cannot strengthen its mode.
Fresh loan identities strictly order parent edges, excluding forged cycles. -/
def World.LoanParents (world : World) : Prop :=
  ∀ id loan parent, world.loans.get id = some loan → loan.parent = some parent →
    ∃ ancestor, world.loans.get parent = some ancestor ∧ parent < id ∧
      ancestor.referent.Prefix loan.referent ∧ (loan.mode = .unique → ancestor.mode = .unique) ∧
      (loan.live = true → ancestor.live = true)

def World.LoanGuards (world : World) : Prop :=
  ∀ id loan guard, world.loans.get id = some loan → guard ∈ loan.guards →
    ∃ carrier, world.loans.get guard = some carrier ∧ guard < id ∧
      (loan.live = true → carrier.live = true)

def World.LiveLoanLocations (world : World) : Prop :=
  ∀ id loan, world.loans.get id = some loan → loan.live = true → world.Located loan.referent

def World.LoanKinds (world : World) : Prop :=
  ∀ id loan, world.loans.get id = some loan → loan.KindValid

/-- Proof factor for atomic construction: binding facts may name the owner
published by the enclosing result constructor. Actual machine states use
`WellFormed`, which fixes this bound to the actual allocated-owner frontier. -/
def World.WellFormedWithOrigins (world : World) (originBound : Identity) : Prop :=
  world.roots.Unique ∧ world.loans.Unique ∧ world.availability.Unique ∧
  world.liveRegions.Nodup ∧
  (∀ id available, world.availability.get id = some available →
    id = available.identity ∧ id < world.nextProof ∧ available.brand = .runtimeBrand (.proof id) ∧
    (available.active = true → available.region ∈ world.liveRegions ∧
      ∀ place ∈ available.reserved, (world.root place.address).isSome = true) ∧
    (∀ place ∈ available.reserved, place.authority.Recorded world.loans)) ∧
  (∀ address value pack, world.Resident address value → value.head = .bindings pack →
    pack.brand < world.nextProof ∧ pack.region ∈ world.liveRegions ∧
    pack.fields.length = value.fields.length ∧ pack.fields.Nodup ∧
    ∀ fact ∈ pack.facts, fact.resultOrigin < originBound) ∧
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
    left.mode = .unique ∨ right.mode = .unique → AncestorLoan world a b ∨ AncestorLoan world b a) ∧
  world.LoanParents ∧ world.LiveLoanLocations ∧ world.LoanGuards ∧ world.LoanKinds

def World.WellFormed (world : World) : Prop := world.WellFormedWithOrigins world.nextOwner

theorem World.reserved_authority_recorded {world : World} {originBound : Identity}
    (well : world.WellFormedWithOrigins originBound) {id : Identity} {available : Availability}
    (found : world.availability.get id = some available) {place : ResolvedPlace}
    (member : place ∈ available.reserved) : place.authority.Recorded world.loans :=
  (well.2.2.2.2.1 id available found).2.2.2.2 place member

theorem World.WellFormedWithOrigins.mono {world : World} {first last : Identity}
    (valid : world.WellFormedWithOrigins first) (bound : first ≤ last) : world.WellFormedWithOrigins last := by
  rcases valid with ⟨roots,loans,proofs,regions,available,packs,rest⟩
  refine ⟨roots,loans,proofs,regions,available,?_,rest⟩
  intro address value pack resident head
  obtain ⟨brand,region,length,distinct,facts⟩ := packs address value pack resident head
  exact ⟨brand,region,length,distinct,fun fact member => Nat.lt_of_lt_of_le (facts fact member) bound⟩

theorem World.loanParents {world : World} {originBound : Identity}
    (valid : world.WellFormedWithOrigins originBound) : world.LoanParents :=
  valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem World.liveLoanLocations {world : World} {originBound : Identity}
    (valid : world.WellFormedWithOrigins originBound) : world.LiveLoanLocations :=
  valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem World.loanGuards {world : World} {originBound : Identity}
    (valid : world.WellFormedWithOrigins originBound) : world.LoanGuards :=
  valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem World.loanKinds {world : World} {originBound : Identity}
    (valid : world.WellFormedWithOrigins originBound) : world.LoanKinds :=
  valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem World.shared_loan_nonowning {world : World} {originBound id : Identity} {loan : Loan}
    (valid : world.WellFormedWithOrigins originBound) (found : world.loans.get id = some loan)
    (shared : loan.mode = .shared) : loan.kind ≠ .owning := by
  intro owning
  have unique := (World.loanKinds valid id loan found).1 owning
  cases shared.symm.trans unique

theorem World.owner_bound {world : World} {originBound : Identity}
    (valid : world.WellFormedWithOrigins originBound) {address : Address} {value : Value}
    (resident : world.Resident address value) : value.owner < world.nextOwner :=
  valid.2.2.2.2.2.2.1 address value resident

theorem World.loanBounds {world : World} {originBound : Identity} (valid : world.WellFormedWithOrigins originBound)
    {id : Identity} {loan : Loan} (found : world.loans.get id = some loan) : id < world.nextLoan :=
  (valid.2.2.2.2.2.2.2.2.2.2.2.2.1 id loan found).2.1

theorem World.loanIdentity {world : World} (valid : world.WellFormed)
    {id : Identity} {loan : Loan} (found : world.loans.get id = some loan) : id = loan.identity :=
  (valid.2.2.2.2.2.2.2.2.2.2.2.2.1 id loan found).1

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

def DisjointStorage (world : World) (base size : Nat) : Prop :=
  ∀ id root, world.roots.get id = some root → root.live = true →
    size = 0 ∨ root.layout.size = 0 ∨ base+size ≤ root.base ∨ root.base+root.layout.size ≤ base

/-- The positive nonphysical request shared by actual allocation and resource
exhaustion. Missing type/layout/lifetime evidence is not physical failure. -/
structure AllocationRequest (program : Program) (world : World) (region : Identity)
    (type : Term) (layout : Layout) : Prop where
  region_live : region ∈ world.liveRegions
  type_supported : type.RuntimeRegionsBelow world.nextRegion
  layout_valid : layout.Valid
  size_bound : layout.size ≤ program.input.target.maximumObjectBytes
  layout_of : ∃ module unsafeAllowed, LayoutOf program ⟨[],[],0,module,unsafeAllowed,{}⟩ type layout

/-- Ordinary homes, raw buffers and exhaustion use this same physical extent
condition. Zero-sized homes still require an aligned positive address and
retain distinct logical storage identities. -/
structure PhysicalExtent (target : TargetProfile) (world : World) (layout : Layout) (base : Nat) : Prop where
  positive : 0 < base
  aligned : base % layout.alignment = 0
  bounded : base + layout.size < 2^target.pointerBits
  disjoint : DisjointStorage world base layout.size

namespace Execution

structure Relocation where
  roots : List Identity
  owners : List Identity
  loans : List Identity
  regions : List Identity
  activations : List Identity
  scopes : List Identity
  handlers : List Identity
  rootBase : Identity
  ownerBase : Identity
  loanBase : Identity
  regionBase : Identity
  activationBase : Identity
  scopeBase : Identity
  handlerBase : Identity
  physical : Table Nat
  deriving Repr, Inhabited

def relocateId (selected : List Identity) (base id : Identity) : Identity :=
  if id ∈ selected then base + id else id

def Relocation.root (map : Relocation) := relocateId map.roots map.rootBase
def Relocation.owner (map : Relocation) := relocateId map.owners map.ownerBase
def Relocation.loan (map : Relocation) := relocateId map.loans map.loanBase
def Relocation.region (map : Relocation) := relocateId map.regions map.regionBase
def Relocation.activation (map : Relocation) := relocateId map.activations map.activationBase
def Relocation.scope (map : Relocation) := relocateId map.scopes map.scopeBase
def Relocation.handler (map : Relocation) := relocateId map.handlers map.handlerBase

def Relocation.address (map : Relocation) (address : Address) : Address :=
  { address with root := map.root address.root }

def Relocation.pointer (map : Relocation) (pointer : RawPointer) : RawPointer :=
  match pointer.allocation with
  | none => pointer
  | some root =>
    if root ∈ map.roots then
      match map.physical.get root with
      | none => pointer
      | some base => { pointer with address := base+pointer.offset, allocation := some (map.root root) }
    else pointer

def Relocation.term (map : Relocation) : Term → Term := Term.renameRuntimeRegions map.region

def Relocation.authority (map : Relocation) : Authority → Authority
  | .owner => .owner
  | .loan id => .loan (map.loan id)
  | .shared backing => .shared (map.authority backing)
  | .guarded backing carrier => .guarded (map.authority backing) (map.loan carrier)

def Relocation.binding (map : Relocation) (binding : StorageBinding) : StorageBinding :=
  { binding with address := map.address binding.address, authority := map.authority binding.authority }

def Relocation.home (map : Relocation) : Home → Home
  | .localSlot activation scope => .localSlot (map.activation activation) (map.scope scope)
  | .temporary activation scope => .temporary (map.activation activation) (map.scope scope)
  | home => home

mutual
  def Relocation.value (map : Relocation) : Value → Value
    | .resident owner type head live fields resources => .resident (map.ownerBase + owner) (map.term type)
        (match head with
         | .reference loan => .reference (map.loan loan)
         | .callable id arguments => .callable id (arguments.map map.term)
         | .operation id arguments => .operation id (arguments.map map.term)
         | .pointer pointer => .pointer (map.pointer pointer)
         | .bindings pack => .bindings { pack.mapOrigins map.owner with region := map.region pack.region }
         | other => other)
        live (map.values fields) (resources.map map.binding)

  def Relocation.values (map : Relocation) : List (Option Value) → List (Option Value)
    | [] => []
    | none :: rest => none :: map.values rest
    | some value :: rest => some (map.value value) :: map.values rest
end

def Relocation.rootValue (map : Relocation) (id : Identity) (root : Root) : Root :=
  { root with home := map.home root.home, region := map.region root.region, type := map.term root.type, value := root.value.map map.value, base := (map.physical.get id).getD root.base }

def Relocation.custody (map : Relocation) : ClaimCustody → ClaimCustody
  | .activation id => .activation (map.activation id)
  | .resident id => .resident (map.owner id)
  | .host id => .host (map.root id)
  | .registration id => .registration id

def Relocation.loanValue (map : Relocation) (loan : Loan) : Loan :=
  { loan with
    identity := map.loan loan.identity
    parent := loan.parent.map map.loan
    guards := loan.guards.map map.loan
    custody := loan.custody.map map.custody
    referent := map.address loan.referent
    region := map.region loan.region }

def Relocation.copyWorld (map : Relocation) (world : World) (homes : Table Home) : World :=
  { world with
    roots := world.roots ++ (world.roots.filter (fun entry => entry.1 ∈ map.roots)).map (fun (id,root) =>
      (map.root id, map.rootValue id { root with home := (homes.get id).getD root.home }))
    loans := world.loans ++ (world.loans.filter (fun entry => entry.1 ∈ map.loans)).map
      (fun (id,loan) => (map.loan id,map.loanValue loan))
    liveRegions := world.liveRegions ++ map.regions.map map.region
    nextRoot := map.rootBase + world.nextRoot
    nextOwner := map.ownerBase + world.nextOwner
    nextLoan := map.loanBase + world.nextLoan
    nextRegion := map.regionBase + world.nextRegion }

/-- The actual shared loans named by the captured product, closed over the
same containment and carrier-dependency edges used by loan admission. Raw
pointer bits are not roots of this selector. Unique external dependencies
remain external: this closure never manufactures a copy of unique authority. -/
inductive SnapshotLoan (world : World) (roots : List Identity) (authorities : List Authority) : Identity → Prop where
  | reference {id loan address value} : world.loans.get id = some loan → loan.live = true → loan.mode = .shared →
      address.root ∈ roots → world.Resident address value → value.head = .reference id →
      SnapshotLoan world roots authorities id
  | resource {id loan address value binding} : world.loans.get id = some loan → loan.live = true → loan.mode = .shared →
      address.root ∈ roots → world.Resident address value → binding ∈ value.resources →
      id ∈ binding.authority.parentLoan.toList ++ binding.authority.guardLoans world →
      SnapshotLoan world roots authorities id
  | control {id loan authority} : world.loans.get id = some loan → loan.live = true → loan.mode = .shared →
      authority ∈ authorities → id ∈ authority.parentLoan.toList ++ authority.guardLoans world →
      SnapshotLoan world roots authorities id
  | parent {id loan parent ancestor} : SnapshotLoan world roots authorities id →
      world.loans.get id = some loan → loan.parent = some parent →
      world.loans.get parent = some ancestor → ancestor.live = true → ancestor.mode = .shared →
      SnapshotLoan world roots authorities parent
  | guard {id loan guard carrier} : SnapshotLoan world roots authorities id →
      world.loans.get id = some loan → guard ∈ loan.guards →
      world.loans.get guard = some carrier → carrier.live = true → carrier.mode = .shared →
      SnapshotLoan world roots authorities guard

/-- This is the pure storage part of the actual snapshot plan. Control
capture extends it; declared invariants consume it directly. There is one
copyWorld/value producer and one selector, not a second resource mapping. -/
theorem SnapshotLoan.record {world : World} {roots : List Identity} {authorities : List Authority} {id : Identity}
    (selected : SnapshotLoan world roots authorities id) :
    ∃ loan, world.loans.get id = some loan ∧ loan.live = true ∧ loan.mode = .shared := by
  cases selected with
  | reference found live shared _ _ _ => exact ⟨_,found,live,shared⟩
  | resource found live shared _ _ _ _ => exact ⟨_,found,live,shared⟩
  | control found live shared _ _ => exact ⟨_,found,live,shared⟩
  | parent _ _ _ found live shared => exact ⟨_,found,live,shared⟩
  | guard _ _ _ found live shared => exact ⟨_,found,live,shared⟩

structure Relocation.StoragePlan (program : Program) (world : World) (authorities : List Authority)
    (map : Relocation) : Prop where
  rootBase : map.rootBase = world.nextRoot
  ownerBase : map.ownerBase = world.nextOwner
  loanBase : map.loanBase = world.nextLoan
  regionBase : map.regionBase = world.nextRegion
  owners : ∀ id, id ∈ map.owners ↔ ∃ address value,
    world.Resident address value ∧ address.root ∈ map.roots ∧ value.owner = id
  loans : ∀ id, id ∈ map.loans ↔ SnapshotLoan world map.roots authorities id
  liveRegions : ∀ id ∈ map.regions, id ∈ world.liveRegions
  physicalUnique : map.physical.Unique
  physicalRoots : map.physical.map Prod.fst = map.roots
  physical : ∀ id root, id ∈ map.roots → world.roots.get id = some root → ∃ base,
    map.physical.get id = some base ∧ 0 < base ∧ base % root.layout.alignment = 0 ∧
    base+root.layout.size < 2^program.input.target.pointerBits ∧ DisjointStorage world base root.layout.size
  disjoint : ∀ a b left right x y, a ∈ map.roots → b ∈ map.roots → a ≠ b →
    world.roots.get a = some left → world.roots.get b = some right →
    map.physical.get a = some x → map.physical.get b = some y →
    left.layout.size = 0 ∨ right.layout.size = 0 ∨ x+left.layout.size ≤ y ∨ y+right.layout.size ≤ x

end Execution

/-- A shared wrapper retains only a view of historical backing; an uncapped
live unique authority cannot be replayed. Explicit carrier guards retain their
records but do not themselves grant storage permission. -/
def Authority.Replayable (world : World) : Authority → Prop
  | .owner => True
  | .loan id => ∃ loan, world.loans.get id = some loan ∧ (loan.live = true → loan.mode = .shared)
  | .shared backing => backing.Recorded world.loans
  | .guarded backing carrier => backing.Replayable world ∧ ∃ loan, world.loans.get carrier = some loan

namespace Execution

/-- The storage projection of replay admission, derived from the same actual
captured residents and control authorities. Invariants may rely on it without
depending on later machine types or a typed post-world. -/
structure Relocation.StorageReady (world : World) (roots : List Identity) (authorities : List Authority) : Prop where
  resources : ∀ address value, address.root ∈ roots → world.Resident address value →
    ∀ binding ∈ value.resources, binding.ReadOnly ∧ binding.HeldBy world value.owner
  references : ∀ address value id loan, address.root ∈ roots → world.Resident address value →
    value.head = .reference id → world.loans.get id = some loan → loan.mode = .shared
  loans : ∀ id loan, world.loans.get id = some loan → loan.live = true → loan.referent.root ∈ roots → loan.mode = .shared
  control : ∀ authority ∈ authorities, authority.Replayable world

end Execution

structure UnsafeInvariantContract (program : Program) where
  owner : DeclId
  holds : World → Value → Prop
  framed : ∀ before after value, value.SupportFramed before after → holds before value → holds after value
  /-- Source Copy admission concerns the actual retained resources before
  traversal. A nominal's semantic duplicability cannot hide an owning or
  unique erased binding. The later copied law cannot establish this premise:
  its CopyTree already requires these resources to be read-only. -/
  copyResources : ∀ world value, world.WellFormed → holds world value →
    PrincipalOf program value.type .duplicable → ∀ binding ∈ value.resources, binding.ReadOnly
  /-- Copy preserves the physical representation and shared resources while
  freshening owners and sealed-fact origins. An invariant of a duplicable type
  must be independent of those ghost identities; this law creates no Copy
  derivation and gives nonduplicable types no additional permission. -/
  copied : ∀ world next value finish raw origins (map : Identity → Identity),
    CopyTree program next value finish raw origins → holds world value →
      holds world (raw.mapBindingOrigins map)
  /-- A replayable invariant is equivariant under the real finite storage
  relocation, including pointer addresses, erased loans and their custody.
  The premises concern the admitted source and actual mapping, never the
  intended closed or well-typed post-state. -/
  relocated : ∀ world (map : Execution.Relocation) authorities homes address value,
    world.WellFormed → Execution.Relocation.StoragePlan program world authorities map →
    Execution.Relocation.StorageReady world map.roots authorities →
    address.root ∈ map.roots → world.Resident address value → holds world value →
      holds (map.copyWorld world homes) (map.value value)
  /-- A declared invariant cannot depend on internal home bookkeeping. Suspension
  capture, replay and cancellation legitimately relabel the homes of captured
  storage while moving no value, creating no loan and leaving every read of the
  resident unchanged; no source term observes a home. Requiring independence
  here is the rehoming counterpart of `relocated`: both rewrite the ghost
  home field, so an invariant of a duplicable type must survive both. -/
  rehomed : ∀ world (select : Identity → Root → Home) value,
    holds world value →
      holds { world with roots := world.roots.map (fun (id,root) => (id,{ root with home := select id root })) } value

structure RuntimeProgram where
  declarations : Program
  unsafeContracts : DeclId → Option UnsafeResourceContract := fun _ => none
  unsafeInvariants : DeclId → Option (UnsafeInvariantContract declarations) := fun _ => none

/-- Caller-unsafe contracts belong to unsafe function declarations (§15.1).
Safe bodies may establish unsafe invariants internally; they cannot impose
hidden unsafe obligations on an ordinary caller, including implicit Drop. -/
def RuntimeProgram.UnsafeContractsValid (program : RuntimeProgram) : Prop :=
  ∀ identity contract, program.unsafeContracts identity = some contract →
    ∃ declaration, program.declarations.function identity = some declaration ∧ declaration.signature.unsafeAllowed = true

theorem RuntimeProgram.UnsafeContractsValid.safe {program : RuntimeProgram} {identity : DeclId}
    {declaration : FunctionDefinition} (valid : program.UnsafeContractsValid)
    (declared : program.declarations.function identity = some declaration)
    (safe : declaration.signature.unsafeAllowed = false) : program.unsafeContracts identity = none := by
  cases selected : program.unsafeContracts identity with
  | none => rfl
  | some contract =>
    obtain ⟨actual,found,requiresUnsafe⟩ := valid identity contract selected
    have same := Option.some.inj (found.symm.trans declared)
    subst actual
    cases safe.symm.trans requiresUnsafe


/-- The declaration's local closed invariant for this actual resident. Its
recursive use and independent storage custody are supplied by ResourcesClosed. -/
def Value.InvariantClosed (program : RuntimeProgram) (world : World) (resident : Value) : Prop :=
    match resident.type with
     | .nominal identity _ => ∃ data, program.declarations.data identity = some data ∧
         (match data.invariant with
          | none => resident.resources = []
          | some invariant => ∃ contract, program.unsafeInvariants invariant = some contract ∧
              contract.owner = identity ∧ contract.holds world resident)
     | _ => resident.resources = []

/-- Every actual nominal resident in the common graph carries its declared
closed invariant. Open representations are allowed inside unsafe execution,
but cannot cross an ordinary value, borrow, or restoration boundary. -/
def Value.ResourcesClosed (program : RuntimeProgram) (world : World) (value : Value) : Prop :=
  ∀ resident authority access, value.ReachableResident world .owner .shared resident authority access →
    (∀ binding ∈ resident.resources, binding.HeldBy world resident.owner) ∧ resident.InvariantClosed program world

/-- Section 7.5 forbids transporting a reference handle while its referent
has a hole. The condition is transitive through actual references, so packing
the handle into a value or passing a pointer to another handle cannot conceal
the restoration obligation. Erased raw-storage loans are not reference values. -/
def Value.LoansRestored (program : RuntimeProgram) (world : World) (value : Value) : Prop :=
  ∀ identity authority access, value.ReachableReference world .owner .shared identity authority access →
    ∃ loan, world.loans.get identity = some loan ∧ loan.live = true ∧
      world.Initialized loan.referent ∧
      ∀ referent, world.Stores loan.referent referent → referent.ResourcesClosed program world

/-- A readable handle is not permission to use a frozen referent. All value
boundaries discharge the actual reachable reference views, not just the local
slot permission. The authority prefix is retained when following references. -/
def Value.ReferencesAccessible (world : World) (value : Value)
    (authority : Authority) (incoming : Access) : Prop :=
  ∀ identity current access, value.ReachableReference world authority incoming identity current access →
    ∃ loan, world.loans.get identity = some loan ∧ loan.live = true ∧
      Permitted world (current.referenceView identity (ReferenceAccess access loan.mode))
        (ReferenceAccess access loan.mode) loan.referent

theorem Value.ReferencesAccessible.resident {world : World} {value child : Value}
    {authority : Authority} {access : Access} {path : List Nat}
    (ready : value.ReferencesAccessible world authority access) (located : ResidentAt value path child) :
    child.ReferencesAccessible world authority access :=
  fun identity current requested reachable => ready identity current requested (reachable.resident_prefix located)

theorem Value.ReferencesAccessible.referent {world : World} {value target : Value}
    {authority current : Authority} {incoming access : Access} {identity : Identity} {loan : Loan}
    (ready : value.ReferencesAccessible world authority incoming)
    (reachable : value.ReachableReference world authority incoming identity current access)
    (found : world.loans.get identity = some loan) (stored : world.Stores loan.referent target) :
    target.ReferencesAccessible world (current.referenceView identity (ReferenceAccess access loan.mode))
      (ReferenceAccess access loan.mode) :=
  fun next nextAuthority nextAccess nested => ready next nextAuthority nextAccess
    (Value.ReachableReference.referent_prefix reachable found stored nested)

/-- A nonrelocating value move cannot consume storage that one of its
transported reference handles still denotes, including cyclic/self references.
This obligation is about the real consumed sources, not a post-state premise. -/
def Value.ReferencesOutside (world : World) (value : Value) (source : Address) : Prop :=
  ∀ identity authority access, value.ReachableReference world .owner .shared identity authority access →
    ∀ loan, world.loans.get identity = some loan → ¬ source.Overlaps loan.referent

/-- Ordinary moves, copies and borrows share reference restoration and the
owned resources retained by nominal carriers. A unique carrier borrow cannot
borrow its owned pointee incompatibly with an existing pointee loan. -/
def Value.ResourcesAccessible (program : RuntimeProgram) (world : World)
    (value : Value) (access : Access) : Prop :=
  value.ResourcesClosed program world ∧ value.LoansRestored program world ∧
  value.ReferencesAccessible world .owner access ∧
  ∀ resident authority incoming, value.ReachableResident world .owner access resident authority incoming →
    ∀ binding ∈ resident.resources, Permitted world (authority.resourceView binding incoming)
      (ResourceAccess incoming binding) binding.address

/-- A handoff retains every support of the actual passed value across its
whole pending write footprint. Lending selects a weaker value view; it does
not remove the obligation to preserve that view while later inputs move. -/
def Value.HandoffReady (program : RuntimeProgram) (world : World) (value : Value)
    (access : Access) (sources : List Address) : Prop :=
  value.ResourcesAccessible program world access ∧
    ∀ source ∈ sources, value.SupportOutside world source

abbrev Value.MoveReady (program : RuntimeProgram) (world : World) (value : Value)
    (sources : List Address) : Prop := value.HandoffReady program world .owned sources

def Values.MoveReady (program : RuntimeProgram) (world : World) (values : List Value)
    (sources : List Address) : Prop :=
  ∀ value ∈ values, value.Initialized ∧ value.MoveReady program world sources

/-- The resident snapshot is the actual ordered source read. Construction
and by-value payload protection share its readiness, source separation and
retained authorities; the explicit footprint also includes destination writes
when a primitive uses existing storage. -/
def ResidentHandoffReady (program : RuntimeProgram) (world : World)
    (sources : List ResolvedPlace) (values : List Value) (footprint : List Address) : Prop :=
  ListRel (fun source value => world.Stores source.address value) sources values ∧
  Values.MoveReady program world values footprint ∧
  sources.Pairwise (fun first last => ¬ first.address.Overlaps last.address) ∧
  ∀ source ∈ sources, Permitted world source.authority .owned source.address

theorem Value.HandoffReady.restrict {program : RuntimeProgram} {world : World} {value : Value}
    {access : Access} {all kept : List Address}
    (ready : value.HandoffReady program world access all)
    (included : ∀ source ∈ kept, source ∈ all) :
    value.HandoffReady program world access kept :=
  ⟨ready.1,fun source member => ready.2 source (included source member)⟩

theorem Value.ResourcesAccessible.references {program : RuntimeProgram} {world : World}
    {value : Value} {access : Access} (ready : value.ResourcesAccessible program world access) :
    value.ReferencesAccessible world .owner access := ready.2.2.1

theorem Value.ReferencesAccessible.direct {world : World} {value resident : Value}
    {authority : Authority} {incoming : Access} {path : List Nat} {identity : Identity}
    (ready : value.ReferencesAccessible world authority incoming)
    (located : ResidentAt value path resident) (reference : resident.head = .reference identity) :
    ∃ loan, world.loans.get identity = some loan ∧ loan.live = true ∧
      Permitted world (authority.referenceView identity (ReferenceAccess incoming loan.mode))
        (ReferenceAccess incoming loan.mode) loan.referent :=
  ready identity authority incoming (.resident located reference)

def World.ResourcesClosed (program : RuntimeProgram) (world : World) (address : Address) : Prop :=
  ∀ value, world.Stores address value → value.ResourcesClosed program world ∧ value.LoansRestored program world

theorem Value.LoansRestored.direct {program : RuntimeProgram} {world : World} {value : Value}
    (restored : value.LoansRestored program world) {path : List Nat} {resident : Value} {identity : Identity}
    (located : ResidentAt value path resident) (reference : resident.head = .reference identity) :
    ∃ loan, world.loans.get identity = some loan ∧ loan.live = true ∧ world.Initialized loan.referent := by
  obtain ⟨loan,found,live,initialized,_⟩ := restored identity .owner .shared (.resident located reference)
  exact ⟨loan,found,live,initialized⟩

theorem Permitted.recorded {world : World} {authority : Authority} {requested : Access} {address : Address}
    (permitted : Permitted world authority requested address) : authority.Recorded world.loans := by
  induction authority with
  | owner => trivial
  | loan id => obtain ⟨loan,found,_⟩ := permitted.2; exact ⟨loan,found⟩
  | shared backing ih => exact ih permitted.2.2
  | guarded backing carrier ih =>
    exact ⟨ih permitted.2.1,by obtain ⟨loan,found,_⟩ := permitted.2.2; exact ⟨loan,found⟩⟩

/-- Loading a unique handle through a shared place does not recover unique
referent access. All dereference consumers use this same view selection. -/
def ReferenceView (world : World) (handle : Address) (authority : Authority)
    (id : Identity) (mode : Mutability) (permission : Authority) (access : Access) : Prop :=
  (mode = .shared ∧ permission = authority.referenceView id .shared ∧ access = .shared) ∨
  (mode = .unique ∧ Permitted world authority .unique handle ∧
    permission = authority.referenceView id .unique ∧ access = .unique) ∨
  (mode = .unique ∧ ¬ Permitted world authority .unique handle ∧
    permission = authority.referenceView id .shared ∧ access = .shared)

theorem shared_authority_cannot_strengthen {world backing requested address}
    (permission : Permitted world (.shared backing) requested address) : requested = .shared :=
  permission.2.1

theorem reference_view_shared_carrier {world handle backing id mode permission access}
    (view : ReferenceView world handle (.shared backing) id mode permission access) : access = .shared := by
  rcases view with ⟨_,_,shared⟩ | ⟨_,writable,_,_⟩ | ⟨_,_,_,shared⟩
  · exact shared
  · cases shared_authority_cannot_strengthen writable
  · exact shared

/-- Allocation introduces a storage home at a fresh, aligned physical extent,
never an initialized owner. Its real request is already statically admitted;
runtime representation cannot come from hypothetical binders or assumptions. -/
inductive Allocates (program : Program) : World → Home → Identity → Term → Layout → Bool → Address → World → Prop where
  | fresh {before home region type layout mutable base} : AllocationRequest program before region type layout →
      PhysicalExtent program.input.target before layout base →
      Allocates program before home region type layout mutable ⟨before.nextRoot,0,[]⟩
        { before with
          roots := before.roots.set before.nextRoot
            ⟨home,0,region,base,layout,type,none,mutable,before.clock,true,List.replicate layout.size none⟩
          nextRoot := before.nextRoot+1
          clock := before.clock+1 }

/-- A genuine resource outcome requires the same positive request as success
and absence of every physical extent, not absence of an arbitrary derivation. -/
def AllocationExhausted (program : Program) (world : World) (region : Identity)
    (type : Term) (layout : Layout) : Prop :=
  AllocationRequest program world region type layout ∧
    ¬ ∃ base, PhysicalExtent program.input.target world layout base

inductive Clears : World → List Address → World → Prop where
  | nil {world} : Clears world [] world
  | cons {before address rest middle after} : before.write address none = some middle →
      Clears middle rest after → Clears before (address :: rest) after

inductive NewValue (program : RuntimeProgram) : World → Address → Term → ValueHead → List ResolvedPlace → World → Prop where
  | construct {before destination type head sources residents taken after} : before.Vacant destination →
      AddressType program.declarations before destination type →
      ResidentHandoffReady program before sources residents (destination :: sources.map ResolvedPlace.address) →
      (∀ source ∈ sources, ¬ source.address.Overlaps destination) →
      Clears before (sources.map ResolvedPlace.address) taken →
      taken.write destination (some (.resident before.nextOwner type head true (residents.map some))) = some after →
      NewValue program before destination type head sources { after with nextOwner := before.nextOwner+1 }

inductive Transfers (program : RuntimeProgram) : World → Authority → Address → Address → World → Prop where
  | move {before authority source destination value cleared after} :
      before.Stores source value → value.Initialized → value.MoveReady program before [source,destination] →
      Permitted before authority .owned source →
      before.Vacant destination → ¬ source.Overlaps destination →
      AddressType program.declarations before destination value.type →
      before.write source none = some cleared → cleared.write destination (some value) = some after →
      Transfers program before authority source destination after

theorem Transfers.permission {program before authority source destination after}
    (transfer : Transfers program before authority source destination after) :
    Permitted before authority .owned source := by cases transfer; assumption

theorem NewValue.inputPermission {program before destination type head sources after}
    (constructed : NewValue program before destination type head sources after)
    {source : ResolvedPlace} (member : source ∈ sources) :
    Permitted before source.authority .owned source.address := by
  cases constructed with
  | construct _ _ ready _ _ _ => exact ready.2.2.2 source member

inductive Copies (program : RuntimeProgram) : World → Authority → Address → Address → World → Prop where
  | copy {before authority source destination value cloned next after} :
      before.Stores source value → value.Initialized → value.HandoffReady program before .shared [destination] →
      Permitted before authority .shared source →
      before.Vacant destination → AddressType program.declarations before destination value.type →
      CopyValue program.declarations before.nextOwner value next cloned →
      before.write destination (some cloned) = some after →
      Copies program before authority source destination { after with nextOwner := next }

inductive Acquires (program : RuntimeProgram) : World → Authority → Bool → Address → Address → World → Prop where
  | explicitMove {before authority source destination after} : Transfers program before authority source destination after →
      Acquires program before authority true source destination after
  | copy {before authority source destination after} : Copies program before authority source destination after →
      Acquires program before authority false source destination after
  | move {before authority source destination after value principal} : before.Stores source value →
      PrincipalOf program.declarations value.type principal → principal ≠ .duplicable → Transfers program before authority source destination after →
      Acquires program before authority false source destination after

/-- Source reference formation requires an addressable language value. A
hidden invocation guard can instead lock logical storage (such as an available
environment witness) without exposing a source reference to that storage. Both
uses create the same loan and are governed by the same parent/cleanup rules. -/
inductive LoanPurpose where
  | source | invocation | destructor
  deriving DecidableEq, BEq, Repr, Inhabited

def LoanPurpose.Admitted (purpose : LoanPurpose) (program : Program) (type : Term) : Prop :=
  match purpose with
  | .source | .destructor => Addressable program ⟨[],[],0,default,false,{}⟩ type
  | .invocation => True

def LoanPurpose.kind : LoanPurpose → LoanKind
  | .source | .invocation => .restoring
  | .destructor => .destructor

inductive FormsLoan (program : RuntimeProgram) (purpose : LoanPurpose) :
    World → Authority → Mutability → Identity → Address → Address → World → Prop where
  | borrow {before authority mode region referent destination value after parent} :
      before.Stores referent value → AddressType program.declarations before referent value.type →
      value.Initialized → region ∈ before.liveRegions →
      purpose.Admitted program.declarations value.type →
      value.ResourcesAccessible program before (if mode = .shared then .shared else .unique) →
      Permitted before authority (if mode = .shared then .shared else .unique) referent →
      before.Vacant destination →
      AddressType program.declarations before destination (.reference mode (.runtimeRegion region) value.type) →
      parent = authority.parentLoan →
      before.write destination (some (.resident before.nextOwner
        (.reference mode (.runtimeRegion region) value.type) (.reference before.nextLoan) true [])) = some after →
      FormsLoan program purpose before authority mode region referent destination
        { after with
          loans := before.loans.set before.nextLoan
            ⟨before.nextLoan,parent,referent,mode,region,true,purpose.kind,authority.guardLoans before,false,none⟩
          nextOwner := before.nextOwner+1
          nextLoan := before.nextLoan+1 }

/-- The source boundary retains exactly its previous addressability guard. -/
abbrev Borrows (program : RuntimeProgram) := FormsLoan program .source

/-- Erased storage inputs use the same exclusion tree as resident loans.
They do not materialize a source reference or promise initialized `T` on
return: those remain obligations of ordinary reference formation. An owning
input transfers the storage obligation; lent inputs must return it explicitly.
The caller supplies this authority from the common binding domain. -/
inductive ClaimsStorage (custody : ClaimCustody) :
    World → Authority → Access → Address → Identity → World → Prop where
  | claim {before authority access referent root} :
      before.root referent = some root → before.Located referent →
      Permitted before authority access referent →
      ClaimsStorage custody before authority access referent before.nextLoan
        { before with
          loans := before.loans.set before.nextLoan
            ⟨before.nextLoan,authority.parentLoan,referent,
              if access = .shared then .shared else .unique,root.region,true,
              .storageBorrow,authority.guardLoans before,false,some custody⟩
          nextLoan := before.nextLoan+1 }

/-- Whole allocation handoff transfers custody, not T and not reference
identity. Keeping the node preserves existing child loans. Actual input
resolution checks the previous custodian; the old recipient's historical
binding cannot pass that check after this transition. -/
inductive TransfersAllocation (recipient : ClaimCustody) :
    World → ResolvedPlace → World → Prop where
  | transfer {before place identity loan} : place.authority = .loan identity →
      AllocationClaim before place.authority place.address →
      before.loans.get identity = some loan →
      TransfersAllocation recipient before place
        { before with loans := before.loans.set identity { loan with custody := some recipient } }

/-- Moving an erased storage-loan handle is distinct from consuming T through
that loan. Unique handles transfer custody; a shared view may be copied, just
like an ordinary shared reference handle. Neither operation creates a loan. -/
inductive TransfersStorageLoan (recipient : ClaimCustody) :
    World → ResolvedPlace → World → Prop where
  | unique {before place identity loan} : place.authority = .loan identity →
      before.loans.get identity = some loan → loan.live = true →
      loan.kind = .storageBorrow → loan.mode = .unique → loan.referent = place.address →
      TransfersStorageLoan recipient before place
        { before with loans := before.loans.set identity { loan with custody := some recipient } }
  | shared {before place backing identity loan} : place.authority = .shared backing →
      backing.parentLoan = some identity → before.loans.get identity = some loan →
      loan.live = true → loan.kind = .storageBorrow → loan.mode = .shared →
      loan.referent = place.address →
      TransfersStorageLoan recipient before place before

/-- Opening allocation ownership under a carrier borrow requires a fresh
owning view so its new guard dependencies remain acyclic. This cannot be
manufactured from pointer provenance or an ordinary pointee loan. -/
inductive ClaimsAllocation (recipient : ClaimCustody) :
    World → Authority → Address → Identity → World → Prop where
  | claim {before authority address root} : AllocationClaim before authority address →
      Permitted before authority .owned address → before.root address = some root →
      ClaimsAllocation recipient before authority address before.nextLoan
        { before with
          loans := before.loans.set before.nextLoan
            ⟨before.nextLoan,authority.parentLoan,address,.unique,root.region,true,
              .owning,authority.guardLoans before,false,some recipient⟩
          nextLoan := before.nextLoan+1 }

def ClaimedAuthority (access : Access) (identity : Identity) : Authority :=
  if access = .shared then .shared (.loan identity) else .loan identity

/-- Leaving a custodian cannot discard an exact owning obligation. A real
whole-place owning child records its transfer to another recipient; an active
borrow, an address copy, or a disjoint partial claim is not that discharge.
The child remains in the same exclusion tree, so historical parent bindings
cannot regain permission merely because the old activation exits. -/
def World.CustodyHandedOff (world : World) (custody : ClaimCustody) : Prop :=
  ∀ identity loan, world.loans.get identity = some loan → loan.live = true →
    loan.kind = .owning → loan.custody = some custody →
    ∃ child successor, world.loans.get child = some successor ∧
      successor.parent = some identity ∧ successor.live = true ∧
      successor.kind = .owning ∧ successor.referent = loan.referent ∧
      ∃ recipient, successor.custody = some recipient ∧ recipient ≠ custody

/-- Relinquishment schedules the storage borrows of this custody for return;
all other loan fields and every physical storage root remain unchanged. -/
def World.RequestReturns (world : World) (custody : ClaimCustody) : World :=
  { world with loans := world.loans.map fun entry =>
      (entry.1,if entry.2.custody = some custody ∧ entry.2.kind = .storageBorrow then
        { entry.2 with returnRequested := true } else entry.2) }


/-- This is the resource analogue of scheduling ordinary input cleanup.
It records actual relinquishment of this invocation's lent storage inputs.
Dependent references can postpone loan completion, but owning obligations
must already have been transferred or physically released. -/
inductive RelinquishesCustody : World → ClaimCustody → World → Prop where
  | relinquish {before custody} : before.CustodyHandedOff custody →
      RelinquishesCustody before custody (before.RequestReturns custody)

/-- The actual resource handoff requests return when it relinquishes a lent
input. A dependent outgoing reference can delay completion of that request. -/
inductive RequestsStorageReturn : World → Identity → World → Prop where
  | request {before id loan} : before.loans.get id = some loan → loan.live = true →
      loan.kind = .storageBorrow →
      RequestsStorageReturn before id
        { before with loans := before.loans.set id { loan with returnRequested := true } }

/-- Only an explicitly requested storage-borrow return can complete without
an initialized-T restoration proof. Owning claims cannot enter this lifecycle. -/
inductive ReturnsStorageLoan : World → Identity → World → Prop where
  | returned {before id loan} : before.loans.get id = some loan → loan.live = true →
      loan.kind = .storageBorrow → loan.returnRequested = true → ¬ before.References id →
      ¬ before.ResourceReferences id →
      (∀ child, before.loans.get child.identity = some child →
        child.parent = some id ∨ id ∈ child.guards → child.live = false) →
      ReturnsStorageLoan before id { before with loans := before.loans.set id { loan with live := false } }

inductive EndsLoan (program : RuntimeProgram) : World → Identity → World → Prop where
  | restored {before id loan} : before.loans.get id = some loan → loan.live = true →
      (loan.kind = .restoring ∨ loan.kind = .destructor) →
      before.Initialized loan.referent →
      (loan.kind = .restoring → before.ResourcesClosed program loan.referent) → ¬ before.References id →
      ¬ before.ResourceReferences id →
      (∀ child, before.loans.get child.identity = some child →
        child.parent = some id ∨ id ∈ child.guards → child.live = false) →
      EndsLoan program before id { before with loans := before.loans.set id { loan with live := false } }

/-- Allocation retirement discharges the current owning claim and its retained
ownership ancestors together. A live ordinary or raw-storage borrow forbids
release. The discharged set is closed under live guard dependencies: releasing
an allocation cannot leave an external access dependent on its dead owner.
This changes neither a generation nor a home; actual storage retirement remains
a separate transition after the claim obligation has been consumed. -/
structure ReleasesStorageClaimsReady (before : World) (place : ResolvedPlace) : Prop where
  claim : ∃ id owner, place.authority = .loan id ∧ before.loans.get id = some owner ∧
    owner.live = true ∧ owner.kind = .owning ∧ ¬ before.ResourceReferences id
  whole : place.address.fields = []
  permission : Permitted before place.authority .owned place.address
  safe : ∀ key loan, before.loans.get key = some loan → loan.live = true →
    loan.referent.root = place.address.root → loan.kind = .owning ∧
      ¬ before.References key ∧ ¬ before.ResourceReferences key
  dependencies : ∀ key loan guard carrier, before.loans.get key = some loan → loan.live = true →
    guard ∈ loan.guards → before.loans.get guard = some carrier →
    carrier.referent.root = place.address.root → loan.referent.root = place.address.root

inductive ReleasesStorageClaims : World → ResolvedPlace → World → Prop where
  | release {before place} : ReleasesStorageClaimsReady before place →
      ReleasesStorageClaims before place
        { before with loans := before.loans.map fun (key,loan) =>
          (key,if loan.referent.root = place.address.root then { loan with live := false } else loan) }

theorem ReleasesStorageClaims.ready {before after : World} {place : ResolvedPlace}
    (released : ReleasesStorageClaims before place after) : ReleasesStorageClaimsReady before place := by
  cases released with
  | release ready => exact ready

theorem ReleasesStorageClaimsReady.progress {before : World} {place : ResolvedPlace}
    (ready : ReleasesStorageClaimsReady before place) : ∃ after, ReleasesStorageClaims before place after :=
  ⟨_,.release ready⟩

inductive Deconstructs (program : RuntimeProgram) (context : Context) : World → Authority → Address → World → Prop where
  | shell {before authority address value after} : before.Stores address value → value.shellLive = true →
      Permitted before authority .owned address → value.ResourcesAccessible program before .owned →
      (value.head = .tuple ∨ value.head = .array ∨
        ∃ id data variant args, program.declarations.Constructor id data variant ∧ value.type = .nominal data.header.id args ∧
          value.head = .constructor id ∧ data.dropHook = none ∧
          (data.nonExhaustive = true → context.module.package = data.header.module.package) ∧
          ∀ field ∈ variant.fields, Visible field.header context.module) →
      before.write address (some (.resident value.owner value.type value.head false value.fields value.resources)) = some after →
      Deconstructs program context before authority address after

def DropHook (program : Program) (type : Term) (hook : Option DeclId) : Prop :=
  (∃ id args data, type = .nominal id args ∧ program.data id = some data ∧ data.dropHook = hook) ∨
  ((∀ id args, type ≠ .nominal id args) ∧ hook = none)

def MayDispose (program : Program) (value : Value) : Prop :=
  ∀ path resident, ResidentAt value path resident →
    (resident.shellLive = true → ∃ principal, PrincipalOf program resident.type principal ∧ principal.MayDiscard) ∧
    (∀ hook, DropHook program resident.type (some hook) → resident.Initialized)

def CanEndStorage (world : World) (rootId : Identity) : Prop :=
  (∀ id loan, world.loans.get id = some loan → loan.live = true → loan.referent.root ≠ rootId) ∧
  (∀ id available, world.availability.get id = some available → available.active = true →
    ∀ place ∈ available.reserved, place.address.root ≠ rootId) ∧
  /- Captured storage remains owned by its active suspension. Final replay
  and cancellation must restore that ownership before ordinary retirement. -/
  (∀ root, world.roots.get rootId = some root → ∀ suspension, root.home ≠ .suspended suspension)

theorem CanEndStorage.sameHomes {before after : World} {id : Identity}
    (safe : CanEndStorage before id)
    (homes : (after.roots.get id).map Root.home = (before.roots.get id).map Root.home)
    (loans : after.loans = before.loans) (availability : after.availability = before.availability) :
    CanEndStorage after id := by
  refine ⟨by simpa only [loans] using safe.1,by simpa only [availability] using safe.2.1,?_⟩
  intro root found suspension
  rw [found] at homes
  obtain ⟨original,selected,equal⟩ := Option.map_eq_some_iff.mp homes.symm
  exact equal ▸ safe.2.2 original selected suspension

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

/-- A phase may create lifetimes without invalidating earlier lifetime
references. Input observation needs this monotone boundary, not table identity. -/
structure World.RegionExtension (before after : World) : Prop where
  regions : ∀ region ∈ before.liveRegions, region ∈ after.liveRegions
  frontier : before.nextRegion ≤ after.nextRegion

theorem World.RegionExtension.of_eq {before after : World}
    (regions : after.liveRegions = before.liveRegions) (frontier : after.nextRegion = before.nextRegion) :
    before.RegionExtension after :=
  ⟨fun _ member => by rw [regions]; exact member,Nat.le_of_eq frontier.symm⟩

theorem World.RegionExtension.refl (world : World) : world.RegionExtension world := .of_eq rfl rfl


def FreshRegion (before : World) (region : Identity) (after : World) : Prop :=
  region = before.nextRegion ∧ after = { before with
    liveRegions := region :: before.liveRegions, nextRegion := region+1 }

theorem FreshRegion.regionExtension {before after : World} {region : Identity}
    (fresh : FreshRegion before region after) : before.RegionExtension after := by
  obtain ⟨rfl,rfl⟩ := fresh
  exact ⟨fun _ member => List.mem_cons_of_mem _ member,Nat.le_succ _⟩

def Suspensible (program : RuntimeProgram) (world : World) (roots : List Identity) : Prop :=
  (∀ id loan, world.loans.get id = some loan → loan.live = true →
    (loan.kind = .restoring ∨ loan.kind = .destructor) →
    (loan.referent.root ∈ roots ∨ ∃ address value, address.root ∈ roots ∧ world.Resident address value ∧ value.head = .reference id) →
    world.Initialized loan.referent ∧ world.ResourcesClosed program loan.referent) ∧
  (∀ address value, address.root ∈ roots → world.Resident address value →
    value.ResourcesClosed program world ∧ value.LoansRestored program world)

def Cancelable (program : RuntimeProgram) (world : World) (roots : List Identity) : Prop :=
  Suspensible program world roots ∧ ∀ address value, address.root ∈ roots → world.Resident address value → MayDispose program.declarations value

def Replayable (program : RuntimeProgram) (world : World) (roots : List Identity) : Prop :=
  Suspensible program world roots ∧
  (∀ address value, address.root ∈ roots → world.Resident address value →
    (value.shellLive = true → PrincipalOf program.declarations value.type .duplicable) ∧
    (∀ brand, value.head ≠ .label brand) ∧ (∀ id, value.head ≠ .available id) ∧
    (∀ binding ∈ value.resources, binding.ReadOnly)) ∧
  (∀ address value id loan, address.root ∈ roots → world.Resident address value → value.head = .reference id →
    world.loans.get id = some loan → loan.mode = .shared) ∧
  (∀ id loan, world.loans.get id = some loan → loan.live = true → loan.referent.root ∈ roots → loan.mode = .shared)

theorem hole_cannot_end {program : RuntimeProgram} {before after : World} {id loan}
    (found : before.loans.get id = some loan) (hole : ¬ before.Initialized loan.referent) : ¬ EndsLoan program before id after := by
  intro ended
  cases ended with
  | restored selected _ _ initialized _ _ _ _ =>
    have same : loan = _ := Option.some.inj (found.symm.trans selected)
    subst same
    exact hole initialized

theorem move_preserves_owner {program : RuntimeProgram} {before after : World} {authority source destination value}
    (found : before.Stores source value) (moved : Transfers program before authority source destination after) :
    ∃ cleared, before.write source none = some cleared ∧ cleared.write destination (some value) = some after := by
  cases moved with
  | move selected _ _ _ _ _ _ clear install =>
    have same := Option.some.inj (found.symm.trans selected)
    subst same
    exact ⟨_,clear,install⟩

/-- The section 7.5 boundary is a consequence of the real move producer,
including references nested arbitrarily deeply in stored aggregates. -/
theorem Transfers.loansRestored {program : RuntimeProgram} {before after : World}
    {authority : Authority} {source destination : Address} {value : Value}
    (moved : Transfers program before authority source destination after) (stored : before.Stores source value) :
    value.LoansRestored program before := by
  cases moved with
  | move selected _ ready _ _ _ _ _ _ =>
      have same := Option.some.inj (stored.symm.trans selected)
      subst same
      exact ready.1.2.1

theorem Transfers.reachable_reference_initialized {program : RuntimeProgram} {before after : World}
    {authority : Authority} {source destination : Address} {value : Value} {identity : Identity} {loan : Loan}
    (moved : Transfers program before authority source destination after) (stored : before.Stores source value)
    {base current : Authority} {incoming access : Access}
    (reachable : value.ReachableReference before base incoming identity current access)
    (found : before.loans.get identity = some loan) :
    before.Initialized loan.referent := by
  obtain ⟨_,_,rebased⟩ := reachable.rebase .owner .shared
  obtain ⟨actual,selected,_,initialized,_⟩ := moved.loansRestored stored identity _ _ rebased
  have same := Option.some.inj (found.symm.trans selected)
  subst actual
  exact initialized

end Glorious.Language
