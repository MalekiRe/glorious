import GloriousLanguage.Effects

/-! Typed residents are authoritative. Defined object bytes are a view of
those residents plus untyped backing bytes; padding is never promoted to a
semantic value. Raw operations must preserve logical ownership separately
from relocation of bits, including for zero-sized residents. -/
namespace Glorious.Language.Memory

open Kernel Execution

def integerBytes (endian : Endianness) (width value : Nat) : List Nat :=
  let little := (List.range width).map (fun index => value / 256^index % 256)
  match endian with | .little => little | .big => little.reverse

def ScalarValue.bytes (target : TargetProfile) : ScalarValue → List Nat
  | .integer _ width n => integerBytes target.endian (width.bits target / 8)
      (n % (2^width.bits target : Int)).toNat
  | .floating width bits => integerBytes target.endian (if width = .single then 4 else 8) bits
  | .character scalar => integerBytes target.endian 4 scalar

structure RuntimeAddresses where
  callable : DeclId → List Term → Nat
  continuation : Identity → Nat
  codeIdentity : Identity

inductive FieldOffset (program : Language.Program) (world : World) :
    Address → Term → Nat → Term → Nat → Prop where
  | tuple {address fields index type layouts layout offset} : fields[index]? = some type →
      ListRel (LayoutOf program ⟨[],[],0,default,false⟩) fields layouts → AggregateLayout layouts layout →
      layout.offsets[index]? = some offset → FieldOffset program world address (.tuple fields) index type offset
  | bindings {address brand region fields index type layouts layout offset} : fields[index]? = some type →
      ListRel (LayoutOf program ⟨[],[],0,default,false⟩) fields layouts → AggregateLayout layouts layout →
      layout.offsets[index]? = some offset → FieldOffset program world address (.bindings brand region fields) index type offset
  | callable {address id arguments fields index type layouts layout offset} : CallableFields program id arguments fields →
      fields[index]? = some type → ListRel (LayoutOf program ⟨[],[],0,default,false⟩) fields layouts →
      AggregateLayout (program.input.target.codeIdentityLayout :: layouts) layout →
      layout.offsets[index+1]? = some offset → FieldOffset program world address (.callable id arguments) index type offset
  | array {address element sign width count index layout} : 0 ≤ count → index < count.toNat →
      LayoutOf program ⟨[],[],0,default,false⟩ element layout →
      FieldOffset program world address (.array element (.constant (.integer sign width count))) index element
        (index * alignUp layout.size layout.alignment)
  | nominal {address id arguments data variant substitution types index type layout offset value} :
      program.Constructor variant.header.id data variant → data.header.id = id →
      Instantiates data.generics arguments substitution → ListRel (Substitutes substitution) (variant.fields.map (·.type)) types →
      types[index]? = some type → LayoutOf program ⟨[],[],0,data.header.module,false⟩ (.nominal id arguments) layout →
      world.Stores address value → value.head = .constructor variant.header.id →
      (data.isEnum = false ∧ layout.offsets[index]? = some offset ∨
        ∃ (tag : Nat) (offsets : List Nat), data.variants[tag]? = some variant ∧ layout.variants[tag]? = some offsets ∧ offsets[index]? = some offset) →
      FieldOffset program world address (.nominal id arguments) index type offset

inductive AddressOffset (program : Language.Program) (world : World) : Address → Term → Nat → Prop where
  | root {id root} : world.roots.get id = some root → root.live = true →
      AddressOffset program world ⟨id,root.generation,[]⟩ root.type 0
  | child {address container offset index type childOffset} : AddressOffset program world address container offset →
      FieldOffset program world address container index type childOffset →
      AddressOffset program world (address.child index) type (offset+childOffset)

def PhysicalAddress (program : Language.Program) (world : World) (address : Address) (type : Term) (physical : Nat) : Prop :=
  Addressable program ⟨[],[],0,default,false⟩ type ∧
  ∃ root offset, world.root address = some root ∧ AddressOffset program world address type offset ∧ physical = root.base + offset

def PointsTo (program : Language.Program) (world : World) (pointer : RawPointer) (address : Address) (type : Term) : Prop :=
  pointer.allocation = some address.root ∧ pointer.generation = address.generation ∧
  PhysicalAddress program world address type pointer.address ∧
  ∃ root offset, world.root address = some root ∧ AddressOffset program world address type offset ∧ pointer.offset = offset ∧
    (∃ domain, pointer.domain = some domain ∧ (root.home = .allocation domain ∨ root.home = .external domain))

mutual
  inductive Encodes (program : Language.Program) (world : World) (runtime : RuntimeAddresses) :
      Address → Value → Layout → List (Option Nat) → Prop where
    | unit {address owner} : Encodes program world runtime address (.resident owner .unit .unit true []) ⟨0,1,[],0,0,[]⟩ []
    | scalar {address owner scalar layout} : scalar.Valid program.input.target →
        LayoutOf program ⟨[],[],0,default,false⟩ (.scalar scalar.type) layout →
        Encodes program world runtime address (.resident owner (.scalar scalar.type) (.scalar scalar) true []) layout
          ((ScalarValue.bytes program.input.target scalar).map some)
    | pointer {address owner mode type pointer layout} : LayoutOf program ⟨[],[],0,default,false⟩ (.rawPointer mode type) layout →
        pointer.address < 2^program.input.target.pointerBits →
        Encodes program world runtime address (.resident owner (.rawPointer mode type) (.pointer pointer) true []) layout
          ((integerBytes program.input.target.endian layout.size pointer.address).map some)
    | reference {address owner mode region type id loan physical layout} : world.loans.get id = some loan → loan.live = true →
        loan.mode = mode → PhysicalAddress program world loan.referent type physical → world.Initialized loan.referent →
        LayoutOf program ⟨[],[],0,default,false⟩ (.reference mode region type) layout →
        Encodes program world runtime address (.resident owner (.reference mode region type) (.reference id) true []) layout
          ((integerBytes program.input.target.endian layout.size physical).map some)
    | aggregate {address value layout bytes} :
        (value.head = .tuple ∨ value.head = .array ∨ ∃ variant, value.head = .constructor variant) →
        LayoutOf program ⟨[],[],0,default,false⟩ value.type layout → bytes.length = layout.size →
        EncodesFields program world runtime address value.type 0 value.fields bytes →
        (∀ id data variant arguments index, value.head = .constructor id → value.type = .nominal data.header.id arguments →
          program.Constructor id data variant → data.isEnum = true → data.variants[index]? = some variant →
          bytes.take layout.tagBytes = (integerBytes program.input.target.endian layout.tagBytes index).map some) →
        (∀ (index byte : Nat), bytes[index]? = some (some byte) → byte < 256) →
        Encodes program world runtime address value layout bytes
    | callable {address owner id arguments fields layout bytes} :
        LayoutOf program ⟨[],[],0,default,false⟩ (.callable id arguments) layout → bytes.length = layout.size →
        runtime.callable id arguments < 256^program.input.target.codeIdentityLayout.size →
        bytes.take program.input.target.codeIdentityLayout.size =
          (integerBytes program.input.target.endian program.input.target.codeIdentityLayout.size (runtime.callable id arguments)).map some →
        EncodesFields program world runtime address (.callable id arguments) 0 fields bytes →
        Encodes program world runtime address (.resident owner (.callable id arguments) (.callable id arguments) true fields) layout bytes
    | operation {address owner id arguments operation layout bytes} : program.operation id = some operation →
        LayoutOf program ⟨[],[],0,default,false⟩ (.callable id arguments) layout → bytes.length = layout.size →
        runtime.callable id arguments < 256^program.input.target.codeIdentityLayout.size →
        bytes.take program.input.target.codeIdentityLayout.size =
          (integerBytes program.input.target.endian program.input.target.codeIdentityLayout.size (runtime.callable id arguments)).map some →
        Encodes program world runtime address (.resident owner (.callable id arguments) (.operation id arguments) true []) layout bytes
    | continuation {address owner brand argument answer effects quantity id} :
        runtime.continuation id < 256^program.input.target.continuationLayout.size →
        Encodes program world runtime address
          (.resident owner (.continuation brand argument answer effects quantity) (.continuation id) true [])
          program.input.target.continuationLayout
          ((integerBytes program.input.target.endian program.input.target.continuationLayout.size (runtime.continuation id)).map some)
    | bindings {address owner brand region fields id types layout bytes} :
        LayoutOf program ⟨[],[],0,default,false⟩ (.bindings brand region types) layout → bytes.length = layout.size →
        EncodesFields program world runtime address (.bindings brand region types) 0 fields bytes →
        Encodes program world runtime address (.resident owner (.bindings brand region types) (.bindings id) true fields) layout bytes
    | proof {address value} : value.fields = [] → value.shellLive = true →
        ((∃ brand region result, value.head = .label brand ∧ value.type = .label (.rigid brand .brand 0) region result) ∨
         (∃ id brand region, value.head = .available id ∧ value.type = .available brand region)) →
        Encodes program world runtime address value ⟨0,1,[],0,0,[]⟩ []

  inductive EncodesFields (program : Language.Program) (world : World) (runtime : RuntimeAddresses) :
      Address → Term → Nat → List (Option Value) → List (Option Nat) → Prop where
    | nil {address type index bytes} : EncodesFields program world runtime address type index [] bytes
    | hole {address type index fields bytes child offset layout} :
        FieldOffset program world address type index child offset → LayoutOf program ⟨[],[],0,default,false⟩ child layout →
        (bytes.drop offset).take layout.size = List.replicate layout.size none →
        EncodesFields program world runtime address type (index+1) fields bytes →
        EncodesFields program world runtime address type index (none :: fields) bytes
    | resident {address type index value fields bytes offset layout childBytes} :
        FieldOffset program world address type index value.type offset →
        Encodes program world runtime (address.child index) value layout childBytes →
        (bytes.drop offset).take layout.size = childBytes →
        EncodesFields program world runtime address type (index+1) fields bytes →
        EncodesFields program world runtime address type index (some value :: fields) bytes
end

def OccupiesByte (program : Language.Program) (world : World) (root : Identity) (offset : Nat) : Prop :=
  ∃ address value relative layout,
    address.root = root ∧ world.Resident address value ∧ AddressOffset program world address value.type relative ∧
    LayoutOf program ⟨[],[],0,default,false⟩ value.type layout ∧
    relative ≤ offset ∧ offset < relative+layout.size ∧
    (value.head = .unit ∨ (∃ scalar, value.head = .scalar scalar) ∨ (∃ pointer, value.head = .pointer pointer) ∨
      (∃ loan, value.head = .reference loan) ∨
      (∃ id args, (value.head = .callable id args ∨ value.head = .operation id args) ∧ offset-relative < program.input.target.codeIdentityLayout.size) ∨
      (∃ id, value.head = .continuation id) ∨
      ∃ variant, value.head = .constructor variant ∧ offset-relative < layout.tagBytes)

def ObjectBytes (program : Language.Program) (world : World) (runtime : RuntimeAddresses)
    (id : Identity) (bytes : List (Option Nat)) : Prop :=
  ∃ root, world.roots.get id = some root ∧ root.live = true ∧ bytes.length = root.layout.size ∧
    ((root.value = none ∧ bytes = root.bytes) ∨
      ∃ value, root.value = some value ∧ Encodes program world runtime ⟨id,root.generation,[]⟩ value root.layout bytes ∧
        ∀ offset, ¬ OccupiesByte program world id offset → bytes[offset]? = some none)

inductive AllocatesBuffer (program : Language.Program) :
    World → Identity → Term → Nat → Nat → RawPointer → World → Prop where
  | fresh {before domain element count base elementLayout layout} :
      domain ∈ program.input.manifest.allocationDomains → LayoutOf program ⟨[],[],0,default,true⟩ element elementLayout →
      ArrayLayout elementLayout count layout → layout.size ≤ program.input.target.maximumObjectBytes →
      0 < base → base % layout.alignment = 0 → base+layout.size < 2^program.input.target.pointerBits →
      DisjointStorage before base layout.size →
      AllocatesBuffer program before domain element count base ⟨base,some before.nextRoot,0,0,some domain⟩
        { before with roots := before.roots.set before.nextRoot ⟨.allocation domain,0,before.nextRegion,base,layout, .array element (.constant (.integer false .pointer count)), some (.resident before.nextOwner (.array element (.constant (.integer false .pointer count))) .array false (List.replicate count none)),true,before.clock,true,List.replicate layout.size none⟩, liveRegions := before.nextRegion :: before.liveRegions, nextRegion := before.nextRegion+1, nextRoot := before.nextRoot+1, nextOwner := before.nextOwner+1, clock := before.clock+1 }

def PointerOffset (program : Language.Program) (world : World) (pointer : RawPointer) (bytes : Int) (result : RawPointer) : Prop :=
  ∃ id root offset,
    pointer.allocation = some id ∧ world.roots.get id = some root ∧ root.live = true ∧ root.generation = pointer.generation ∧
    0 ≤ Int.ofNat pointer.offset+bytes ∧ offset = (Int.ofNat pointer.offset+bytes).toNat ∧ offset ≤ root.layout.size ∧
    root.base+offset < 2^program.input.target.pointerBits ∧ result = { pointer with address := root.base+offset, offset := offset }

def AddressOnly (integer : Nat) : RawPointer := ⟨integer,none,0,0,none⟩

def WithAddress (program : Language.Program) (world : World) (pointer : RawPointer) (address : Nat) (result : RawPointer) : Prop :=
  ∃ id root,
    pointer.allocation = some id ∧ world.roots.get id = some root ∧ root.live = true ∧ root.generation = pointer.generation ∧
    root.base ≤ address ∧ address ≤ root.base+root.layout.size ∧ address < 2^program.input.target.pointerBits ∧
    result = { pointer with address := address, offset := address-root.base }

inductive RawRead (program : Language.Program) : World → RawPointer → Term → Bool → Address → World → Prop where
  | read {before pointer type copy source destination after layout} : PointsTo program before pointer source type →
      LayoutOf program ⟨[],[],0,default,true⟩ type layout → RawRange program before pointer layout.size layout.alignment →
      (copy = true ∧ Copies program before .owner source destination after ∨
        copy = false ∧ Transfers before .owner source destination after) →
      RawRead program before pointer type copy destination after

inductive RawWrite (program : Language.Program) : World → Address → RawPointer → Term → World → Prop where
  | write {before source pointer type destination after layout value} : before.Stores source value → value.type = type →
      PointsTo program before pointer destination type → LayoutOf program ⟨[],[],0,default,true⟩ type layout →
      RawRange program before pointer layout.size layout.alignment → Transfers before .owner source destination after →
      RawWrite program before source pointer type after

inductive RawBorrow (program : Language.Program) :
    World → RawPointer → Term → Mutability → Identity → Address → World → Prop where
  | borrow {before pointer type mode region source destination after layout} : PointsTo program before pointer source type →
      LayoutOf program ⟨[],[],0,default,true⟩ type layout → RawRange program before pointer layout.size layout.alignment →
      before.Initialized source → Borrows program before .owner mode region source destination after →
      RawBorrow program before pointer type mode region destination after

def Slots (base : Address) (start count : Nat) : List Address :=
  (List.range count).map (fun index => base.child (start+index))

inductive InstallsResidents : World → List Address → List (Option Value) → World → Prop where
  | nil {world} : InstallsResidents world [] [] world
  | hole {before address addresses residents after} : before.Vacant address →
      InstallsResidents before addresses residents after → InstallsResidents before (address :: addresses) (none :: residents) after
  | resident {before address addresses value residents middle after} : before.Vacant address →
      before.write address (some value) = some middle → InstallsResidents middle addresses residents after →
      InstallsResidents before (address :: addresses) (some value :: residents) after

/-- Reads all sources before clearing, then writes the preserved snapshot.
Destination overlap is legal only with the source range; unrelated initialized
owners cannot be overwritten. This is relocation, never implicit Copy. -/
def BulkMove (before : World) (sources destinations : List Address) (after : World) : Prop :=
  ∃ residents cleared,
    sources.length = destinations.length ∧ sources.Nodup ∧ destinations.Nodup ∧
    ListRel (fun address value => before.read address = value) sources residents ∧
    (∀ address ∈ sources, Permitted before .owner .owned address) ∧
    (∀ address ∈ destinations, address ∈ sources ∨ before.Vacant address) ∧
    Clears before sources cleared ∧ InstallsResidents cleared destinations residents after

inductive ReleasesBuffer (program : Language.Program) : World → RawPointer → Identity → World → Prop where
  | release {before pointer domain id root value cleared retired} : pointer.allocation = some id → pointer.offset = 0 →
      pointer.domain = some domain → before.roots.get id = some root → root.live = true →
      root.home = .allocation domain → root.generation = pointer.generation → root.base = pointer.address →
      root.value = some value → value.shellLive = false → (∀ field ∈ value.fields, field = none) →
      CanEndStorage before id → before.write ⟨id,root.generation,[]⟩ none = some cleared → Retires cleared id retired →
      ReleasesBuffer program before pointer domain
        { retired with liveRegions := retired.liveRegions.filter (· != root.region) }

def ReallocatesBuffer (program : Language.Program) (before : World) (old : RawPointer)
    (domain : Identity) (element : Term) (newCount base : Nat) (result : RawPointer) (after : World) : Prop :=
  ∃ oldId root value allocated newId moved oldCount,
    old.allocation = some oldId ∧ before.roots.get oldId = some root ∧ root.value = some value ∧
    oldCount = value.fields.length ∧ value.shellLive = false ∧ oldCount ≤ newCount ∧
    CanEndStorage before oldId ∧ AllocatesBuffer program before domain element newCount base result allocated ∧
    result.allocation = some newId ∧
    BulkMove allocated (Slots ⟨oldId,root.generation,[]⟩ 0 oldCount) (Slots ⟨newId,0,[]⟩ 0 oldCount) moved ∧
    ReleasesBuffer program moved old domain after

structure AllocationContract where
  domain : Identity
  allocate : DeclId
  reallocate : Option DeclId
  release : DeclId

def AllocationContract.Valid (program : Language.Program) (contract : AllocationContract) : Prop :=
  contract.domain ∈ program.input.manifest.allocationDomains ∧
  (∃ binding ∈ program.input.manifest.bindings, binding.declaration = contract.allocate ∧
    binding.domain = some contract.domain ∧ binding.primitive = some .allocate) ∧
  (∃ binding ∈ program.input.manifest.bindings, binding.declaration = contract.release ∧
    binding.domain = some contract.domain ∧ binding.primitive = some .release)

theorem address_integer_has_no_provenance {program : Language.Program} {world : World}
    {integer address type} : ¬ PointsTo program world (AddressOnly integer) address type := by
  intro points
  cases points.1

theorem vacant_release_has_no_live_loan {program : Language.Program} {before after : World}
    {pointer domain id loan} (released : ReleasesBuffer program before pointer domain after)
    (allocation : pointer.allocation = some id) (found : before.loans.get loan.identity = some loan)
    (live : loan.live = true) : loan.referent.root ≠ id := by
  cases released with
  | release selected _ _ _ _ _ _ _ _ _ _ safe _ _ =>
    have same := Option.some.inj (allocation.symm.trans selected)
    subst same
    exact safe loan.identity loan found live

end Glorious.Language.Memory
