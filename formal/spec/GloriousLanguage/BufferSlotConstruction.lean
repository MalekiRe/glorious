import GloriousLanguage.BufferReallocationFraming
import GloriousLanguage.HeadStructure
import GloriousLanguage.LayoutContext
import GloriousLanguage.ProjectionStorage

/-! Buffer movement consumes the actual array resident's child snapshot.
Its slot geometry and declared array layout construct the existing bulk-move
inputs and destination typing, including holes and zero-sized elements. -/
namespace Glorious.Language

theorem Address.child_not_overlaps {address : Address} {first last : Nat} (different : first ≠ last) :
    ¬ (address.child first).Overlaps (address.child last) := by
  rintro ⟨_,_,⟨suffix,path⟩ | ⟨suffix,path⟩⟩
  · have same : [first] = [last] ++ suffix :=
      List.append_cancel_left (by simpa only [Address.child,List.append_assoc] using path)
    exact different (List.cons.inj same).1
  · have same : [last] = [first] ++ suffix :=
      List.append_cancel_left (by simpa only [Address.child,List.append_assoc] using path)
    exact different (List.cons.inj same).1.symm

theorem World.Stores.read_child {world : World} {address : Address} {value : Value}
    (stored : world.Stores address value) {index : Nat} {slot : Option Value}
    (selected : value.fields[index]? = some slot) : world.read (address.child index) = slot := by
  change world.read { address with fields := address.fields ++ [index] } = slot
  rw [World.read_append,stored]
  cases slot <;> simp [Value.atPath,selected]

theorem Typing.ValueTyped.array_children {program : Kernel.Program} {world : World} {value : Value}
    {element : Term} {count : Nat} (typed : Typing.ValueTyped program world value)
    (type : value.type = .array element (.constant (.integer false .pointer count))) :
    value.head = .array ∧ ∀ child, some child ∈ value.fields → child.type = element := by
  cases value with
  | resident owner actual head live values resources =>
    change actual = _ at type
    subst actual
    cases typed with
    | aggregate form fields =>
      rcases form with ⟨impossible,_⟩ | ⟨actual,sign,width,length,equal,_,head,_,elements⟩ | ⟨_,_,_,_,_,impossible,_⟩
      · cases impossible
      · have same := Term.array.inj equal
        cases same.1
        refine ⟨head,?_⟩
        intro child member
        obtain ⟨index,selected⟩ := List.mem_iff_getElem?.mp member
        exact elements child.type (List.mem_of_getElem? (fields.get selected).2)
      · cases impossible
    | continuation form =>
      obtain ⟨_,_,_,_,impossible⟩ := form
      cases impossible

namespace Memory

theorem AllocatesBuffer.created_buffer {program : Program} {before after : World}
    {custody : ClaimCustody} {allocation : ResolvedPlace} {domain : Identity}
    {element : Term} {count base : Nat} {pointer : RawPointer}
    (allocated : AllocatesBuffer program custody before domain element count base pointer allocation after) :
    ∃ value, BufferAt after allocation pointer domain value ∧
      value.type = .array element (.constant (.integer false .pointer count)) ∧
      value.fields = List.replicate count none ∧ value.shellLive = false ∧ value.resources = [] := by
  cases allocated
  exact ⟨_,⟨_,_,rfl,rfl,rfl,rfl,Table.get_set _ _ _,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl,rfl⟩

theorem BufferAt.allocated {program : Program} {before after : World}
    {custody : ClaimCustody} {allocation old : ResolvedPlace} {domain oldDomain : Identity}
    {element : Term} {count base : Nat} {pointer oldPointer : RawPointer} {value : Value}
    (valid : before.WellFormed)
    (allocated : AllocatesBuffer program custody before domain element count base pointer allocation after)
    (buffer : BufferAt before old oldPointer oldDomain value) : BufferAt after old oldPointer oldDomain value := by
  obtain ⟨id,root,allocationEq,offset,address,domainEq,found,live,home,generation,physical,contents⟩ := buffer
  exact ⟨id,root,allocationEq,offset,address,domainEq,allocated.roots valid found,live,home,generation,physical,contents⟩

theorem BufferAt.address_type {program : Kernel.Program} {world : World}
    {allocation : ResolvedPlace} {pointer : RawPointer} {domain : Identity} {value : Value}
    (typed : Typing.WorldTyped program world) (buffer : BufferAt world allocation pointer domain value) :
    AddressType program.declarations world allocation.address value.type := by
  obtain ⟨root,located,contents,_⟩ := buffer.root
  obtain ⟨found,live,generation⟩ := World.root_found located
  have type := typed.2.2.1 allocation.address.root root value found contents
  have address : allocation.address = ⟨allocation.address.root,root.generation,[]⟩ := by
    have eta : allocation.address = ⟨allocation.address.root,allocation.address.generation,allocation.address.fields⟩ := rfl
    rw [← generation,buffer.whole] at eta
    exact eta
  refine ⟨0,?_⟩
  rw [address,type]
  exact .root found live

theorem Slots.pairwise (address : Address) (start count : Nat) :
    (Slots address start count).Pairwise (fun first last => ¬ first.Overlaps last) := by
  apply List.pairwise_iff_getElem.mpr
  intro first last firstBound lastBound less
  simp only [Slots,List.getElem_map,List.getElem_range]
  exact Address.child_not_overlaps (by omega)

theorem Slots.resolved_at {address : Address} {authority : Authority} {start count index : Nat}
    {place : ResolvedPlace}
    (found : ((Slots address start count).map (fun address => (⟨address,authority⟩ : ResolvedPlace)))[index]? = some place) :
    index < count ∧ place = ⟨address.child (start+index),authority⟩ := by
  have bound : index < count := by
    obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp found
    simpa only [Slots,List.length_map,List.length_range] using bound
  simp only [Slots,List.getElem?_map,List.getElem?_range bound,Option.map_some,Option.some.injEq] at found
  exact ⟨bound,found.symm⟩

theorem Slots.resolved_member {address : Address} {authority : Authority} {start count : Nat}
    {place : ResolvedPlace}
    (member : place ∈ (Slots address start count).map (fun address => (⟨address,authority⟩ : ResolvedPlace))) :
    ∃ index, index < count ∧ place = ⟨address.child (start+index),authority⟩ := by
  obtain ⟨index,selected⟩ := List.mem_iff_getElem?.mp member
  exact ⟨index,Slots.resolved_at selected⟩

theorem Slots.snapshot {world : World} {allocation : ResolvedPlace} {value : Value}
    (stored : world.Stores allocation.address value) (count : Nat) (length : value.fields.length = count) :
    ListRel (fun (place : ResolvedPlace) slot => world.read place.address = slot)
      ((Slots allocation.address 0 count).map (fun address => ⟨address,allocation.authority⟩)) value.fields := by
  apply ListRel.of_at (by simp [Slots,length])
  intro index place slot atPlace atSlot
  obtain ⟨_,rfl⟩ := Slots.resolved_at atPlace
  simpa only [Nat.zero_add] using stored.read_child atSlot

theorem Slots.located {world : World} {allocation : ResolvedPlace} {value : Value}
    (stored : world.Stores allocation.address value) (count : Nat) (length : value.fields.length = count) :
    ∀ place ∈ (Slots allocation.address 0 count).map (fun address => (⟨address,allocation.authority⟩ : ResolvedPlace)),
      world.Located place.address := by
  intro place member
  obtain ⟨index,bounded,rfl⟩ := Slots.resolved_member member
  exact World.Located.child_iff.mpr ⟨value,stored,by simpa only [length,Nat.zero_add] using bounded⟩

/-- Positive source admission and the actual fresh allocation construct the
real move of every old slot. No successful move or later permission is an
input: all destination slots and access paths come from the allocator. -/
theorem ReallocationSourceReady.move_exists {program : Kernel.Program} {before after : World}
    {custody : ClaimCustody} {oldAllocation allocation : ResolvedPlace} {old pointer : RawPointer}
    {domain : Identity} {element : Term} {oldCount newCount base : Nat}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (ready : ReallocationSourceReady program before oldAllocation old domain element oldCount newCount)
    (allocated : AllocatesBuffer program.declarations custody before domain element newCount base pointer allocation after) :
    ∃ moved, BulkMove program after
      ((Slots oldAllocation.address 0 oldCount).map (fun address => ⟨address,oldAllocation.authority⟩))
      ((Slots allocation.address 0 oldCount).map (fun address => ⟨address,allocation.authority⟩)) moved := by
  obtain ⟨value,buffer,length,type,_,_,children⟩ := ready.source
  have oldBuffer := buffer.allocated typed.1 allocated
  have oldStored := oldBuffer.stores
  have oldSnapshot := Slots.snapshot oldStored oldCount length
  have childrenTyped := (World.stores_typed typed.roots buffer.stores).array_children type
  have afterTyped := allocated.worldTyped valid inventory typed
  obtain ⟨newValue,newBuffer,newType,newFields,_,_⟩ := allocated.created_buffer
  obtain ⟨offset,newOffset⟩ := newBuffer.address_type afterTyped
  rw [newType] at newOffset
  have newStored := newBuffer.stores
  have newPermission := allocated.owning_permission typed.1 .unique
  have oldPermission := allocated.permitted typed.1 ready.release_ready.permission
  have freshRoot : allocation.address.root = before.nextRoot := by cases allocated; rfl
  obtain ⟨oldRoot,oldAt,_,_⟩ := buffer.root
  have oldBound := World.root_bound typed.1 (World.root_found oldAt).1
  have different : oldAllocation.address.root ≠ allocation.address.root := by rw [freshRoot]; exact Nat.ne_of_lt oldBound
  have elementLayout : ∃ layout, LayoutOf program.declarations ⟨[],[],0,default,false,{}⟩ element layout := by
    cases allocated with
    | fresh request _ =>
      obtain ⟨layout,located,_⟩ := request.array_layout
      exact ⟨layout,located.runtime_context⟩
  obtain ⟨layout,elementLayout⟩ := elementLayout
  apply BulkMove.disjoint_exists
    (List.pairwise_map.mpr (Slots.pairwise oldAllocation.address 0 oldCount))
    (List.pairwise_map.mpr (Slots.pairwise allocation.address 0 oldCount)) ?_ oldSnapshot
    (Slots.located oldStored oldCount length) ?_ ?_ ?_
  · intro source present destination member overlap
    obtain ⟨_,_,rfl⟩ := Slots.resolved_member present
    obtain ⟨_,_,rfl⟩ := Slots.resolved_member member
    exact different overlap.1
  · intro source member
    obtain ⟨index,atSource⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨_,sourceEq⟩ := Slots.resolved_at atSource
    refine ⟨by simpa only [sourceEq] using oldPermission.child (0+index),?_⟩
    intro child stored
    obtain ⟨slot,selected,read⟩ := oldSnapshot.get_left atSource
    have same : slot = some child := read.symm.trans stored
    rw [same] at selected
    have childReady := children child (List.mem_of_getElem? selected)
    apply allocated.handoffReady typed.1
    refine ⟨childReady.1,?_⟩
    intro mutation member
    obtain ⟨place,present,rfl⟩ := List.mem_map.mp member
    rcases List.mem_append.mp present with sourceMember | destinationMember
    · obtain ⟨slot,_,rfl⟩ := Slots.resolved_member sourceMember
      intro support supported overlap
      exact childReady.2 oldAllocation.address (by simp) support supported
        ⟨overlap.1,overlap.2.1,Or.inr ⟨support.fields,by simp [buffer.whole]⟩⟩
    · obtain ⟨slot,_,rfl⟩ := Slots.resolved_member destinationMember
      exact childReady.1.supportOutside_fresh typed.1 (by simpa only [Address.child,freshRoot] using Nat.le_refl before.nextRoot)
  · intro destination member
    obtain ⟨index,_,rfl⟩ := Slots.resolved_member member
    exact newPermission.child (0+index)
  · apply ListRel.of_at (by simp [Slots,length])
    intro index destination slot atDestination atSlot
    obtain ⟨bounded,rfl⟩ := Slots.resolved_at atDestination
    have newBound : index < newCount := Nat.lt_of_lt_of_le bounded ready.growing
    have hole : newValue.fields[0+index]? = some none := by simp [newFields,newBound]
    refine ⟨newStored.vacant_child hole,?_⟩
    intro child same
    rw [same] at atSlot
    have childType := childrenTyped.2 child (List.mem_of_getElem? atSlot)
    rw [childType]
    exact ⟨offset+(0+index)*alignUp layout.size layout.alignment,
      .child newOffset (.array (by omega) (by simpa using newBound) elementLayout)⟩

end Memory
end Glorious.Language
