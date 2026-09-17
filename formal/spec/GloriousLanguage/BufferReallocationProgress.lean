import GloriousLanguage.BufferReallocationConstruction
import GloriousLanguage.BufferAllocationProgress

/-! Full raw-buffer growth progress at the actual primitive transition:
admitted physical storage constructs the typed returned pointer; exhausted
physical storage takes the explicit unchanged-world terminal resource step. -/
namespace Glorious.Language

theorem Clears.read_disjoint {before after : World} {addresses : List Address}
    (cleared : Clears before addresses after) {address : Address}
    (apart : ∀ mutation ∈ addresses, ¬ mutation.Overlaps address) : after.read address = before.read address := by
  induction cleared with
  | nil => rfl
  | cons written _ ih =>
    exact (ih (fun mutation member => apart mutation (List.mem_cons_of_mem _ member))).trans
      (World.write_disjoint written (apart _ List.mem_cons_self))

theorem Execution.DestinationType.frame {before after : World} {address : Address} {type : Term}
    (destination : Execution.DestinationType before address type)
    (locations : ∀ id, (after.roots.get id).map Root.location = (before.roots.get id).map Root.location)
    (read : after.read address = before.read address) : Execution.DestinationType after address type := by
  have empty := destination.vacant.read_none
  obtain ⟨whole,root,found,type,hole⟩ := destination
  obtain ⟨current,located,same⟩ := World.root_transport locations found
  have typeEq := congrArg Root.type same
  refine ⟨whole,current,located,typeEq.trans type,?_⟩
  simpa [World.read,located,whole,Value.atPath] using read.trans empty

theorem ReleasesStorageClaims.destinationType {before after : World} {allocation : ResolvedPlace}
    {destination : Address} {type : Term} (released : ReleasesStorageClaims before allocation after)
    (destinationType : Execution.DestinationType before destination type) :
    Execution.DestinationType after destination type := by
  cases released
  exact destinationType

namespace Memory

theorem BulkMove.read_disjoint {program : RuntimeProgram} {before after : World}
    {sources destinations : List ResolvedPlace} (moved : BulkMove program before sources destinations after)
    {address : Address} (apart : ∀ place ∈ sources ++ destinations, ¬ place.address.Overlaps address) :
    after.read address = before.read address := by
  obtain ⟨_,_,_,_,_,_,_,_,cleared,installed⟩ := moved
  exact (installed.read_disjoint (by
    intro mutation member
    obtain ⟨place,present,rfl⟩ := List.mem_map.mp member
    exact apart place (List.mem_append_right _ present))).trans (cleared.read_disjoint (by
      intro mutation member
      obtain ⟨place,present,rfl⟩ := List.mem_map.mp member
      exact apart place (List.mem_append_left _ present)))

/-- The snapshot's recursive resources remain accessible at the corresponding
destination, even when source and destination ranges overlap. The pending
write footprint comes from the actual move's original admission. -/
theorem BulkMove.handed_off_ready {program : RuntimeProgram} {before after : World}
    {sources destinations : List ResolvedPlace} {index : Nat} {source destination : ResolvedPlace} {value : Value}
    (moved : BulkMove program before sources destinations after)
    (sourceAt : sources[index]? = some source) (destinationAt : destinations[index]? = some destination)
    (stored : before.Stores source.address value) :
    after.Stores destination.address value ∧ value.ResourcesAccessible program after .owned := by
  have found := (moved.snapshot index source destination sourceAt destinationAt).trans stored
  have ready : value.MoveReady program before ((sources ++ destinations).map ResolvedPlace.address) := by
    obtain ⟨_,_,_,_,_,_,permissions,_,_,_⟩ := moved
    exact (permissions source (List.mem_of_getElem? sourceAt)).2 value stored
  have frame : value.SupportFramed before after := by
    intro address supported
    exact ⟨moved.read_disjoint (fun place member =>
      ready.2 place.address (List.mem_map.mpr ⟨place,member,rfl⟩) address supported),moved.locations address.root⟩
  have loans := congrArg World.loans moved.rest
  exact ⟨found,ready.1.frame (.of_locations moved.locations) loans frame⟩

/-- Original-world admission constructs overlap-aware relocation with exact
slot contents, preserved world typing and accessible relocated resources. -/
theorem BulkMove.typed_progress {program : Kernel.Program} {before : World}
    {sources destinations : List ResolvedPlace} {values : List (Option Value)}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (sourceApart : sources.Pairwise (fun first last => ¬ first.address.Overlaps last.address))
    (destinationApart : destinations.Pairwise (fun first last => ¬ first.address.Overlaps last.address))
    (paths : ∀ source ∈ sources, ∀ destination ∈ destinations, ¬ source.address.ProperPrefix destination.address)
    (snapshot : ListRel (fun source value => before.read source.address = value) sources values)
    (located : ∀ source ∈ sources, before.Located source.address)
    (permissions : ∀ source ∈ sources, Permitted before source.authority .owned source.address ∧
      ∀ value, before.Stores source.address value → value.MoveReady program before ((sources ++ destinations).map ResolvedPlace.address))
    (writable : ∀ destination ∈ destinations, Permitted before destination.authority .unique destination.address)
    (prepared : ListRel (fun destination resident =>
      (destination.address ∈ sources.map ResolvedPlace.address ∨ before.Vacant destination.address) ∧
      ∀ value, resident = some value → AddressType program.declarations before destination.address value.type) destinations values) :
    ∃ after, BulkMove program before sources destinations after ∧ Typing.WorldTyped program after ∧
      (∀ (index : Nat) (source destination : ResolvedPlace), sources[index]? = some source → destinations[index]? = some destination →
        after.read destination.address = before.read source.address) ∧
      (∀ (index : Nat) (source destination : ResolvedPlace) (value : Value),
        sources[index]? = some source → destinations[index]? = some destination → before.Stores source.address value →
          after.Stores destination.address value ∧ value.ResourcesAccessible program after .owned) := by
  obtain ⟨after,moved⟩ := BulkMove.exists sourceApart destinationApart paths snapshot located permissions writable prepared
  exact ⟨after,moved,moved.worldTyped valid inventory typed,moved.snapshot,
    fun _ _ _ _ sourceAt destinationAt stored => moved.handed_off_ready sourceAt destinationAt stored⟩

theorem BufferAt.destination_root_ne {before : World} {allocation : ResolvedPlace} {pointer : RawPointer}
    {domain : Identity} {value : Value} {destination : Address} {type : Term}
    (buffer : BufferAt before allocation pointer domain value)
    (empty : Execution.DestinationType before destination type) : allocation.address.root ≠ destination.root := by
  obtain ⟨root,atRoot,contents,_⟩ := buffer.root
  obtain ⟨_,other,atOther,_,hole⟩ := empty
  have found := (World.root_found atRoot).1
  have selected := (World.root_found atOther).1
  intro equal
  rw [equal] at found
  have same := Option.some.inj (found.symm.trans selected)
  rw [same,hole] at contents
  cases contents

theorem ReleasesBuffer.destinationType {program : Program} {before after : World}
    {allocation : ResolvedPlace} {pointer : RawPointer} {domain : Identity} {destination : Address} {type : Term}
    (released : ReleasesBuffer program before allocation pointer domain after)
    (destinationType : Execution.DestinationType before destination type) :
    Execution.DestinationType after destination type := by
  cases released with
  | release buffer _ _ _ _ claims _ written retired closed =>
    have different := buffer.destination_root_ne destinationType
    have unclaimedType := claims.destinationType destinationType
    have clearedType := unclaimedType.frame (World.write_locations written)
      (World.write_disjoint written (fun overlap => different overlap.1))
    obtain ⟨whole,root,found,type,hole⟩ := clearedType
    obtain ⟨_,rfl⟩ := closed
    exact ⟨whole,root,(retired.root_other (Ne.symm different)).trans found,type,hole⟩

theorem ReallocatesBuffer.destinationType {program : RuntimeProgram} {before after : World}
    {custody : ClaimCustody} {oldAllocation allocation : ResolvedPlace} {old pointer : RawPointer}
    {domain : Identity} {element type : Term} {count base : Nat} {destination : Address}
    (valid : before.WellFormed)
    (reallocated : ReallocatesBuffer program custody before oldAllocation old domain element count base pointer allocation after)
    (destinationType : Execution.DestinationType before destination type) :
    Execution.DestinationType after destination type := by
  cases reallocated with
  | grow ready allocated moved released =>
    obtain ⟨_,buffer,_⟩ := ready.source
    have oldDifferent := buffer.destination_root_ne destinationType
    have destinationOriginal := destinationType
    obtain ⟨_,root,found,_,_⟩ := destinationType
    have bound := World.root_bound valid (World.root_found found).1
    have fresh : allocation.address.root = before.nextRoot := by cases allocated; rfl
    have newDifferent : allocation.address.root ≠ destination.root := by
      rw [fresh]
      exact Ne.symm (Nat.ne_of_lt bound)
    apply released.destinationType
    apply (allocated.destinationType valid destinationOriginal).frame moved.locations
    apply moved.read_disjoint
    intro place member overlap
    rcases List.mem_append.mp member with old | new
    · obtain ⟨_,_,rfl⟩ := Slots.resolved_member old
      exact oldDifferent overlap.1
    · obtain ⟨_,_,rfl⟩ := Slots.resolved_member new
      exact newDifferent overlap.1

theorem BufferReallocationRequest.progress {program : Kernel.Program} {world : World}
    {oldAllocation : ResolvedPlace} {old : RawPointer} {domain : Identity}
    {element : Term} {count : Nat} {layout : Layout} (custody : ClaimCustody)
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program world)
    (request : BufferReallocationRequest program world oldAllocation old domain element count layout) :
    (∃ base pointer allocation after,
      ReallocatesBuffer program custody world oldAllocation old domain element count base pointer allocation after ∧
        Typing.WorldTyped program after) ∨
      BufferReallocationExhausted program world oldAllocation old domain element count layout := by
  obtain ⟨oldCount,ready⟩ := request.2
  rcases request.1.progress custody with ⟨base,pointer,allocation,allocated,buffer⟩ | exhausted
  · obtain ⟨after,reallocated,afterTyped⟩ := ready.reallocate_exists valid inventory typed buffer
    exact Or.inl ⟨base,pointer,allocation,after,reallocated,afterTyped⟩
  · exact Or.inr ⟨request,exhausted.2⟩

theorem BufferReallocationExhausted.no_reallocation {program : RuntimeProgram} {world after : World}
    {custody : ClaimCustody} {oldAllocation allocation : ResolvedPlace} {old pointer : RawPointer}
    {domain : Identity} {element : Term} {count base : Nat} {layout : Layout}
    (valid : ProgramWellFormed program.declarations)
    (exhausted : BufferReallocationExhausted program world oldAllocation old domain element count layout) :
    ¬ ReallocatesBuffer program custody world oldAllocation old domain element count base pointer allocation after := by
  intro reallocated
  cases reallocated with
  | grow _ allocated _ _ => exact BufferAllocationExhausted.no_allocation valid ⟨exhausted.1.1,exhausted.2⟩ allocated

end Memory

namespace Execution

open Memory

theorem PrimitiveStep.reallocate_typed_progress {program : Kernel.Program} {before : State}
    {context : Context} {destination : Address} {binding : RuntimeBinding} {element : Term}
    {pointerAddress countAddress oldAllocation : ResolvedPlace} {old : RawPointer} {next : Kernel.Code}
    {count : Int} {domain : Identity} {layout : Layout}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .primitive context destination binding [element] [pointerAddress,countAddress] next)
    (identity : binding.primitive = some .reallocate) (domainBound : binding.domain = some domain)
    (pointerAt : PointerAt before.world pointerAddress old)
    (resource : Kernel.ResolvesResource before.world context.environment (.activation context.activation) oldAllocation)
    (countAt : ScalarAt before.world countAddress (.integer false .pointer count)) (nonnegative : 0 ≤ count)
    (request : BufferReallocationRequest program before.world oldAllocation old domain element count.toNat layout)
    (destinationType : DestinationType before.world destination (.rawPointer .unique element)) :
    ∃ event after, PrimitiveStep program before event after ∧ Typing.WorldTyped program after.world ∧
      ((event = some (.fatal .resource) ∧ after.task = .fatal .resource ∧ after.world = before.world) ∨
        ∃ pointer value allocation, after.world.Stores destination value ∧
          Typing.ValueTyped program after.world value ∧ value.head = .pointer pointer ∧
          after.task = .run (context.bindResource before.world.nextLoan allocation) next) := by
  rcases request.progress (.activation context.activation) valid inventory typed with
      ⟨base,pointer,allocation,reallocated,buffer,reallocatedTyped⟩ | exhausted
  · obtain ⟨after,stored⟩ := StoresPointer.exists pointer (buffer.destinationType typed.1 destinationType)
    have afterTyped := stored.worldTyped valid inventory reallocatedTyped buffer.bound buffer.origin
    obtain ⟨value,found,valueTyped,head⟩ := stored.typed_result buffer.bound buffer.origin
    exact ⟨_,_,.reallocate task identity domainBound pointerAt resource countAt nonnegative buffer stored,afterTyped,
      Or.inr ⟨pointer,value,allocation,found,valueTyped,head,rfl⟩⟩
  · exact ⟨_,_,.reallocateExhausted task identity domainBound pointerAt resource countAt nonnegative exhausted,typed,
      Or.inl ⟨rfl,rfl,rfl⟩⟩

theorem Step.reallocate_typed_progress {program : Kernel.Program} {host : Foreign.Model} {before : State}
    {context : Context} {destination : Address} {binding : RuntimeBinding} {element : Term}
    {pointerAddress countAddress oldAllocation : ResolvedPlace} {old : RawPointer} {next : Kernel.Code}
    {count : Int} {domain : Identity} {layout : Layout}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .primitive context destination binding [element] [pointerAddress,countAddress] next)
    (identity : binding.primitive = some .reallocate) (domainBound : binding.domain = some domain)
    (pointerAt : PointerAt before.world pointerAddress old)
    (resource : Kernel.ResolvesResource before.world context.environment (.activation context.activation) oldAllocation)
    (countAt : ScalarAt before.world countAddress (.integer false .pointer count)) (nonnegative : 0 ≤ count)
    (request : BufferReallocationRequest program before.world oldAllocation old domain element count.toNat layout)
    (destinationType : DestinationType before.world destination (.rawPointer .unique element)) :
    ∃ event after, Step program host before event after ∧ Typing.WorldTyped program after.world ∧
      ((event = some (.fatal .resource) ∧ after.task = .fatal .resource ∧ after.world = before.world) ∨
        ∃ pointer value allocation, after.world.Stores destination value ∧
          Typing.ValueTyped program after.world value ∧ value.head = .pointer pointer ∧
          after.task = .run (context.bindResource before.world.nextLoan allocation) next) := by
  obtain ⟨event,after,stepped,afterTyped,outcome⟩ := PrimitiveStep.reallocate_typed_progress valid inventory typed
    task identity domainBound pointerAt resource countAt nonnegative request destinationType
  exact ⟨event,after,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl stepped)))),afterTyped,outcome⟩

end Execution
end Glorious.Language
