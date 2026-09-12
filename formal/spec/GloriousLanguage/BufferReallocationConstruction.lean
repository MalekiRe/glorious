import GloriousLanguage.BufferSlotConstruction

/-! The complete constructive buffer-growth path. Fresh physical storage,
the actual evaluated slot move, owning-claim discharge and old-region teardown
compose before a successful reallocation is concluded. -/
namespace Glorious.Language

theorem Clears.retains_shell {before after : World} {addresses : List Address}
    (cleared : Clears before addresses after) {address : Address} {value : Value}
    (outside : ∀ mutation ∈ addresses, ¬ mutation.Prefix address) (resident : before.Resident address value) :
    ∃ retained, after.Resident address retained ∧ retained.shell = value.shell := by
  induction cleared generalizing value with
  | nil => exact ⟨value,resident,rfl⟩
  | cons written _ ih =>
    obtain ⟨middle,found,first⟩ := World.write_retains_shell written (outside _ List.mem_cons_self) resident
    obtain ⟨retained,present,last⟩ := ih (fun mutation member => outside mutation (List.mem_cons_of_mem _ member)) found
    exact ⟨retained,present,last.trans first⟩

namespace Memory

theorem InstallsResidents.retains_shell {program : Program} {before after : World}
    {addresses : List Address} {values : List (Option Value)}
    (installed : InstallsResidents program before addresses values after) {address : Address} {value : Value}
    (outside : ∀ mutation ∈ addresses, ¬ mutation.Prefix address) (resident : before.Resident address value) :
    ∃ retained, after.Resident address retained ∧ retained.shell = value.shell := by
  induction installed generalizing value with
  | nil => exact ⟨value,resident,rfl⟩
  | hole _ _ ih => exact ih (fun mutation member => outside mutation (List.mem_cons_of_mem _ member)) resident
  | resident _ _ written _ ih =>
    obtain ⟨middle,found,first⟩ := World.write_retains_shell written (outside _ List.mem_cons_self) resident
    obtain ⟨retained,present,last⟩ := ih (fun mutation member => outside mutation (List.mem_cons_of_mem _ member)) found
    exact ⟨retained,present,last.trans first⟩

theorem BufferAt.with_stores {before after : World} {allocation : ResolvedPlace} {pointer : RawPointer}
    {domain : Identity} {value changed : Value} (buffer : BufferAt before allocation pointer domain value)
    (locations : ∀ id, (after.roots.get id).map Root.location = (before.roots.get id).map Root.location)
    (stored : after.Stores allocation.address changed) : BufferAt after allocation pointer domain changed := by
  obtain ⟨id,root,allocationEq,offset,address,domainEq,found,live,home,generation,physical,_⟩ := buffer
  have framed := locations id
  rw [found] at framed
  obtain ⟨current,selected,same⟩ := Option.map_eq_some_iff.mp framed
  have liveEq := congrArg Root.live same
  have homeEq := congrArg Root.home same
  have generationEq := congrArg Root.generation same
  have baseEq := congrArg Root.base same
  dsimp only [Root.location] at liveEq homeEq generationEq baseEq
  have atCurrent : after.root allocation.address = some current := by
    simp [World.root,address,selected,liveEq,live,generationEq,generation]
  have contents : current.value = some changed := by
    have whole : allocation.address.fields = [] := by simp [address]
    simpa [World.Stores,World.read,atCurrent,whole,Value.atPath] using stored
  exact ⟨id,current,allocationEq,offset,address,domainEq,selected,liveEq.trans live,homeEq.trans home,
    generationEq.trans generation,baseEq.trans physical,contents⟩

theorem BulkMove.empties_buffer {program : RuntimeProgram} {before after : World}
    {allocation destination : ResolvedPlace} {pointer : RawPointer} {domain : Identity}
    {value : Value} {count : Nat} (buffer : BufferAt before allocation pointer domain value)
    (length : value.fields.length = count)
    (different : allocation.address.root ≠ destination.address.root)
    (moved : BulkMove program before
      ((Slots allocation.address 0 count).map (fun address => ⟨address,allocation.authority⟩))
      ((Slots destination.address 0 count).map (fun address => ⟨address,destination.authority⟩)) after) :
    ∃ changed, BufferAt after allocation pointer domain changed ∧ changed.shell = value.shell ∧
      ∀ field ∈ changed.fields, field = none := by
  have locations := moved.locations
  obtain ⟨_,_,_,_,_,_,_,_,cleared,installed⟩ := moved
  have sourceOutside : ∀ mutation ∈ (Slots allocation.address 0 count).map
      (fun address => (⟨address,allocation.authority⟩ : ResolvedPlace)) |>.map ResolvedPlace.address,
      ¬ mutation.Prefix allocation.address := by
    intro mutation member included
    obtain ⟨place,present,rfl⟩ := List.mem_map.mp member
    obtain ⟨index,_,rfl⟩ := Slots.resolved_member present
    have impossible := included.length_le
    simp only [Address.child,List.length_append,List.length_singleton] at impossible
    omega
  obtain ⟨middle,present,first⟩ := cleared.retains_shell sourceOutside (World.resident_iff_stores.mpr buffer.stores)
  obtain ⟨changed,retained,last⟩ := installed.retains_shell (by
    intro mutation member included
    obtain ⟨place,present,rfl⟩ := List.mem_map.mp member
    obtain ⟨_,_,rfl⟩ := Slots.resolved_member present
    exact different included.1.symm) present
  have same := last.trans first
  have changedBuffer := buffer.with_stores locations (World.resident_iff_stores.mp retained)
  have countEq : changed.fields.length = count := by
    have lengths := congrArg (fun value : Value => value.fields.length) same
    have equal : changed.fields.length = value.fields.length := by
      simpa only [Value.shell,Value.withFields,Value.fields,List.length_replicate] using lengths
    exact equal.trans length
  refine ⟨changed,changedBuffer,same,?_⟩
  intro field member
  obtain ⟨index,selected⟩ := List.mem_iff_getElem?.mp member
  have bounded : index < count := by
    obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp selected
    simpa only [countEq] using bound
  have sourceMember : allocation.address.child (0+index) ∈
      ((Slots allocation.address 0 count).map (fun address => (⟨address,allocation.authority⟩ : ResolvedPlace))).map ResolvedPlace.address := by
    simp only [Slots,List.map_map,Function.comp_def,List.mem_map]
    exact ⟨index,List.mem_range.mpr bounded,rfl⟩
  have empty := cleared.cleared sourceMember []
  simp only [List.append_nil] at empty
  have finalEmpty := installed.read_disjoint (address := allocation.address.child (0+index)) (by
    intro mutation member overlap
    obtain ⟨place,present,rfl⟩ := List.mem_map.mp member
    obtain ⟨_,_,rfl⟩ := Slots.resolved_member present
    exact different overlap.1.symm)
  have read := changedBuffer.stores.read_child selected
  exact read.symm.trans (by simpa only [Nat.zero_add] using finalEmpty.trans empty)

/-- The admitted pre-world source and a real allocation construct the full
successful reallocation, including its old-region release. -/
theorem ReallocationSourceReady.reallocate_exists {program : Kernel.Program} {before allocatedWorld : World}
    {custody : ClaimCustody} {oldAllocation allocation : ResolvedPlace} {old pointer : RawPointer}
    {domain : Identity} {element : Term} {oldCount newCount base : Nat}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (ready : ReallocationSourceReady program before oldAllocation old domain element oldCount newCount)
    (allocated : AllocatesBuffer program.declarations custody before domain element newCount base pointer allocation allocatedWorld) :
    ∃ after, ReallocatesBuffer program custody before oldAllocation old domain element newCount base pointer allocation after ∧
      Typing.WorldTyped program after := by
  obtain ⟨moved,movement⟩ := ready.move_exists valid inventory typed allocated
  obtain ⟨value,buffer,length,_,shell,resources,_⟩ := ready.source
  have allocatedBuffer := buffer.allocated typed.1 allocated
  have freshRoot : allocation.address.root = before.nextRoot := by cases allocated; rfl
  obtain ⟨root,atRoot,_,_⟩ := buffer.root
  have oldBound := World.root_bound typed.1 (World.root_found atRoot).1
  have different : oldAllocation.address.root ≠ allocation.address.root := by rw [freshRoot]; exact Nat.ne_of_lt oldBound
  obtain ⟨changed,changedBuffer,same,holes⟩ := movement.empties_buffer allocatedBuffer length different
  have changedShell : changed.shellLive = false := by
    have sameLive := congrArg Value.shellLive same
    change changed.shellLive = value.shellLive at sameLive
    exact sameLive.trans shell
  have changedResources : changed.resources = [] := by
    have sameResources := congrArg Value.resources same
    change changed.resources = value.resources at sameResources
    exact sameResources.trans resources
  have claimReady := movement.release_ready (allocated.release_ready typed.1 ready.release_ready)
  have unreserved : ∀ id available, moved.availability.get id = some available → available.active = true →
      ∀ place ∈ available.reserved, place.address.root ≠ oldAllocation.address.root := by
    have availability := congrArg World.availability movement.rest
    rw [availability]
    cases allocated
    exact ready.unreserved
  have regionReady : ∀ actual, moved.root oldAllocation.address = some actual → BufferRegionReady moved oldAllocation actual.region := by
    intro actual located
    have framed := World.root_transport movement.locations (allocated.root typed.1 atRoot)
    obtain ⟨retained,selected,locationEq⟩ := framed
    have equal := Option.some.inj (selected.symm.trans located)
    subst retained
    have regionEq := congrArg Root.region locationEq
    have bounded : root.region < before.nextRegion :=
      typed.1.2.2.2.2.2.2.2.2.2.1 root.region (before.root_region_live typed.1 atRoot)
    exact regionEq ▸ movement.region_ready (allocated.region_ready bounded (ready.region_ready root atRoot))
  obtain ⟨after,released⟩ := ReleasesBuffer.exists changedBuffer changedShell changedResources holes claimReady unreserved regionReady
  exact ⟨after,.grow ready allocated movement released,
    released.worldTyped (movement.worldTyped valid inventory (allocated.worldTyped valid inventory typed))⟩

end Memory
end Glorious.Language
