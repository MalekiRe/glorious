import GloriousLanguage.ForeignEvolution

/-! Exact root framing from the existing mutation producers. Vacant private
slots are included: the absence of a resident does not authorize installing
one, retiring the slot or changing its home, generation or lifetime. -/
namespace Glorious.Language

open Kernel Execution Memory

theorem World.write_roots_other {before after : World} {address : Address} {value : Option Value} {id : Identity}
    (written : before.write address value = some after) (outside : id ≠ address.root) :
    after.roots.get id = before.roots.get id := by
  obtain ⟨root,value,_,rfl⟩ := World.write_value_update written
  exact Table.get_set_other _ _ _ _ outside

theorem Allocates.roots_other {program : Program} {before after : World}
    {home region type layout mutable address} {id : Identity}
    (allocated : Allocates program before home region type layout mutable address after) (bound : id < before.nextRoot) :
    after.roots.get id = before.roots.get id := by
  cases allocated
  exact Table.get_set_other _ _ _ _ (Nat.ne_of_lt bound)

theorem Clears.roots_other {before after : World} {addresses : List Address} {id : Identity}
    (cleared : Clears before addresses after) (outside : ∀ address ∈ addresses, id ≠ address.root) :
    after.roots.get id = before.roots.get id := by
  induction cleared with
  | nil => rfl
  | cons written _ ih =>
    exact (ih (fun _ member => outside _ (List.mem_cons_of_mem _ member))).trans
      (World.write_roots_other written (outside _ List.mem_cons_self))

/-- The allocation-claim release only rewrites the loan table. -/
theorem ReleasesStorageClaims.roots_other {before after : World} {place : ResolvedPlace} {id : Identity}
    (released : ReleasesStorageClaims before place after) : after.roots.get id = before.roots.get id := by
  cases released
  rfl

theorem Transfers.roots_other {program : RuntimeProgram} {before after : World} {authority : Authority}
    {source destination : Address} {id : Identity}
    (moved : Transfers program before authority source destination after)
    (sourceOutside : id ≠ source.root) (destinationOutside : id ≠ destination.root) :
    after.roots.get id = before.roots.get id := by
  cases moved with
  | move _ _ _ _ _ _ _ sourceWritten destinationWritten =>
    exact (World.write_roots_other destinationWritten destinationOutside).trans
      (World.write_roots_other sourceWritten sourceOutside)

theorem Copies.roots_other {program : RuntimeProgram} {before after : World} {authority : Authority}
    {source destination : Address} {id : Identity}
    (copied : Copies program before authority source destination after) (outside : id ≠ destination.root) :
    after.roots.get id = before.roots.get id := by
  cases copied with
  | copy =>
    rename_i value cloned next afterWorld stored initialized ready permission vacant typed copiedValue written
    exact World.write_roots_other (after := afterWorld) written outside

theorem Acquires.roots_other {program : RuntimeProgram} {before after : World} {authority : Authority}
    {force : Bool} {source destination : Address} {id : Identity}
    (acquired : Acquires program before authority force source destination after)
    (sourceOutside : id ≠ source.root) (destinationOutside : id ≠ destination.root) :
    after.roots.get id = before.roots.get id := by
  cases acquired with
  | explicitMove moved => exact moved.roots_other sourceOutside destinationOutside
  | copy copied => exact copied.roots_other destinationOutside
  | move _ _ _ moved => exact moved.roots_other sourceOutside destinationOutside

theorem NewValue.roots_other {program : RuntimeProgram} {before after : World}
    {destination : Address} {type : Term} {head : ValueHead} {sources : List ResolvedPlace} {id : Identity}
    (constructed : NewValue program before destination type head sources after)
    (destinationOutside : id ≠ destination.root) (sourcesOutside : ∀ source ∈ sources, id ≠ source.address.root) :
    after.roots.get id = before.roots.get id := by
  cases constructed with
  | construct =>
    rename_i residents taken afterWorld vacant typed ready separate cleared written
    refine (World.write_roots_other (after := afterWorld) written destinationOutside).trans (cleared.roots_other ?_)
    intro address member
    obtain ⟨source,present,rfl⟩ := List.mem_map.mp member
    exact sourcesOutside source present

theorem FormsLoan.roots_other {program : RuntimeProgram} {purpose : LoanPurpose} {before after : World}
    {authority : Authority} {mode : Mutability} {region : Identity} {referent destination : Address} {id : Identity}
    (borrowed : FormsLoan program purpose before authority mode region referent destination after)
    (outside : id ≠ destination.root) : after.roots.get id = before.roots.get id := by
  cases borrowed with
  | borrow =>
    rename_i value afterWorld parent stored typed initialized regionLive admitted accessible permitted vacant destTyped parentEq written
    exact World.write_roots_other (after := afterWorld) written outside

theorem Memory.InstallsResidents.roots_other {program : Program} {before after : World}
    {addresses : List Address} {values : List (Option Value)} {id : Identity}
    (installed : InstallsResidents program before addresses values after)
    (outside : ∀ address ∈ addresses, id ≠ address.root) : after.roots.get id = before.roots.get id := by
  induction installed with
  | nil => rfl
  | hole _ _ ih => exact ih (fun _ member => outside _ (List.mem_cons_of_mem _ member))
  | resident _ _ written _ ih =>
    exact (ih (fun _ member => outside _ (List.mem_cons_of_mem _ member))).trans
      (World.write_roots_other written (outside _ List.mem_cons_self))

theorem Memory.BulkMove.roots_other {program : RuntimeProgram} {before after : World}
    {sources destinations : List ResolvedPlace} {id : Identity}
    (moved : BulkMove program before sources destinations after)
    (sourcesOutside : ∀ address ∈ sources, id ≠ address.address.root)
    (destinationsOutside : ∀ address ∈ destinations, id ≠ address.address.root) :
    after.roots.get id = before.roots.get id := by
  obtain ⟨_,_,_,_,_,_,_,_,cleared,installed⟩ := moved
  refine (installed.roots_other ?_).trans (cleared.roots_other ?_)
  · intro address member
    obtain ⟨place,present,rfl⟩ := List.mem_map.mp member
    exact destinationsOutside place present
  · intro address member
    obtain ⟨place,present,rfl⟩ := List.mem_map.mp member
    exact sourcesOutside place present

theorem Memory.AllocatesBuffer.roots_other {program : Program} {custody : ClaimCustody} {before after : World}
    {domain : Identity} {element : Term} {count base : Nat} {pointer : RawPointer} {place : ResolvedPlace}
    {id : Identity}
    (allocated : AllocatesBuffer program custody before domain element count base pointer place after)
    (bound : id < before.nextRoot) : after.roots.get id = before.roots.get id := by
  cases allocated
  exact Table.get_set_other _ _ _ _ (Nat.ne_of_lt bound)

namespace Foreign

/-- Allocation/external objects can be explicitly shared with a host.
Internal logical homes require an actual source handoff instead. -/
def InternalHome (root : Root) : Prop :=
  ∀ domain, root.home ≠ .allocation domain ∧ root.home ≠ .external domain

theorem InternalHome.temporary {root : Root} {activation scope : Identity}
    (home : root.home = .temporary activation scope) : InternalHome root := by
  intro domain
  simp [home]

theorem InternalHome.no_raw {program : Language.Program} {world : World} {id : Identity} {root : Root}
    (selected : world.roots.get id = some root) (internalHome : InternalHome root)
    {pointer : RawPointer} {address : Address} {type : Term}
    (points : PointsTo program world pointer address type) : address.root ≠ id := by
  intro same
  obtain ⟨other,_,found,_,_,domain,_,home⟩ := points.2.2.2
  have identity := Option.some.inj ((World.root_found found).1.symm.trans (same ▸ selected))
  subst other
  exact home.elim (internalHome domain).1 (internalHome domain).2

end Foreign

theorem World.HomeExtension.internal_root {before after : World} {id : Identity} {root : Root}
    (changed : before.HomeExtension after) (bound : id < before.nextRoot)
    (selected : before.roots.get id = some root) (internalHome : Foreign.InternalHome root) :
    ∃ current, after.roots.get id = some current ∧ Foreign.InternalHome current := by
  have homes := changed.homes id bound
  rw [selected] at homes
  obtain ⟨current,found,home⟩ := Option.map_eq_some_iff.mp homes
  exact ⟨current,found,fun domain => by simpa only [home] using internalHome domain⟩

theorem Memory.ReleasesBuffer.avoids_internal {program : Program} {before after : World} {place : ResolvedPlace}
    {pointer : RawPointer} {domain allocation id : Identity} {root : Root}
    (released : ReleasesBuffer program before place pointer domain after) (selected : before.roots.get id = some root)
    (internalHome : Foreign.InternalHome root) (origin : pointer.allocation = some allocation) : allocation ≠ id := by
  cases released with
  | release =>
    rename_i value rootv unclaimed cleared retired bufferAt rootAt shellLive resourcesEmpty fieldsNone claims safe written retires ended
    obtain ⟨allocated, allocatedRoot, allocationEq, offset, addressEq, domainEq, rootFound, rootLive, home,
      generation, base, valueEq⟩ := bufferAt
    have rowEq : allocated = allocation := Option.some.inj (allocationEq.symm.trans origin)
    intro same
    have selected' : before.roots.get allocated = some root := by rw [rowEq, same]; exact selected
    have equal : allocatedRoot = root := Option.some.inj (rootFound.symm.trans selected')
    exact (internalHome domain).1 (equal ▸ home)

theorem Memory.ReleasesBuffer.roots_other {program : Program} {before after : World} {place : ResolvedPlace}
    {pointer : RawPointer} {domain allocation id : Identity}
    (released : ReleasesBuffer program before place pointer domain after)
    (origin : pointer.allocation = some allocation) (outside : id ≠ allocation) :
    after.roots.get id = before.roots.get id := by
  cases released with
  | release =>
    rename_i value rootv unclaimed cleared retired bufferAt rootAt shellLive resourcesEmpty fieldsNone claims safe written retires ended
    obtain ⟨allocated, allocatedRoot, allocationEq, offset, addressEq, domainEq, rootFound, rootLive, home,
      generation, base, valueEq⟩ := bufferAt
    have rowEq : allocated = allocation := Option.some.inj (allocationEq.symm.trans origin)
    have placeOutside : id ≠ place.address.root := by
      intro same
      exact outside (rowEq ▸ (by simpa only [addressEq] using same))
    calc after.roots.get id
        = _ := by rw [ended.2]
      _ = _ := retires.roots_other placeOutside
      _ = _ := World.write_roots_other written placeOutside
      _ = before.roots.get id := claims.roots_other (id := id)

theorem Memory.ReallocatesBuffer.private_root {program : RuntimeProgram} {custody : ClaimCustody}
    {before after : World} {oldAllocation allocation : ResolvedPlace} {old : RawPointer} {domain : Identity}
    {element : Term} {newCount base : Nat} {result : RawPointer} {id : Identity} {root : Root}
    (reallocated : ReallocatesBuffer program custody before oldAllocation old domain element newCount base result allocation after)
    (bound : id < before.nextRoot) (selected : before.roots.get id = some root) (internalHome : Foreign.InternalHome root) :
    after.roots.get id = before.roots.get id := by
  cases reallocated with
  | grow =>
    rename_i oldCount allocated moved ready bulkMove allocatedRun released
    obtain ⟨value, bufferAt, countEq, typeEq, shellClosed, resourcesEmpty, readyFields⟩ := ready.source
    obtain ⟨allocatedId, allocatedRoot, origin, offset, oldAddressEq, domainEq, rootFound, rootLive, home,
      generation, base, valueEq⟩ := bufferAt
    have oldOutside : id ≠ allocatedId := by
      intro same
      have selected' : before.roots.get allocatedId = some root := same.symm ▸ selected
      have equal : allocatedRoot = root := Option.some.inj (rootFound.symm.trans selected')
      exact (internalHome domain).1 (equal ▸ home)
    have newRoot : allocation.address.root = before.nextRoot := by cases allocatedRun with | fresh _ _ => rfl
    have newOutside : id ≠ allocation.address.root := by rw [newRoot]; exact Nat.ne_of_lt bound
    have slots (address : Address) (outer : id ≠ address.root) :
        ∀ slot ∈ Slots address 0 oldCount, id ≠ slot.root := by
      intro slot member
      obtain ⟨index,_,rfl⟩ := List.mem_map.mp member
      exact outer
    have oldSlots : ∀ slot ∈ Slots oldAllocation.address 0 oldCount, id ≠ slot.root := by
      rw [oldAddressEq]
      exact slots _ oldOutside
    have newSlots : ∀ slot ∈ Slots allocation.address 0 oldCount, id ≠ slot.root := slots _ newOutside
    have sourcesOutside : ∀ source ∈ (Slots oldAllocation.address 0 oldCount).map
        (fun address => (⟨address,oldAllocation.authority⟩ : ResolvedPlace)), id ≠ source.address.root := by
      intro source member
      obtain ⟨address,present,rfl⟩ := List.mem_map.mp member
      exact oldSlots address present
    have destinationsOutside : ∀ destination ∈ (Slots allocation.address 0 oldCount).map
        (fun address => (⟨address,allocation.authority⟩ : ResolvedPlace)), id ≠ destination.address.root := by
      intro destination member
      obtain ⟨address,present,rfl⟩ := List.mem_map.mp member
      exact newSlots address present
    exact (released.roots_other origin oldOutside).trans
      ((bulkMove.roots_other sourcesOutside destinationsOutside).trans (allocatedRun.roots_other bound))

end Glorious.Language
