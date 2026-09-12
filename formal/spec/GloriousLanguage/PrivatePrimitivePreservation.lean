import GloriousLanguage.PrivateControl

/-! Machine leaves preserve hidden logical storage through their actual
allocation, raw-access and physical-transfer producers. Pointer provenance
does not make an internal caller slot a raw-memory location. -/
namespace Glorious.Language

theorem World.PrivateSlot.stable {before after : World} {id : Identity} {root : Root}
    (slot : before.PrivateSlot id root) (roots : after.roots.get id = before.roots.get id)
    (loans : after.loans = before.loans) (availability : after.availability = before.availability) :
    after.PrivateSlot id root :=
  slot.transport roots (slot.safe.sameHomes (by rw [roots]) loans availability)

namespace Memory

theorem AllocatesBuffer.private_slot {program : Program} {before after : World}
    {domain element count base pointer} {id : Identity} {root : Root}
    (allocated : AllocatesBuffer program before domain element count base pointer after)
    (well : before.WellFormed) (slot : before.PrivateSlot id root) : after.PrivateSlot id root :=
  slot.stable (allocated.roots_other (slot.bound well)) allocated.authorityStable.loans (by cases allocated; rfl)

theorem ReleasesBuffer.private_slot {program : Program} {before after : World} {pointer domain}
    {id : Identity} {root : Root} (released : ReleasesBuffer program before pointer domain after)
    (slot : before.PrivateSlot id root) : after.PrivateSlot id root := by
  have origin : ∃ allocation, pointer.allocation = some allocation := by cases released; exact ⟨_,by assumption⟩
  obtain ⟨allocation,origin⟩ := origin
  exact slot.stable
    (released.roots_other origin (released.avoids_internal slot.found slot.internalHome origin).symm)
    released.authorityStable.loans released.availability

theorem ReallocatesBuffer.private_slot {program : Program} {before after : World}
    {old domain element count base result} {id : Identity} {root : Root}
    (reallocated : ReallocatesBuffer program before old domain element count base result after)
    (well : before.WellFormed) (slot : before.PrivateSlot id root) : after.PrivateSlot id root :=
  slot.stable (reallocated.private_root (slot.bound well) slot.found slot.internalHome)
    reallocated.authorityStable.loans reallocated.availability

theorem RawRead.private_slot {program : Program} {before after : World} {pointer type copy destination}
    {id : Identity} {root : Root} (read : RawRead program before pointer type copy destination after)
    (slot : before.PrivateSlot id root) (outside : destination.root ≠ id) : after.PrivateSlot id root := by
  cases read with
  | read _ _ _ action =>
    rcases action with ⟨_,copied⟩ | ⟨_,moved⟩
    · exact copied.private_slot slot outside
    · exact moved.private_slot slot outside

theorem RawWrite.private_slot {program : Program} {before after : World} {authority source pointer type}
    {id : Identity} {root : Root} (written : RawWrite program before authority source pointer type after)
    (slot : before.PrivateSlot id root) : after.PrivateSlot id root := by
  cases written with
  | write _ _ points _ _ moved => exact moved.private_slot slot (slot.internalHome.no_raw slot.found points)

theorem RawBorrow.private_slot {program : Program} {before after : World} {pointer type mode region destination}
    {id : Identity} {root : Root} (borrowed : RawBorrow program before pointer type mode region destination after)
    (slot : before.PrivateSlot id root) (outside : destination.root ≠ id) : after.PrivateSlot id root := by
  cases borrowed with
  | borrow _ _ _ _ formed => exact formed.private_slot slot outside

end Memory

namespace Execution

open Kernel

theorem PrimitiveStep.private_slot {program : Kernel.Program} {before after : State} {event : Option Event}
    {id : Identity} {root : Root} (step : PrimitiveStep program before event after)
    (well : before.world.WellFormed) (slot : before.world.PrivateSlot id root)
    (outside : id ∉ before.task.rootSupport) : after.world.PrivateSlot id root := by
  cases step
  all_goals try exact slot
  all_goals simp_all only [Task.rootSupport,List.mem_append,List.mem_cons,not_or]
  case scalar stored | pointerAddress stored => exact stored.2.2.private_slot slot (Ne.symm outside.2.1)
  case allocate allocated stored => exact stored.2.private_slot (allocated.private_slot well slot) (Ne.symm outside.2.1)
  case release released stored => exact stored.2.private_slot (released.private_slot slot) (Ne.symm outside.2.1)
  case reallocate allocated stored => exact stored.2.private_slot (allocated.private_slot well slot) (Ne.symm outside.2.1)
  case rawRead read | rawCopy read => exact read.private_slot slot (Ne.symm outside.2.1)
  case rawWrite written stored => exact stored.2.private_slot (written.private_slot slot) (Ne.symm outside.2.1)
  case rawBorrow borrowed => exact borrowed.private_slot slot (Ne.symm outside.2.1)
  case pointerOffset stored | pointerWithAddress stored => exact stored.2.private_slot slot (Ne.symm outside.2.1)
  case layout written _ =>
    have current := slot.write written (Ne.symm outside.2.1)
    exact ⟨current.found,current.vacant,current.safe,current.internalHome⟩

theorem PrimitiveStep.private_control {program : Kernel.Program} {before after : State} {event : Option Event}
    {id owner : Identity} {inner : List Frame} (step : PrimitiveStep program before event after)
    (control : PrivateControl id owner inner before.task) : PrivateControl id owner inner after.task := by
  cases step
  all_goals simp_all [PrivateControl,Task.rootSupport,Task.PrivateActivation]

end Execution
end Glorious.Language
