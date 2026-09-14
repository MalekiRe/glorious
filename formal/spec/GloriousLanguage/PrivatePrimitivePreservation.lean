import GloriousLanguage.PrivateControl

/-! Machine leaves preserve hidden logical storage through their actual
allocation, raw-access and physical-transfer producers. Pointer provenance
does not make an internal caller slot a raw-memory location. -/
namespace Glorious.Language

namespace Memory

theorem AllocatesBuffer.fresh_avoids {program : Program} {custody : ClaimCustody} {before after : World}
    {domain element count base pointer allocation} {id : Identity}
    (allocated : AllocatesBuffer program custody before domain element count base pointer allocation after)
    (bound : id < before.nextRoot) : allocation.address.root ≠ id := by
  cases allocated
  exact (Nat.ne_of_lt bound).symm

theorem AllocatesBuffer.private_slot {program : Program} {custody : ClaimCustody} {before after : World}
    {domain element count base pointer allocation} {id : Identity} {root : Root}
    (allocated : AllocatesBuffer program custody before domain element count base pointer allocation after)
    (well : before.WellFormed) (slot : before.PrivateSlot id root) : after.PrivateSlot id root := by
  refine slot.retain ((allocated.roots_other (slot.bound well)).trans slot.found) ?_ ?_
  · intro key loan found live
    rcases allocated.loan_live_before found live with ⟨original,present,active,same⟩ | fresh
    · rw [same]
      exact slot.safe.1 key original present active
    · exact (Nat.ne_of_lt (Nat.lt_of_lt_of_le (slot.bound well) fresh)).symm
  · simpa only [allocated.availability] using slot.safe.2.1

theorem ReleasesBuffer.private_slot {program : Program} {before after : World} {allocation pointer domain}
    {id : Identity} {root : Root} (released : ReleasesBuffer program before allocation pointer domain after)
    (slot : before.PrivateSlot id root) : after.PrivateSlot id root := by
  have origin : ∃ rootId, pointer.allocation = some rootId := by
    cases released with
    | release ready _ _ _ _ _ _ _ _ _ => exact ⟨ready.choose,ready.choose_spec.choose_spec.1⟩
  obtain ⟨rootId,origin⟩ := origin
  refine slot.retain
    ((released.roots_other origin (released.avoids_internal slot.found slot.internalHome origin).symm).trans slot.found) ?_ ?_
  · intro key loan found live
    obtain ⟨original,present,active,same⟩ := released.loan_live_before found live
    rw [same]
    exact slot.safe.1 key original present active
  · simpa only [released.availability] using slot.safe.2.1

theorem ReallocatesBuffer.fresh_avoids {program : RuntimeProgram} {custody : ClaimCustody} {before after : World}
    {oldAllocation old domain element count base result allocation} {id : Identity}
    (reallocated : ReallocatesBuffer program custody before oldAllocation old domain element count base result allocation after)
    (bound : id < before.nextRoot) : allocation.address.root ≠ id := by
  cases reallocated with
  | grow _ allocated _ _ => exact allocated.fresh_avoids bound

theorem ReallocatesBuffer.private_slot {program : RuntimeProgram} {custody : ClaimCustody} {before after : World}
    {oldAllocation old domain element count base result allocation} {id : Identity} {root : Root}
    (reallocated : ReallocatesBuffer program custody before oldAllocation old domain element count base result allocation after)
    (well : before.WellFormed) (slot : before.PrivateSlot id root) : after.PrivateSlot id root := by
  refine slot.retain ((reallocated.private_root (slot.bound well) slot.found slot.internalHome).trans slot.found) ?_ ?_
  · intro key loan found live
    rcases reallocated.loan_live_before found live with ⟨original,present,active,same⟩ | fresh
    · rw [same]
      exact slot.safe.1 key original present active
    · exact (Nat.ne_of_lt (Nat.lt_of_lt_of_le (slot.bound well) fresh)).symm
  · simpa only [reallocated.availability] using slot.safe.2.1


theorem RawRead.private_slot {program : RuntimeProgram} {before after : World} {source pointer type copy destination}
    {id : Identity} {root : Root} (read : RawRead program before source pointer type copy destination after)
    (slot : before.PrivateSlot id root) (outside : destination.root ≠ id) : after.PrivateSlot id root := by
  cases read with
  | read _ _ _ action =>
    rcases action with ⟨_,copied⟩ | ⟨_,moved⟩
    · exact copied.private_slot slot outside
    · exact moved.private_slot slot outside

theorem RawWrite.private_slot {program : RuntimeProgram} {before after : World} {source destination pointer type}
    {id : Identity} {root : Root} (written : RawWrite program before source destination pointer type after)
    (slot : before.PrivateSlot id root) : after.PrivateSlot id root := by
  cases written with
  | write _ _ points _ _ _ moved => exact moved.private_slot slot (slot.internalHome.no_raw slot.found points)

theorem RawBorrow.private_slot {program : RuntimeProgram} {before after : World} {source pointer type mode region destination}
    {id : Identity} {root : Root} (borrowed : RawBorrow program before source pointer type mode region destination after)
    (slot : before.PrivateSlot id root) (outside : destination.root ≠ id) : after.PrivateSlot id root := by
  cases borrowed with
  | borrow _ _ _ _ formed => exact formed.private_slot slot outside

end Memory

namespace Execution

open _root_.Glorious.Language.Kernel

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
    {id owner : Identity} {root : Root} {inner : List Frame} (step : PrimitiveStep program before event after)
    (well : before.world.WellFormed) (slot : before.world.PrivateSlot id root)
    (control : PrivateControl id owner inner before.task) : PrivateControl id owner inner after.task := by
  cases step
  all_goals simp_all [PrivateControl,Task.rootSupport,Task.PrivateActivation]
  case allocate allocated _ | reallocate allocated _ =>
    exact ⟨Context.bindResource_avoids_root control.1.1 (allocated.fresh_avoids (slot.bound well)),control.2.2.1⟩

end Execution
end Glorious.Language
