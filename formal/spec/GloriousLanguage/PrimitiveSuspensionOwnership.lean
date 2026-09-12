import GloriousLanguage.SuspensionOrigins

/-! Primitive execution preserves captured storage ownership through its real
allocation and memory producers. Raw mutation may change values, but cannot
invent suspended homes or retire storage still owned by a suspension. -/
namespace Glorious.Language

open Kernel Execution Memory

theorem Memory.AllocatesBuffer.suspensionExtension {program : Program} {before after : World}
    {domain element count base pointer}
    (allocated : AllocatesBuffer program before domain element count base pointer after) :
    before.SuspensionExtension after := by
  refine ⟨allocated.authorityStable.homes,?_,?_,allocated.authorityStable.recorded⟩
  · intro id root suspension bound found home
    rw [allocated.roots_other bound,found]; rfl
  · intro id root suspension found home
    obtain ⟨original,originalAt,location⟩ := allocated.suspended_origin found home
    exact ⟨original,originalAt,location.symm⟩

theorem Memory.BulkMove.suspensionExtension {program : Program} {before after : World} {sources destinations}
    (moved : BulkMove program before sources destinations after) : before.SuspensionExtension after := by
  have counter := moved.authorityStable.homes.counter
  have recorded := moved.authorityStable.recorded
  obtain ⟨_,_,_,_,_,_,_,_,cleared,installed⟩ := moved
  exact .of_locations counter (fun id => (installed.locations id).trans (cleared.locations id)) recorded

theorem Memory.ReleasesBuffer.suspensionExtension {program : Program} {before after : World} {pointer domain}
    (released : ReleasesBuffer program before pointer domain after) : before.SuspensionExtension after := by
  cases released with
  | release _ _ _ _ _ _ _ _ _ _ _ _ written retired ended =>
    exact (World.write_suspensionExtension written).trans
      (retired.suspensionExtension.trans (RegionEnds.suspensionExtension ended))

theorem Memory.ReallocatesBuffer.suspensionExtension {program : Program} {before after : World}
    {old domain element count base result}
    (reallocated : ReallocatesBuffer program before old domain element count base result after) :
    before.SuspensionExtension after := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,allocated,_,moved,released⟩ := reallocated
  exact allocated.suspensionExtension.trans (moved.suspensionExtension.trans released.suspensionExtension)

theorem Memory.RawRead.suspensionExtension {program : Program} {before after : World} {pointer type copy destination}
    (read : RawRead program before pointer type copy destination after) : before.SuspensionExtension after := by
  cases read with
  | read _ _ _ action =>
    rcases action with ⟨_,copied⟩ | ⟨_,moved⟩
    · exact copied.suspensionExtension
    · exact moved.suspensionExtension

theorem Memory.RawWrite.suspensionExtension {program : Program} {before after : World} {authority source pointer type}
    (written : RawWrite program before authority source pointer type after) : before.SuspensionExtension after := by
  cases written with
  | write _ _ _ _ _ moved => exact moved.suspensionExtension

theorem Memory.RawBorrow.suspensionExtension {program : Program} {before after : World} {pointer type mode region destination}
    (borrowed : RawBorrow program before pointer type mode region destination after) : before.SuspensionExtension after := by
  cases borrowed with
  | borrow _ _ _ _ formed => exact formed.suspensionExtension

namespace Execution

/-- All successful and fatal primitive branches preserve the same captured
root relation; no primitive-specific post-state certificate is introduced. -/
theorem PrimitiveStep.suspensionExtension {program : Kernel.Program} {before after : State} {event : Option Event}
    (step : PrimitiveStep program before event after) : before.world.SuspensionExtension after.world := by
  cases step with
  | scalar _ _ _ _ stored => exact stored.2.2.suspensionExtension
  | scalarFault => exact .refl _
  | allocate _ _ _ _ _ allocated stored => exact allocated.suspensionExtension.trans stored.2.suspensionExtension
  | release _ _ _ _ released stored => exact released.suspensionExtension.trans stored.2.suspensionExtension
  | reallocate _ _ _ _ _ _ reallocated stored => exact reallocated.suspensionExtension.trans stored.2.suspensionExtension
  | rawRead _ _ _ read => exact read.suspensionExtension
  | rawCopy _ _ _ read => exact read.suspensionExtension
  | rawWrite _ _ _ written stored => exact written.suspensionExtension.trans stored.2.suspensionExtension
  | rawBorrow _ _ _ borrowed => exact borrowed.suspensionExtension
  | pointerOffset _ _ _ _ _ stored => exact stored.2.suspensionExtension
  | pointerAddress _ _ _ stored => exact stored.2.2.suspensionExtension
  | pointerWithAddress _ _ _ _ _ _ stored => exact stored.2.suspensionExtension
  | layout _ _ _ _ _ written _ =>
    have changed := World.write_suspensionExtension written
    exact ⟨⟨changed.counter,changed.homes⟩,changed.retained,changed.origin,changed.recorded⟩
  | abort => exact .refl _

theorem PrimitiveStep.suspensions {program : Kernel.Program} {before after : State} {event : Option Event}
    (well : before.world.WellFormed) (suspensions : before.SuspensionsWellFormed)
    (step : PrimitiveStep program before event after) : after.SuspensionsWellFormed := by
  apply suspensions.transport well step.suspensionExtension
  · cases step <;> rfl
  · cases step <;> exact Nat.le_refl _

end Execution
end Glorious.Language
