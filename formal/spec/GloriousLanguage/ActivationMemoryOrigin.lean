import GloriousLanguage.ActivationBranchOrigin

/-! Raw memory changes resident contents and allocation-domain homes, not
private activation identities. Machine leaves consume these exact storage
relations and preserve the same historical activation frontier. -/
namespace Glorious.Language

open Kernel Execution Memory

theorem Memory.AllocatesBuffer.activationsBelow {program : Program} {before after : World}
    {domain element count base pointer} {limit : Identity}
    (allocated : AllocatesBuffer program before domain element count base pointer after)
    (bounded : before.ActivationsBelow limit) : after.ActivationsBelow limit := by
  cases allocated
  intro id root found
  by_cases same : id = before.nextRoot
  · subst id
    simp only [Table.get_set,Option.some.injEq] at found
    subst root
    exact Home.allocation_activationsBelow _ _
  · exact bounded id root (by simpa only [Table.get_set_other _ _ _ _ same] using found)

theorem Memory.InstallsResidents.activationsBelow {program : Program} {before after : World}
    {addresses : List Address} {values : List (Option Value)} {limit : Identity}
    (installed : InstallsResidents program before addresses values after)
    (bounded : before.ActivationsBelow limit) : after.ActivationsBelow limit :=
  bounded.of_locations installed.locations

theorem Memory.BulkMove.activationsBelow {program : Program} {before after : World}
    {sources destinations} {limit : Identity}
    (moved : BulkMove program before sources destinations after)
    (bounded : before.ActivationsBelow limit) : after.ActivationsBelow limit := by
  obtain ⟨_,_,_,_,_,_,_,_,cleared,installed⟩ := moved
  exact installed.activationsBelow (cleared.activationsBelow bounded)

theorem Memory.ReleasesBuffer.activationsBelow {program : Program} {before after : World}
    {pointer domain} {limit : Identity}
    (released : ReleasesBuffer program before pointer domain after)
    (bounded : before.ActivationsBelow limit) : after.ActivationsBelow limit := by
  cases released with
  | release _ _ _ _ _ _ _ _ _ _ _ _ written retired ended =>
    exact ended.activationsBelow (retired.activationsBelow (World.write_activationsBelow written bounded))

theorem Memory.ReallocatesBuffer.activationsBelow {program : Program} {before after : World}
    {old domain element count base result} {limit : Identity}
    (reallocated : ReallocatesBuffer program before old domain element count base result after)
    (bounded : before.ActivationsBelow limit) : after.ActivationsBelow limit := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,allocated,_,moved,released⟩ := reallocated
  exact released.activationsBelow (moved.activationsBelow (allocated.activationsBelow bounded))

theorem Memory.RawRead.activationsBelow {program : Program} {before after : World}
    {pointer type copy destination} {limit : Identity}
    (read : RawRead program before pointer type copy destination after)
    (bounded : before.ActivationsBelow limit) : after.ActivationsBelow limit := by
  cases read with
  | read _ _ _ action =>
    rcases action with ⟨_,copied⟩ | ⟨_,moved⟩
    · exact copied.activationsBelow bounded
    · exact moved.activationsBelow bounded

theorem Memory.RawWrite.activationsBelow {program : Program} {before after : World}
    {authority source pointer type} {limit : Identity}
    (written : RawWrite program before authority source pointer type after)
    (bounded : before.ActivationsBelow limit) : after.ActivationsBelow limit := by
  cases written with
  | write _ _ _ _ _ moved => exact moved.activationsBelow bounded

theorem Memory.RawBorrow.activationsBelow {program : Program} {before after : World}
    {pointer type mode region destination} {limit : Identity}
    (borrowed : RawBorrow program before pointer type mode region destination after)
    (bounded : before.ActivationsBelow limit) : after.ActivationsBelow limit := by
  cases borrowed with
  | borrow _ _ _ _ formed => exact formed.activationsBelow bounded

namespace Execution

theorem PrimitiveStep.activation_frontier {program : Kernel.Program} {before after : State} {event : Option Event}
    (step : PrimitiveStep program before event after) : before.nextActivation ≤ after.nextActivation := by
  cases step <;> exact Nat.le_refl _

theorem PrimitiveStep.activation_support {program : Kernel.Program} {before after : State} {event : Option Event}
    (taskBound : RootSupport.Below before.task.activationSupport before.nextActivation)
    (frameBound : RootSupport.Below (before.frames.flatMap Frame.activationSupport) before.nextActivation)
    (step : PrimitiveStep program before event after) :
    RootSupport.Below after.task.activationSupport after.nextActivation ∧
      RootSupport.Below (after.frames.flatMap Frame.activationSupport) after.nextActivation := by
  cases step <;> simp_all only [Task.activationSupport,RootSupport.below_nil,true_and]

theorem PrimitiveStep.homes_activationsBelow {program : Kernel.Program} {before after : State} {event : Option Event}
    (bounded : before.world.ActivationsBelow before.nextActivation)
    (step : PrimitiveStep program before event after) : after.world.ActivationsBelow after.nextActivation := by
  cases step with
  | scalar _ _ _ _ stored => exact stored.2.2.activationsBelow bounded
  | scalarFault => exact bounded
  | allocate _ _ _ _ _ allocated stored => exact stored.2.activationsBelow (allocated.activationsBelow bounded)
  | release _ _ _ _ released stored => exact stored.2.activationsBelow (released.activationsBelow bounded)
  | reallocate _ _ _ _ _ _ reallocated stored => exact stored.2.activationsBelow (reallocated.activationsBelow bounded)
  | rawRead _ _ _ read | rawCopy _ _ _ read => exact read.activationsBelow bounded
  | rawWrite _ _ _ written stored => exact stored.2.activationsBelow (written.activationsBelow bounded)
  | rawBorrow _ _ _ borrowed => exact borrowed.activationsBelow bounded
  | pointerOffset _ _ _ _ _ stored | pointerWithAddress _ _ _ _ _ _ stored => exact stored.2.activationsBelow bounded
  | pointerAddress _ _ _ stored => exact stored.2.2.activationsBelow bounded
  | layout _ _ _ _ _ written _ =>
    have actual := World.write_activationsBelow written bounded
    exact actual
  | abort => exact bounded

end Execution
end Glorious.Language
