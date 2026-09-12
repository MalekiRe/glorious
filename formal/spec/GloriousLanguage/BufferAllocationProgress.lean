import GloriousLanguage.BufferAllocationPreservation
import GloriousLanguage.PointerStorageConstruction
import GloriousLanguage.LayoutCoherence

/-! Buffer requests reach the actual allocation and pointer installation, or
the explicit terminal resource step. Physical nondeterminism may choose an
extent, but missing semantic admission cannot select the failure branch. -/
namespace Glorious.Language.Memory

theorem BufferAllocationRequest.layout_unique {program : Program} {world : World}
    {domain : Identity} {element : Term} {count : Nat} {left right : Layout}
    (valid : ProgramWellFormed program)
    (first : BufferAllocationRequest program world domain element count left)
    (second : BufferAllocationRequest program world domain element count right) : left = right := by
  obtain ⟨a,firstLayout,firstArray⟩ := first.array_layout
  obtain ⟨b,secondLayout,secondArray⟩ := second.array_layout
  have same := firstLayout.unique valid rfl secondLayout
  subst b
  exact firstArray.unique secondArray

theorem BufferAllocationRequest.progress {program : Program} {world : World}
    {domain : Identity} {element : Term} {count : Nat} {layout : Layout} (custody : ClaimCustody)
    (request : BufferAllocationRequest program world domain element count layout) :
    (∃ base pointer allocation after, AllocatesBuffer program custody world domain element count base pointer allocation after) ∨
      BufferAllocationExhausted program world domain element count layout := by
  classical
  by_cases physical : ∃ base, PhysicalExtent program.input.target world layout base
  · obtain ⟨base,extent⟩ := physical
    exact Or.inl ⟨base,_,_,_,.fresh request extent⟩
  · exact Or.inr ⟨request,physical⟩

theorem BufferAllocationExhausted.no_allocation {program : Program} {world after : World}
    {domain : Identity} {element : Term} {count base : Nat} {layout : Layout}
    {custody : ClaimCustody} {pointer : RawPointer} {allocation : ResolvedPlace}
    (valid : ProgramWellFormed program)
    (exhausted : BufferAllocationExhausted program world domain element count layout) :
    ¬ AllocatesBuffer program custody world domain element count base pointer allocation after := by
  intro allocated
  cases allocated with
  | fresh request extent =>
      have same := request.layout_unique valid exhausted.1
      exact exhausted.2 ⟨base,same ▸ extent⟩

end Glorious.Language.Memory

namespace Glorious.Language.Execution

open Memory

/-- Positive buffer admission and an existing result slot construct either
the real typed pointer result or an unchanged-world terminal resource fault. -/
theorem PrimitiveStep.allocate_typed_progress {program : Kernel.Program} {before : State}
    {context : Context} {destination : Address} {binding : RuntimeBinding}
    {element : Term} {countAddress : ResolvedPlace} {next : Kernel.Code}
    {count : Int} {domain : Identity} {layout : Layout}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .primitive context destination binding [element] [countAddress] next)
    (identity : binding.primitive = some .allocate) (domainBound : binding.domain = some domain)
    (observed : ScalarAt before.world countAddress (.integer false .pointer count)) (nonnegative : 0 ≤ count)
    (request : BufferAllocationRequest program.declarations before.world domain element count.toNat layout)
    (destinationType : DestinationType before.world destination (.rawPointer .unique element)) :
    ∃ event after, PrimitiveStep program before event after ∧ Typing.WorldTyped program after.world ∧
      ((event = some (.fatal .resource) ∧ after.task = .fatal .resource ∧ after.world = before.world) ∨
        ∃ pointer value allocation, after.world.Stores destination value ∧
          Typing.ValueTyped program after.world value ∧ value.head = .pointer pointer ∧
          after.task = .run (context.bindResource before.world.nextLoan allocation) next) := by
  rcases request.progress (.activation context.activation) with ⟨base,pointer,allocation,allocated,buffer⟩ | exhausted
  · obtain ⟨after,stored⟩ := StoresPointer.exists pointer (buffer.destinationType typed.1 destinationType)
    have afterTyped := stored.worldTyped valid inventory (buffer.worldTyped valid inventory typed) buffer.bound buffer.origin
    obtain ⟨value,found,valueTyped,head⟩ := stored.typed_result buffer.bound buffer.origin
    exact ⟨_,_,.allocate task identity domainBound observed nonnegative buffer stored,afterTyped,
      Or.inr ⟨pointer,value,allocation,found,valueTyped,head,rfl⟩⟩
  · exact ⟨_,_,.allocateExhausted task identity domainBound observed nonnegative exhausted,typed,
      Or.inl ⟨rfl,rfl,rfl⟩⟩

theorem Step.allocate_typed_progress {program : Kernel.Program} {host : Foreign.Model} {before : State}
    {context : Context} {destination : Address} {binding : RuntimeBinding}
    {element : Term} {countAddress : ResolvedPlace} {next : Kernel.Code}
    {count : Int} {domain : Identity} {layout : Layout}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .primitive context destination binding [element] [countAddress] next)
    (identity : binding.primitive = some .allocate) (domainBound : binding.domain = some domain)
    (observed : ScalarAt before.world countAddress (.integer false .pointer count)) (nonnegative : 0 ≤ count)
    (request : BufferAllocationRequest program.declarations before.world domain element count.toNat layout)
    (destinationType : DestinationType before.world destination (.rawPointer .unique element)) :
    ∃ event after, Step program host before event after ∧ Typing.WorldTyped program after.world ∧
      ((event = some (.fatal .resource) ∧ after.task = .fatal .resource ∧ after.world = before.world) ∨
        ∃ pointer value allocation, after.world.Stores destination value ∧
          Typing.ValueTyped program after.world value ∧ value.head = .pointer pointer ∧
          after.task = .run (context.bindResource before.world.nextLoan allocation) next) := by
  obtain ⟨event,after,step,afterTyped,outcome⟩ := PrimitiveStep.allocate_typed_progress valid inventory typed
    task identity domainBound observed nonnegative request destinationType
  exact ⟨event,after,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl step)))),afterTyped,outcome⟩

end Glorious.Language.Execution
