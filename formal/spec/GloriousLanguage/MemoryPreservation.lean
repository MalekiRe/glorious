import GloriousLanguage.BulkMovePreservation
import GloriousLanguage.PointerStorageConstruction
import GloriousLanguage.UnitStorageConstruction
import GloriousLanguage.LocalPreservation

/-! Storage preservation for the actual raw-memory producers. The common
buffer allocator and pointer installer supply their lower proofs; bulk moves,
raw operations and primitive execution consume those same producers. -/
namespace Glorious.Language
namespace Memory

theorem ReallocatesBuffer.worldTyped {program : Kernel.Program} {before after : World}
    {custody oldAllocation old domain element count base result allocation}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (reallocated : ReallocatesBuffer program custody before oldAllocation old domain element count base result allocation after) :
    Typing.WorldTyped program after := by
  cases reallocated with
  | grow _ allocated moved released =>
    exact released.worldTyped (moved.worldTyped valid inventory (allocated.worldTyped valid inventory typed))

theorem RawRead.worldTyped {program : Kernel.Program} {before after : World}
    {source pointer type copy destination}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (read : RawRead program before source pointer type copy destination after) : Typing.WorldTyped program after := by
  cases read with
  | read _ _ _ copied =>
    rcases copied with ⟨_,copied⟩ | ⟨_,moved⟩
    · exact copied.worldTyped valid inventory typed
    · exact moved.worldTyped valid inventory typed

theorem RawWrite.worldTyped {program : Kernel.Program} {before after : World}
    {source destination pointer type}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (written : RawWrite program before source destination pointer type after) : Typing.WorldTyped program after := by
  cases written with
  | write _ _ _ _ _ _ moved => exact moved.worldTyped valid inventory typed

theorem RawBorrow.worldTyped {program : Kernel.Program} {before after : World}
    {source pointer type mode region destination}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (borrowed : RawBorrow program before source pointer type mode region destination after) : Typing.WorldTyped program after := by
  cases borrowed with
  | borrow _ _ _ _ borrowed => exact borrowed.worldTyped valid inventory typed

end Memory

namespace Execution

theorem StoresScalar.worldTyped {program : Kernel.Program} {before after : World} {destination scalar}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (stored : StoresScalar program before destination scalar after) : Typing.WorldTyped program after :=
  stored.2.2.empty_worldTyped valid inventory typed (by simp) (by simp) (.scalar stored.1)


/-- Every primitive transition preserves complete storage typing, including
fresh buffers, overlapping bulk relocation, raw reference operations and
layout results. Arithmetic result validity is consumed from StoresScalar's
actual producer contract; arithmetic totality is proved independently. -/
theorem PrimitiveStep.worldTyped {program : Kernel.Program} {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world) (step : PrimitiveStep program before event after) :
    Typing.WorldTyped program after.world := by
  cases step with
  | scalar task primitive inputs calculated stored => exact stored.worldTyped valid inventory typed
  | scalarFault => exact typed
  | allocateExhausted => exact typed
  | reallocateExhausted => exact typed
  | allocate task primitive domain count nonnegative allocated stored =>
    exact stored.worldTyped valid inventory (allocated.worldTyped valid inventory typed) allocated.bound allocated.origin
  | release task primitive domain pointer resource released stored =>
    exact stored.worldTyped valid inventory (released.worldTyped typed)
  | reallocate task primitive domain old resource count nonnegative reallocated stored =>
    exact stored.worldTyped valid inventory (reallocated.worldTyped valid inventory typed) reallocated.bound reallocated.origin
  | rawRead task primitive pointer resource read => exact read.worldTyped valid inventory typed
  | rawCopy task primitive pointer resource read => exact read.worldTyped valid inventory typed
  | rawWrite task primitive pointer resource written stored =>
    exact stored.worldTyped valid inventory (written.worldTyped valid inventory typed)
  | rawMove _ _ _ _ _ _ _ _ _ moved stored =>
    exact stored.worldTyped valid inventory (moved.worldTyped valid inventory typed)
  | rawBorrow task primitive pointer resource borrowed => exact borrowed.worldTyped valid inventory typed
  | pointerOffset task primitive pointer amount offset stored =>
    exact stored.worldTyped valid inventory typed offset.bound offset.origin
  | pointerAddress task primitive pointer stored => exact stored.worldTyped valid inventory typed
  | pointerWithAddress task primitive pointer integer nonnegative changed stored =>
    exact stored.worldTyped valid inventory typed changed.bound changed.origin
  | layout task primitive layout constant destination written counter =>
    subst counter
    exact constant.install_worldTyped valid inventory typed destination.vacant destination.addressType written
  | literalText task primitive constant result destination written =>
    exact constant.install_worldTyped valid inventory typed destination.vacant destination.addressType written
  | literalBytes task primitive constant result destination written =>
    exact constant.install_worldTyped valid inventory typed destination.vacant destination.addressType written
  | abort => exact typed

end Execution

end Glorious.Language
