import GloriousLanguage.StorageConstruction

/-! The actual pointer installer constructs and types its written resident
from an admitted origin and vacant destination. The resulting world is never
an input to pointer progress. -/
namespace Glorious.Language.Execution

theorem StoresPointer.exists {program : Kernel.Program} {before : World}
    {destination : Address} {mode : Mutability} {type : Term} (pointer : RawPointer)
    (destinationType : DestinationType before destination (.rawPointer mode type)) :
    ∃ after, StoresPointer program before destination mode type pointer after := by
  obtain ⟨after,constructed⟩ := NewValue.empty_exists (.pointer pointer)
    destinationType.vacant destinationType.addressType
  exact ⟨after,destinationType,constructed⟩

theorem StoresPointer.worldTyped {program : Kernel.Program} {before after : World} {destination mode type pointer}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (bound : pointer.address < 2^program.declarations.input.target.pointerBits) (origin : pointer.Origin before)
    (stored : StoresPointer program before destination mode type pointer after) : Typing.WorldTyped program after :=
  stored.2.empty_worldTyped valid inventory typed (by simp) (by simp) (.pointer bound origin)

theorem StoresPointer.typed_result {program : Kernel.Program} {before after : World}
    {destination : Address} {mode : Mutability} {type : Term} {pointer : RawPointer}
    (bound : pointer.address < 2^program.declarations.input.target.pointerBits)
    (origin : pointer.Origin before)
    (stored : StoresPointer program before destination mode type pointer after) :
    ∃ value, after.Stores destination value ∧ Typing.ValueTyped program after value ∧ value.head = .pointer pointer := by
  obtain ⟨_,constructed⟩ := stored
  cases constructed with
  | construct _ _ ready _ cleared written =>
      have sources := ready.1
      cases sources
      cases cleared
      have coherent := origin.transport (World.write_locations written)
      refine ⟨.resident before.nextOwner (.rawPointer mode type) (.pointer pointer) true [],?_,.pointer bound coherent,rfl⟩
      have found := World.write_read_inside written []
      simpa [Value.atPath,World.Stores,World.read,World.root] using found

end Glorious.Language.Execution
