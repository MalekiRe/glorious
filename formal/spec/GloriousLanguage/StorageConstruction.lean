import GloriousLanguage.ConstructionPreservation
import GloriousLanguage.StorageWrites

/-! Constructibility of the common vacant-storage write and empty-input value
producer. Scalar results and continuation handles consume this same relation;
an actual allocation is separate from initialization and may fail physically. -/
namespace Glorious.Language

theorem NewValue.empty_exists {program : RuntimeProgram} {before : World} {destination : Address}
    {type : Term} (head : ValueHead) (vacant : before.Vacant destination)
    (typed : AddressType program.declarations before destination type) :
    ∃ after, NewValue program before destination type head [] after := by
  obtain ⟨after,written⟩ := vacant.write_exists (some (.resident before.nextOwner type head true []))
  refine ⟨_,NewValue.construct vacant typed ⟨.nil,?_,.nil,?_⟩ ?_ .nil written⟩
  · intro value member; simp at member
  · intro source member; simp at member
  · intro source member; simp at member

/-- A successful fresh allocation supplies both actual vacancy and its
declared address type. Initialization is constructed, not an allocation input. -/
theorem Allocates.empty_value {program : RuntimeProgram} {before allocated : World}
    {home region type layout mutable address}
    (allocation : Allocates program.declarations before home region type layout mutable address allocated) (head : ValueHead) :
    ∃ after, NewValue program allocated address type head [] after :=
  NewValue.empty_exists head allocation.created_vacant allocation.created_addressType

end Glorious.Language
