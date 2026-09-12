import GloriousLanguage.AllocationFraming
import GloriousLanguage.OrderedHandoff

/-! Ordered handoff preservation follows the actual temporary allocation and
clear/install producer. The original footprint protects earlier outputs through
every later input, including their guarded references and raw-resource support. -/
namespace Glorious.Language

theorem Value.SupportFramed.trans {before middle after : World} {value : Value}
    (loans : middle.loans = before.loans) (first : value.SupportFramed before middle)
    (last : value.SupportFramed middle after) : value.SupportFramed before after := by
  intro address supported
  have middle := (Value.Support.frame loans first).mp supported
  exact ⟨(last address middle).1.trans (first address supported).1,
    (last address middle).2.trans (first address supported).2⟩

theorem Transfers.supportFramed_of_outside {program : RuntimeProgram} {before after : World}
    {authority : Authority} {source destination : Address} {value : Value}
    (moved : Transfers program before authority source destination after)
    (sourceOutside : value.SupportOutside before source)
    (destinationOutside : value.SupportOutside before destination) : value.SupportFramed before after := by
  have locations := moved.locations
  cases moved with
  | move _ _ _ _ _ _ _ clear install =>
      intro address supported
      exact ⟨(World.write_disjoint install (destinationOutside address supported)).trans
        (World.write_disjoint clear (sourceOutside address supported)),locations _⟩

theorem Transfers.nextRoot {program : RuntimeProgram} {before after : World}
    {authority : Authority} {source destination : Address}
    (moved : Transfers program before authority source destination after) :
    after.nextRoot = before.nextRoot := by
  cases moved with
  | move _ _ _ _ _ _ _ clear install =>
      obtain ⟨_,_,_,rfl⟩ := World.write_value_update clear
      obtain ⟨_,_,_,rfl⟩ := World.write_value_update install
      rfl

theorem Allocates.fresh_root {program : Program} {before after : World}
    {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after) :
    address.root = before.nextRoot ∧ after.nextRoot = before.nextRoot + 1 := by
  cases allocated
  exact ⟨rfl,rfl⟩

end Glorious.Language
