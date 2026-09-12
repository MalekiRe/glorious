import GloriousLanguage.StorageConstruction

/-! The actual unit-result installer shares the total vacant write and
empty-input value producer used by other primitive results. -/
namespace Glorious.Language.Execution

theorem StoresUnit.exists {program : Kernel.Program} {before : World} {destination : Address}
    (destinationType : DestinationType before destination .unit) :
    ∃ after, StoresUnit program before destination after := by
  obtain ⟨after,constructed⟩ := NewValue.empty_exists .unit
    destinationType.vacant destinationType.addressType
  exact ⟨after,destinationType,constructed⟩

theorem StoresUnit.worldTyped {program : Kernel.Program} {before after : World} {destination}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (stored : StoresUnit program before destination after) : Typing.WorldTyped program after :=
  stored.2.empty_worldTyped valid inventory typed (by simp) (by simp) .unit

theorem StoresUnit.typed_result {program : Kernel.Program} {before after : World} {destination : Address}
    (stored : StoresUnit program before destination after) :
    ∃ value, after.Stores destination value ∧ Typing.ValueTyped program after value ∧
      value.type = .unit ∧ value.head = .unit := by
  obtain ⟨_,constructed⟩ := stored
  cases constructed with
  | construct _ _ ready _ cleared written =>
    have sources := ready.1
    cases sources
    cases cleared
    refine ⟨.resident before.nextOwner .unit .unit true [],?_,.unit,rfl,rfl⟩
    have found := World.write_read_inside written []
    simpa [Value.atPath,World.Stores,World.read,World.root] using found

theorem StoresUnit.actual_write {program : Kernel.Program} {before after : World} {destination : Address}
    (stored : StoresUnit program before destination after) :
    ∃ written, before.write destination (some (.resident before.nextOwner .unit .unit true [])) = some written ∧
      after = { written with nextOwner := before.nextOwner+1 } := by
  obtain ⟨_,constructed⟩ := stored
  cases constructed with
  | construct _ _ ready _ cleared written =>
    have sources := ready.1
    cases sources
    cases cleared
    exact ⟨_,written,rfl⟩

theorem StoresUnit.locations {program : Kernel.Program} {before after : World} {destination : Address}
    (stored : StoresUnit program before destination after) (id : Identity) :
    (after.roots.get id).map Root.location = (before.roots.get id).map Root.location := by
  obtain ⟨_,written,rfl⟩ := stored.actual_write
  exact World.write_locations written id

theorem StoresUnit.loans {program : Kernel.Program} {before after : World} {destination : Address}
    (stored : StoresUnit program before destination after) : after.loans = before.loans := by
  obtain ⟨_,written,rfl⟩ := stored.actual_write
  have same := World.write_loans written
  exact same

theorem StoresUnit.read_disjoint {program : Kernel.Program} {before after : World} {destination address : Address}
    (stored : StoresUnit program before destination after) (apart : ¬ destination.Overlaps address) :
    after.read address = before.read address := by
  obtain ⟨_,written,rfl⟩ := stored.actual_write
  have same := World.write_disjoint written apart
  exact same

/-- A raw mutation's unit result preserves the actual transferred payload's
whole resource graph when its result slot was in the protected write footprint. -/
theorem StoresUnit.resourcesAccessible {program : Kernel.Program} {before after : World}
    {destination : Address} {value : Value} {access : Access}
    (stored : StoresUnit program before destination after)
    (ready : value.ResourcesAccessible program before access) (outside : value.SupportOutside before destination) :
    value.ResourcesAccessible program after access :=
  ready.frame (.of_locations stored.locations) stored.loans
    (fun address supported => ⟨stored.read_disjoint (outside address supported),stored.locations address.root⟩)

end Glorious.Language.Execution
