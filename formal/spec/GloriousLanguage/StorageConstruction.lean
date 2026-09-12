import GloriousLanguage.ConstructionPreservation

/-! Constructibility of the common vacant-storage write and empty-input value
producer. Scalar results and continuation handles consume this same relation;
an actual allocation is separate from initialization and may fail physically. -/
namespace Glorious.Language

theorem Value.replace_extension_exists {before container changed : Value}
    {parent suffix : List Nat} {replacement : Option Value}
    (located : before.atPath parent = some container)
    (written : container.replace suffix replacement = some changed) :
    ∃ after, before.replace (parent ++ suffix) replacement = some after := by
  induction parent generalizing before with
  | nil =>
      have same : before = container := Option.some.inj located
      subst container
      exact ⟨changed,written⟩
  | cons index rest ih =>
      simp only [Value.atPath] at located
      cases found : before.fields[index]? with
      | none => simp [found] at located
      | some slot =>
          cases slot with
          | none => simp [found] at located
          | some child =>
              have nested : child.atPath rest = some container := by simpa [found] using located
              obtain ⟨after,replaced⟩ := ih nested
              exact ⟨_,Value.replace_cons found replaced⟩

/-- Every actual hole is writable, including a field beneath a resident
ancestor. This proves totality of the existing partial write at its contract. -/
theorem World.Vacant.write_exists {world : World} {address : Address}
    (vacant : world.Vacant address) (replacement : Option Value) :
    ∃ after, world.write address replacement = some after := by
  obtain ⟨root,selected,⟨empty,_⟩ | ⟨parent,index,value,path,contents,container,located,slot⟩⟩ := vacant
  · exact ⟨{ world with roots := world.roots.set address.root { root with value := replacement } },
      by simp [World.write,selected,empty]⟩
  · have written : container.replace [index] replacement =
        some (container.withFields (container.fields.set index replacement)) := by
      simp [Value.replace,slot]
    obtain ⟨changed,changedAt⟩ := Value.replace_extension_exists located written
    exact ⟨{ world with roots := world.roots.set address.root { root with value := some changed } },
      by simp [World.write,selected,path,contents,changedAt]⟩

theorem NewValue.empty_exists {program : Program} {before : World} {destination : Address}
    {type : Term} (head : ValueHead) (vacant : before.Vacant destination)
    (typed : AddressType program before destination type) :
    ∃ after, NewValue program before destination type head [] after := by
  obtain ⟨after,written⟩ := vacant.write_exists (some (.resident before.nextOwner type head true []))
  refine ⟨_,NewValue.construct vacant typed .nil ?_ ?_ ?_ .nil written⟩
  · simp
  · exact .nil
  · simp

/-- A successful fresh allocation supplies both actual vacancy and its
declared address type. Initialization is constructed, not an allocation input. -/
theorem Allocates.empty_value {program : Program} {before allocated : World}
    {home region type layout mutable address}
    (allocation : Allocates program before home region type layout mutable address allocated) (head : ValueHead) :
    ∃ after, NewValue program allocated address type head [] after :=
  NewValue.empty_exists head allocation.created_vacant allocation.created_addressType

end Glorious.Language
