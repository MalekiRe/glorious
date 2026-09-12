import GloriousLanguage.Preservation

/-! Totality of the one partial storage write at its actual located-address
contract. Existing vacant initialization and owned transfer share this proof. -/
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

theorem World.Located.write_exists {world : World} {address : Address}
    (located : world.Located address) (replacement : Option Value) :
    ∃ after, world.write address replacement = some after := by
  rcases address with ⟨id,generation,fields⟩
  rcases List.eq_nil_or_concat fields with empty | ⟨parent,index,equation⟩
  · subst fields
    obtain ⟨root,selected⟩ := (World.Located.root_iff rfl).mp located
    exact ⟨{ world with roots := world.roots.set id { root with value := replacement } },
      by simp [World.write,selected]⟩
  · simp only [List.concat_eq_append] at equation
    subst fields
    change world.Located ((⟨id,generation,parent⟩ : Address).child index) at located
    obtain ⟨container,stored,bound⟩ := World.Located.child_iff.mp located
    obtain ⟨root,selected,contents⟩ := Option.bind_eq_some_iff.mp stored
    obtain ⟨whole,present,inside⟩ := Option.bind_eq_some_iff.mp contents
    have written : container.replace [index] replacement =
        some (container.withFields (container.fields.set index replacement)) := by
      simp [Value.replace,List.getElem?_eq_getElem bound]
    obtain ⟨changed,changedAt⟩ := Value.replace_extension_exists inside written
    have selectedFull : world.root ⟨id,generation,parent ++ [index]⟩ = some root := selected
    exact ⟨{ world with roots := world.roots.set id { root with value := some changed } },
      by simp [World.write,selectedFull,present,changedAt]⟩

theorem World.Vacant.write_exists {world : World} {address : Address}
    (vacant : world.Vacant address) (replacement : Option Value) :
    ∃ after, world.write address replacement = some after :=
  World.Located.write_exists (.inr vacant) replacement

theorem World.Stores.write_exists {world : World} {address : Address} {value : Value}
    (stored : world.Stores address value) (replacement : Option Value) :
    ∃ after, world.write address replacement = some after :=
  World.Located.write_exists (.inl ⟨value,stored⟩) replacement

/-- The read, permission, vacancy and handoff contracts construct the actual
clear/install transfer. Successful writes are conclusions, not extra inputs. -/
theorem Transfers.exists {program : RuntimeProgram} {before : World}
    {source destination : Address} {authority : Authority} {value : Value}
    (stored : before.Stores source value) (initialized : value.Initialized)
    (ready : value.MoveReady program before [source,destination])
    (permission : Permitted before authority .owned source) (vacant : before.Vacant destination)
    (separated : ¬ source.Overlaps destination) (type : AddressType program.declarations before destination value.type) :
    ∃ after, Transfers program before authority source destination after := by
  obtain ⟨cleared,clear⟩ := stored.write_exists none
  have located := World.write_located clear (fun included => separated included.1.overlaps) (.inr vacant)
  obtain ⟨after,install⟩ := located.write_exists (some value)
  exact ⟨after,.move stored initialized ready permission vacant separated type clear install⟩

end Glorious.Language
