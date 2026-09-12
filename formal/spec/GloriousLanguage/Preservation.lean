import GloriousLanguage.Typing

/-! Preservation obligations for the actual storage and execution relations.
No result in this module assumes `ResourceAdmission` or the safety conclusion
it proves. The whole-machine preservation/progress proof is still in progress. -/
namespace Glorious.Language

theorem Table.mem_of_get {α : Type} {table : Table α} {id : Identity} {value : α}
    (found : table.get id = some value) : (id,value) ∈ table := by
  induction table with
  | nil => simp [Table.get] at found
  | cons entry rest ih =>
      rcases entry with ⟨key,resident⟩
      by_cases same : key = id
      · subst key
        have equal : resident = value := by simpa [Table.get] using found
        subst resident
        exact List.mem_cons_self
      · have later : Table.get rest id = some value := by simpa [Table.get,same] using found
        exact List.mem_cons_of_mem _ (ih later)

theorem World.root_found {world : World} {address : Address} {root : Root}
    (selected : world.root address = some root) :
    world.roots.get address.root = some root ∧ root.live = true ∧ root.generation = address.generation := by
  unfold World.root at selected
  cases found : world.roots.get address.root with
  | none => simp [found] at selected
  | some resident =>
      simp only [found] at selected
      dsimp at selected
      split at selected
      next valid =>
        have same := Option.some.inj selected
        subst resident
        exact ⟨rfl,by simpa using valid⟩
      next => contradiction

/-- Even a nested write changes only the resident tree, never the declared
storage location, layout, generation, region or liveness of its root. -/
theorem World.write_value_update {before after : World} {address : Address} {value : Option Value}
    (written : before.write address value = some after) :
    ∃ root replacement, before.roots.get address.root = some root ∧
      after = { before with roots := before.roots.set address.root { root with value := replacement } } := by
  unfold World.write at written
  cases selected : before.root address with
  | none => simp [selected] at written
  | some root =>
      have found := (World.root_found selected).1
      simp only [selected] at written
      dsimp at written
      split at written
      next => exact ⟨root,value,found,(Option.some.inj written).symm⟩
      next =>
        cases resident : root.value with
        | none => simp [resident] at written
        | some tree =>
            simp only [resident] at written
            dsimp at written
            cases replaced : tree.replace address.fields value with
            | none => simp [replaced] at written
            | some changed =>
                simp only [replaced] at written
                dsimp at written
                exact ⟨root,some changed,found,(Option.some.inj written).symm⟩

def Root.location (root : Root) : Root := { root with value := none }

theorem World.write_locations {before after : World} {address : Address} {value : Option Value}
    (written : before.write address value = some after) (id : Identity) :
    (after.roots.get id).map Root.location = (before.roots.get id).map Root.location := by
  rcases World.write_value_update written with ⟨root,replacement,found,rfl⟩
  by_cases same : id = address.root
  · subst id
    rw [Table.get_set,found]
    rfl
  · rw [Table.get_set_other _ _ _ _ same]

theorem World.write_loans {before after : World} {address : Address} {value : Option Value}
    (written : before.write address value = some after) : after.loans = before.loans := by
  rcases World.write_value_update written with ⟨_,_,_,rfl⟩
  rfl

theorem Transfers.locations {program : Program} {before after : World} {authority source destination}
    (transfer : Transfers program before authority source destination after) (id : Identity) :
    (after.roots.get id).map Root.location = (before.roots.get id).map Root.location := by
  cases transfer with
  | move _ _ _ _ _ _ clear install =>
      exact (World.write_locations install id).trans (World.write_locations clear id)

theorem Transfers.loans {program : Program} {before after : World} {authority source destination}
    (transfer : Transfers program before authority source destination after) : after.loans = before.loans := by
  cases transfer with
  | move _ _ _ _ _ _ clear install =>
      exact (World.write_loans install).trans (World.write_loans clear)

theorem Transfers.destination_type {program : Program} {before after : World} {authority source destination value}
    (transfer : Transfers program before authority source destination after) (stored : before.Stores source value) :
    AddressType program before destination value.type := by
  cases transfer with
  | move found _ _ _ _ typed _ _ =>
      have same := Option.some.inj (stored.symm.trans found)
      subst same
      exact typed

theorem Copies.destination_type {program : Program} {before after : World} {authority source destination value}
    (copy : Copies program before authority source destination after) (stored : before.Stores source value) :
    AddressType program before destination value.type := by
  cases copy with
  | copy found _ _ _ typed _ _ =>
      have same := Option.some.inj (stored.symm.trans found)
      subst same
      exact typed

theorem NewValue.destination_type {program : Program} {before after : World} {destination type head sources}
    (constructed : NewValue program before destination type head sources after) : AddressType program before destination type := by
  cases constructed
  assumption

theorem AddressType.root_iff {program : Program} {world : World} {address : Address} {type : Term}
    (whole : address.fields = []) :
    AddressType program world address type ↔ ∃ root, world.root address = some root ∧ root.type = type := by
  constructor
  · rintro ⟨offset,typed⟩
    cases typed with
    | root found live => exact ⟨_,by simp [World.root,found,live],rfl⟩
    | child _ _ => simp [Address.child] at whole
  · rintro ⟨root,selected,rfl⟩
    obtain ⟨found,live,generation⟩ := World.root_found selected
    rcases address with ⟨id,epoch,fields⟩
    change fields = [] at whole
    subst fields
    change root.generation = epoch at generation
    subst epoch
    exact ⟨0,.root found live⟩

theorem AddressType.root_transport {program : Program} {before after : World} {address : Address} {type : Term}
    (locations : ∀ id, (after.roots.get id).map Root.location = (before.roots.get id).map Root.location)
    (whole : address.fields = []) (typed : AddressType program before address type) :
    AddressType program after address type := by
  rcases (AddressType.root_iff whole).mp typed with ⟨root,selected,typeEq⟩
  obtain ⟨found,live,generation⟩ := World.root_found selected
  have location := locations address.root
  rw [found] at location
  cases changed : after.roots.get address.root with
  | none => simp [changed] at location
  | some resident =>
      rw [changed] at location
      have same := Option.some.inj location
      have residentType : resident.type = root.type := by simpa [Root.location] using congrArg Root.type same
      have residentGeneration : resident.generation = root.generation := by simpa [Root.location] using congrArg Root.generation same
      have residentLive : resident.live = root.live := by simpa [Root.location] using congrArg Root.live same
      apply (AddressType.root_iff whole).mpr
      exact ⟨resident,by simp [World.root,changed,residentLive,live,residentGeneration,generation],residentType.trans typeEq⟩

theorem Transfers.root_types {program : Program} {before after : World} {authority source destination}
    (transfer : Transfers program before authority source destination after) {address : Address} {type : Term}
    (whole : address.fields = []) : AddressType program before address type ↔ AddressType program after address type := by
  constructor
  · exact AddressType.root_transport transfer.locations whole
  · exact AddressType.root_transport (fun id => (transfer.locations id).symm) whole

/-- A retained reference to a whole storage location remains typed across a
transfer, even when that location is the consumed source. Initialization and
loan-ending obligations are separate; this does not authorize reading a hole. -/
theorem Transfers.reference_root_typed {program : Kernel.Program} {before after : World}
    {authority source destination owner mode region type id loan live}
    (transfer : Transfers program.declarations before authority source destination after)
    (found : before.loans.get id = some loan) (whole : loan.referent.fields = [])
    (typed : Typing.ValueTyped program before
      (.resident owner (.reference mode region type) (.reference id) live [])) :
    Typing.ValueTyped program after (.resident owner (.reference mode region type) (.reference id) live []) := by
  cases typed with
  | aggregate head _ =>
      rcases head with ⟨_,_,impossible⟩ | ⟨_,_,_,_,_,_,impossible,_⟩ | ⟨_,_,_,_,_,_,_,impossible,_⟩ <;> cases impossible
  | reference selected active modeEq regionEq located =>
      have same := Option.some.inj (found.symm.trans selected)
      subst same
      exact .reference (by simpa [transfer.loans] using found) active modeEq regionEq
        ((transfer.root_types whole).mp located)

end Glorious.Language
