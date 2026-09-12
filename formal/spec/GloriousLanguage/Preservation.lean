import GloriousLanguage.Typing

/-! Preservation obligations for the actual storage and execution relations.
No result in this module assumes `ResourceAdmission` or the safety conclusion
it proves. The whole-machine preservation/progress proof is still in progress. -/
namespace Glorious.Language

/-- Proof projection, not additional runtime state: nested field writes retain
the resident's identity, type, constructor and shell-liveness. -/
def Value.shell (value : Value) : Value := value.withFields []

theorem Value.replace_cons_shape {before after : Value} {index : Nat} {path : List Nat}
    {replacement : Option Value} (written : before.replace (index :: path) replacement = some after) :
    ∃ field, before.fields[index]? = some field ∧
      ((path = [] ∧ after = before.withFields (before.fields.set index replacement)) ∨
       ∃ child changed, field = some child ∧ child.replace path replacement = some changed ∧
         after = before.withFields (before.fields.set index (some changed))) := by
  unfold Value.replace at written
  cases found : before.fields[index]? with
  | none => simp [found] at written
  | some field =>
      refine ⟨field,rfl,?_⟩
      simp only [found] at written
      dsimp at written
      split at written
      next empty =>
        exact Or.inl ⟨by simpa using empty,(Option.some.inj written).symm⟩
      next =>
        cases field with
        | none => simp at written
        | some child =>
            dsimp at written
            cases replaced : child.replace path replacement with
            | none => simp [replaced] at written
            | some changed =>
                simp only [replaced] at written
                dsimp at written
                exact Or.inr ⟨child,changed,rfl,replaced,(Option.some.inj written).symm⟩

theorem Value.replace_shell {before after : Value} {path : List Nat} {replacement : Option Value}
    (written : before.replace path replacement = some after) (nonempty : path ≠ []) :
    after.shell = before.shell := by
  cases path with
  | nil => exact False.elim (nonempty rfl)
  | cons index path =>
      rcases Value.replace_cons_shape written with ⟨_,_,⟨_,rfl⟩ | ⟨_,_,_,_,rfl⟩⟩ <;> rfl

/-- A write cannot change an ancestor's constructor or any sibling subtree.
The excluded case is exactly an observation inside the replaced subtree. -/
theorem Value.replace_atPath_shell {before after : Value} {path observed : List Nat}
    {replacement : Option Value} (written : before.replace path replacement = some after)
    (outside : ¬ ∃ suffix, observed = path ++ suffix) :
    (after.atPath observed).map Value.shell = (before.atPath observed).map Value.shell := by
  induction path generalizing before after observed with
  | nil => exact False.elim (outside ⟨observed,rfl⟩)
  | cons index path ih =>
      cases observed with
      | nil =>
          simpa [Value.atPath] using Value.replace_shell written (by simp)
      | cons other observed =>
          rcases Value.replace_cons_shape written with ⟨field,found,⟨rfl,rfl⟩ | ⟨child,changed,rfl,replaced,rfl⟩⟩
          · have different : index ≠ other := by
              intro same
              subst other
              exact outside ⟨observed,rfl⟩
            simp [Value.atPath,Value.withFields,Value.fields,List.getElem?_set_ne different]
          · by_cases same : index = other
            · subst other
              have inBounds : index < before.fields.length := List.getElem?_eq_some_iff.mp found |>.1
              have restOutside : ¬ ∃ suffix, observed = path ++ suffix := by
                rintro ⟨suffix,equal⟩
                exact outside ⟨suffix,by simp [equal]⟩
              change (((before.fields.set index (some changed))[index]?).join >>= fun value => value.atPath observed).map Value.shell =
                ((before.fields[index]?).join >>= fun value => value.atPath observed).map Value.shell
              rw [List.getElem?_set_self inBounds,found]
              exact ih replaced restOutside
            · simp [Value.atPath,Value.withFields,Value.fields,List.getElem?_set_ne same]

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

/-- Geometric proof predicates over the existing address path. They carry no
additional storage identity or independently inferred field information. -/
def Address.Prefix (ancestor descendant : Address) : Prop :=
  ancestor.root = descendant.root ∧ ancestor.generation = descendant.generation ∧
    ∃ suffix, descendant.fields = ancestor.fields ++ suffix

def Address.ProperPrefix (ancestor descendant : Address) : Prop :=
  ancestor.Prefix descendant ∧ ancestor.fields.length < descendant.fields.length

theorem Address.Prefix.child {ancestor descendant : Address} (included : ancestor.Prefix descendant) (index : Nat) :
    ancestor.ProperPrefix (descendant.child index) := by
  rcases included with ⟨root,generation,suffix,fields⟩
  refine ⟨⟨root,generation,suffix ++ [index],?_⟩,?_⟩
  · simp [Address.child,fields,List.append_assoc]
  · simp [Address.child,fields]

theorem World.write_read_shell {before after : World} {address observed : Address} {value : Option Value}
    (written : before.write address value = some after) (outside : ¬ address.Prefix observed) :
    (after.read observed).map Value.shell = (before.read observed).map Value.shell := by
  have update := World.write_value_update written
  unfold World.write at written
  cases selected : before.root address with
  | none => simp [selected] at written
  | some root =>
      obtain ⟨found,live,generation⟩ := World.root_found selected
      simp only [selected] at written
      dsimp at written
      by_cases sameRoot : observed.root = address.root
      · by_cases sameGeneration : observed.generation = address.generation
        · have pathOutside : ¬ ∃ suffix, observed.fields = address.fields ++ suffix :=
            fun included => outside ⟨sameRoot.symm,sameGeneration.symm,included⟩
          split at written
          next empty =>
            have fields : address.fields = [] := by simpa using empty
            exact False.elim (pathOutside ⟨observed.fields,by simp [fields]⟩)
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
                    cases (Option.some.inj written).symm
                    have observedGeneration : root.generation = observed.generation := generation.trans sameGeneration.symm
                    have unchanged := Value.replace_atPath_shell replaced pathOutside
                    simpa [World.read,World.root,Table.get_set,sameRoot,found,live,observedGeneration,resident]
                      using unchanged
        · rcases update with ⟨changedRoot,_,changedFound,equal⟩
          have same := Option.some.inj (changedFound.symm.trans found)
          subst changedRoot
          subst after
          have different : root.generation ≠ observed.generation := by omega
          simp [World.read,World.root,sameRoot,Table.get_set,found,live,different]
      · rcases update with ⟨_,_,_,equal⟩
        subst after
        simp [World.read,World.root,Table.get_set_other _ _ _ _ sameRoot]

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

theorem FieldOffset.transport {program : Program} {before after : World}
    {address : Address} {container type : Term} {index offset : Nat}
    (shells : (after.read address).map Value.shell = (before.read address).map Value.shell)
    (field : FieldOffset program before address container index type offset) :
    FieldOffset program after address container index type offset := by
  cases field with
  | tuple selected layouts layout offset => exact .tuple selected layouts layout offset
  | bindings selected layouts layout offset => exact .bindings selected layouts layout offset
  | callable captures selected layouts layout offset => exact .callable captures selected layouts layout offset
  | array nonnegative bound layout => exact .array nonnegative bound layout
  | nominal constructor id instantiated substituted selected layout stored head offset =>
      change before.read address = some _ at stored
      rw [stored] at shells
      cases found : after.read address with
      | none => simp [found] at shells
      | some resident =>
          rw [found] at shells
          have same := Option.some.inj shells
          have sameHead := congrArg Value.head same
          simp only [Value.shell,Value.withFields,Value.head] at sameHead
          exact .nominal constructor id instantiated substituted selected layout found (sameHead.trans head) offset

/-- The shared address/layout derivation survives a write except beneath a
replaced proper ancestor. The address being written may itself become vacant. -/
theorem AddressOffset.transport {program : Program} {before after : World} {mutation address : Address}
    {type : Term} {offset : Nat}
    (locations : ∀ id, (after.roots.get id).map Root.location = (before.roots.get id).map Root.location)
    (shells : ∀ observed, ¬ mutation.Prefix observed →
      (after.read observed).map Value.shell = (before.read observed).map Value.shell)
    (outside : ¬ mutation.ProperPrefix address) (typed : AddressOffset program before address type offset) :
    AddressOffset program after address type offset := by
  induction typed with
  | @root id root found live =>
      have location := locations id
      rw [found] at location
      cases changed : after.roots.get id with
      | none => simp [changed] at location
      | some resident =>
          rw [changed] at location
          have same := Option.some.inj location
          have residentType : resident.type = root.type := by simpa [Root.location] using congrArg Root.type same
          have residentGeneration : resident.generation = root.generation := by simpa [Root.location] using congrArg Root.generation same
          have residentLive : resident.live = true := by simpa [Root.location,live] using congrArg Root.live same
          simpa only [residentType,residentGeneration] using (AddressOffset.root (program := program) changed residentLive)
  | @child parent container parentOffset index type childOffset _ field ih =>
      have parentOutside : ¬ mutation.Prefix parent := fun included => outside (included.child index)
      exact .child (ih (fun included => parentOutside included.1)) (field.transport (shells parent parentOutside))

theorem World.write_address_offsets {program : Program} {before after : World} {mutation address : Address}
    {type : Term} {offset : Nat} {value : Option Value}
    (written : before.write mutation value = some after) (outside : ¬ mutation.ProperPrefix address) :
    AddressOffset program before address type offset ↔ AddressOffset program after address type offset := by
  constructor
  · exact AddressOffset.transport (World.write_locations written) (fun _ => World.write_read_shell written) outside
  · exact AddressOffset.transport (fun id => (World.write_locations written id).symm)
      (fun _ separate => (World.write_read_shell written separate).symm) outside

theorem World.write_address_types {program : Program} {before after : World} {mutation address : Address}
    {type : Term} {value : Option Value}
    (written : before.write mutation value = some after) (outside : ¬ mutation.ProperPrefix address) :
    AddressType program before address type ↔ AddressType program after address type := by
  exact exists_congr (fun _ => World.write_address_offsets written outside)

theorem Transfers.address_types {program : Program} {before after : World} {authority source destination}
    (transfer : Transfers program before authority source destination after) {address : Address} {type : Term}
    (sourceOutside : ¬ source.ProperPrefix address) (destinationOutside : ¬ destination.ProperPrefix address) :
    AddressType program before address type ↔ AddressType program after address type := by
  cases transfer with
  | move _ _ _ _ _ _ clear install =>
      exact (World.write_address_types clear sourceOutside).trans (World.write_address_types install destinationOutside)

/-- A retained reference remains typed across a transfer outside its proper
ancestors. Deriving that side condition for every live loan is a separate
world-invariant obligation; initialization and loan ending remain separate. -/
theorem Transfers.reference_typed {program : Kernel.Program} {before after : World}
    {authority source destination owner mode region type id loan live}
    (transfer : Transfers program.declarations before authority source destination after)
    (found : before.loans.get id = some loan)
    (sourceOutside : ¬ source.ProperPrefix loan.referent) (destinationOutside : ¬ destination.ProperPrefix loan.referent)
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
        ((transfer.address_types sourceOutside destinationOutside).mp located)

theorem Transfers.reference_root_typed {program : Kernel.Program} {before after : World}
    {authority source destination owner mode region type id loan live}
    (transfer : Transfers program.declarations before authority source destination after)
    (found : before.loans.get id = some loan) (whole : loan.referent.fields = [])
    (typed : Typing.ValueTyped program before
      (.resident owner (.reference mode region type) (.reference id) live [])) :
    Typing.ValueTyped program after (.resident owner (.reference mode region type) (.reference id) live []) := by
  apply transfer.reference_typed found ?_ ?_ typed <;>
    rintro ⟨_,length⟩ <;> simp [whole] at length

end Glorious.Language
