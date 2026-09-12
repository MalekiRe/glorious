import GloriousLanguage.BufferAllocationPreservation

/-! The actual bulk move preserves the one evaluated resident snapshot through
clear and installation, including every owner and retained resource field. -/
namespace Glorious.Language
namespace Memory

theorem InstallsResidents.rest {program : Program} {before after : World} {addresses : List Address} {values : List (Option Value)}
    (installed : InstallsResidents program before addresses values after) : after = { before with roots := after.roots } := by
  induction installed with
  | nil => rfl
  | hole _ _ ih => exact ih
  | resident _ _ written _ ih =>
    have first := World.write_rest written
    conv => lhs; rw [ih,first]

theorem InstallsResidents.locations {program : Program} {before after : World} {addresses : List Address} {values : List (Option Value)}
    (installed : InstallsResidents program before addresses values after) (id : Identity) :
    (after.roots.get id).map Root.location = (before.roots.get id).map Root.location := by
  induction installed with
  | nil => rfl
  | hole _ _ ih => exact ih
  | resident _ _ written _ ih => exact ih.trans (World.write_locations written id)

theorem InstallsResidents.resident_origin {program : Program} {before after : World}
    {addresses : List Address} {values : List (Option Value)}
    (installed : InstallsResidents program before addresses values after)
    {address : Address} {value : Value} (resident : after.Resident address value) :
    (∃ original, before.Resident address original ∧ value.shell = original.shell) ∨
      ∃ input, some input ∈ values ∧ ∃ path original,
        ResidentAt input path original ∧ value.shell = original.shell := by
  induction installed with
  | nil => exact Or.inl ⟨value,resident,rfl⟩
  | hole _ _ ih =>
      rcases ih resident with old | ⟨input,member,path,original,inside,same⟩
      · exact Or.inl old
      · exact Or.inr ⟨input,List.mem_cons_of_mem _ member,path,original,inside,same⟩
  | resident _ _ written _ ih =>
      rcases ih resident with ⟨middle,found,last⟩ | ⟨input,member,path,original,inside,same⟩
      · rcases World.write_value_origin written found with ⟨path,_,inside⟩ | ⟨original,old,first⟩
        · exact Or.inr ⟨_,List.mem_cons_self,path,middle,inside,last⟩
        · exact Or.inl ⟨original,old,last.trans first⟩
      · exact Or.inr ⟨input,List.mem_cons_of_mem _ member,path,original,inside,same⟩

theorem InstallsResidents.read_disjoint {program : Program} {before after : World}
    {addresses : List Address} {values : List (Option Value)}
    (installed : InstallsResidents program before addresses values after) {address : Address}
    (apart : ∀ mutation ∈ addresses, ¬ mutation.Overlaps address) : after.read address = before.read address := by
  induction installed with
  | nil => rfl
  | hole _ _ ih => exact ih (fun mutation member => apart mutation (List.mem_cons_of_mem _ member))
  | resident _ _ written _ ih =>
      exact (ih (fun mutation member => apart mutation (List.mem_cons_of_mem _ member))).trans
        (World.write_disjoint written (apart _ List.mem_cons_self))

theorem BulkMove.rest {program : RuntimeProgram} {before after : World} {sources destinations : List ResolvedPlace}
    (moved : BulkMove program before sources destinations after) : after = { before with roots := after.roots } := by
  obtain ⟨_,_,_,_,_,_,_,_,cleared,installed⟩ := moved
  conv => lhs; rw [installed.rest,cleared.rest]

theorem BulkMove.locations {program : RuntimeProgram} {before after : World} {sources destinations : List ResolvedPlace}
    (moved : BulkMove program before sources destinations after) (id : Identity) :
    (after.roots.get id).map Root.location = (before.roots.get id).map Root.location := by
  obtain ⟨_,_,_,_,_,_,_,_,cleared,installed⟩ := moved
  exact (installed.locations id).trans (cleared.locations id)

/-- Every resulting resident shell comes from the actual pre-move world,
including the subtrees of the evaluated source snapshot. -/
theorem BulkMove.resident_origin {program : RuntimeProgram} {before after : World} {sources destinations : List ResolvedPlace}
    (moved : BulkMove program before sources destinations after) {address : Address} {value : Value}
    (resident : after.Resident address value) :
    ∃ oldAddress original, before.Resident oldAddress original ∧ value.shell = original.shell := by
  obtain ⟨_,_,_,_,_,snapshot,_,_,cleared,installed⟩ := moved
  rcases installed.resident_origin resident with ⟨middle,found,last⟩ | ⟨input,member,path,original,inside,same⟩
  · obtain ⟨original,old,first⟩ := cleared.resident_origin found
    exact ⟨address,original,old,last.trans first⟩
  · obtain ⟨index,selected⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨source,_,stored⟩ := snapshot.get_right selected
    exact ⟨_,original,World.Stores.residentAt stored inside,same⟩

theorem BulkMove.references_before {program : RuntimeProgram} {before after : World} {sources destinations : List ResolvedPlace}
    (moved : BulkMove program before sources destinations after) {id : Identity}
    (referenced : after.References id) : before.References id := by
  obtain ⟨address,value,resident,head⟩ := referenced
  obtain ⟨oldAddress,original,found,same⟩ := moved.resident_origin resident
  have headEq : value.head = original.head := by
    simpa only [Value.shell,Value.withFields,Value.head] using congrArg Value.head same
  exact ⟨oldAddress,original,found,headEq.symm.trans head⟩

theorem BulkMove.resourceReferences_before {program : RuntimeProgram} {before after : World} {sources destinations : List ResolvedPlace}
    (moved : BulkMove program before sources destinations after) {id : Identity}
    (referenced : after.ResourceReferences id) : before.ResourceReferences id := by
  obtain ⟨address,value,binding,resident,member,parent⟩ := referenced
  obtain ⟨oldAddress,original,found,same⟩ := moved.resident_origin resident
  have resources : value.resources = original.resources := by
    simpa only [Value.shell,Value.withFields,Value.resources] using congrArg Value.resources same
  exact ⟨oldAddress,original,binding,found,resources ▸ member,parent⟩

theorem InstallsResidents.worldTyped {program : Kernel.Program} {before after : World}
    {addresses : List Address} {values : List (Option Value)}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (checked : ∀ (index : Nat) value, values[index]? = some (some value) → Typing.ValueTyped program before value)
    (owners : ∀ (index : Nat) value, values[index]? = some (some value) →
      ∀ path resident, ResidentAt value path resident → resident.owner < before.nextOwner)
    (unique : ∀ (first second : Nat) left right x y a b,
      values[first]? = some (some x) → values[second]? = some (some y) →
      ResidentAt x left a → ResidentAt y right b → a.owner = b.owner → first = second ∧ left = right)
    (separate : ∀ (index : Nat) value, values[index]? = some (some value) →
      ∀ path resident, ResidentAt value path resident →
        ∀ address original, before.Resident address original → resident.owner ≠ original.owner)
    (packs : ∀ (index : Nat) value, values[index]? = some (some value) →
      ∀ path resident pack, ResidentAt value path resident → resident.head = .bindings pack →
        pack.brand < before.nextProof ∧ pack.region ∈ before.liveRegions ∧ pack.fields.length = resident.fields.length ∧
        pack.fields.Nodup ∧ ∀ fact ∈ pack.facts, fact.resultOrigin < before.nextOwner)
    (references : ∀ (index : Nat) value, values[index]? = some (some value) →
      ∀ path resident id, ResidentAt value path resident → resident.head = .reference id →
        ∃ loan, before.loans.get id = some loan ∧ loan.live = true)
    (installed : InstallsResidents program.declarations before addresses values after) : Typing.WorldTyped program after := by
  induction installed with
  | nil => exact typed
  | hole vacant rest ih =>
    exact ih typed (fun index value found => checked (index+1) value found)
      (fun index value found => owners (index+1) value found)
      (fun first second left right x y a b one two inside nested same => by
        obtain ⟨indices,paths⟩ := unique (first+1) (second+1) left right x y a b one two inside nested same
        exact ⟨Nat.add_right_cancel indices,paths⟩)
      (fun index value found => separate (index+1) value found)
      (fun index value found => packs (index+1) value found)
      (fun index value found => references (index+1) value found)
  | @resident before destination addresses value values middle after vacant located written rest ih =>
    have middleTyped := World.install_owned_worldTyped valid inventory typed vacant located (checked 0 value rfl)
      (owners 0 value rfl)
      (fun a b x y first second same => (unique 0 0 a b value value x y rfl rfl first second same).2)
      (separate 0 value rfl) (packs 0 value rfl) (references 0 value rfl) written
    have first := World.write_rest written
    have counter := congrArg World.nextOwner first
    have proofs := congrArg World.nextProof first
    have regions := congrArg World.liveRegions first
    have loans := congrArg World.loans first
    apply ih middleTyped
    · intro index resident found
      exact (checked (index+1) resident found).write_vacant typed.1 vacant written
    · intro index resident found path nested inside
      simpa only [counter] using owners (index+1) resident found path nested inside
    · intro first second left right x y a b one two inside nested same
      obtain ⟨indices,paths⟩ := unique (first+1) (second+1) left right x y a b one two inside nested same
      exact ⟨Nat.add_right_cancel indices,paths⟩
    · intro index resident found path nested inside address original stored same
      rcases World.write_value_origin written stored with ⟨suffix,_,inFirst⟩ | ⟨old,oldFound,shell⟩
      · have impossible := (unique (index+1) 0 path suffix resident value nested original found rfl inside inFirst same).1
        omega
      · have ownersEq : original.owner = old.owner := by
          simpa only [Value.shell,Value.withFields,Value.owner] using congrArg Value.owner shell
        exact separate (index+1) resident found path nested inside address old oldFound (same.trans ownersEq)
    · intro index resident found path nested pack inside head
      simpa only [proofs,regions,counter] using packs (index+1) resident found path nested pack inside head
    · intro index resident found path nested id inside head
      simpa only [loans] using references (index+1) resident found path nested id inside head

theorem BulkMove.worldTyped {program : Kernel.Program} {before after : World} {sources destinations : List ResolvedPlace}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (moved : BulkMove program before sources destinations after) : Typing.WorldTyped program after := by
  obtain ⟨values,middle,length,sourceApart,destinationApart,inputs,permissions,vacant,cleared,installed⟩ := moved
  have allowed : ∀ address ∈ sources.map ResolvedPlace.address, ∃ authority, Permitted before authority .owned address := by
    intro address member
    obtain ⟨source,selected,equal⟩ := List.mem_map.mp member
    exact ⟨source.authority,equal ▸ (permissions source selected).1⟩
  have middleTyped := cleared.worldTyped typed allowed
  have counter := congrArg World.nextOwner cleared.rest
  have proofs := congrArg World.nextProof cleared.rest
  have regions := congrArg World.liveRegions cleared.rest
  have input : ∀ (index : Nat) value, values[index]? = some (some value) →
      ∃ source, sources[index]? = some source ∧ before.Stores source.address value := by
    intro index value found
    exact inputs.get_right found
  apply installed.worldTyped valid inventory middleTyped
  · intro index value found
    obtain ⟨source,_,stored⟩ := input index value found
    exact cleared.valueTyped typed.1 allowed (World.stores_typed typed.roots stored)
  · intro index value found path resident inside
    obtain ⟨source,_,stored⟩ := input index value found
    simpa only [counter] using World.owner_bound typed.1 (stored.residentAt inside)
  · intro first second left right x y a b one two inside nested same
    obtain ⟨firstSource,firstFound,firstStored⟩ := input first x one
    obtain ⟨secondSource,secondFound,secondStored⟩ := input second y two
    have addressEq := typed.1.2.2.2.2.2.2.2.1 _ _ a b
      (firstStored.residentAt inside) (secondStored.residentAt nested) same
    by_cases indices : first = second
    · subst second
      have sourceEq := Option.some.inj (firstFound.symm.trans secondFound)
      subst secondSource
      exact ⟨rfl,List.append_cancel_left (congrArg Address.fields addressEq)⟩
    · have apart := sourceApart.get_other (fun different overlap => different overlap.symm) firstFound secondFound indices
      apply False.elim
      apply apart
      apply Address.Prefix.overlap_of_common (common := { firstSource.address with fields := firstSource.address.fields ++ left })
      · exact ⟨rfl,rfl,left,rfl⟩
      · rw [addressEq]
        exact ⟨rfl,rfl,right,rfl⟩
  · intro index value found path resident inside address original current same
    obtain ⟨source,sourceFound,stored⟩ := input index value found
    obtain ⟨old,oldFound,shell⟩ := cleared.resident_origin current
    have ownerEq : original.owner = old.owner := by
      simpa only [Value.shell,Value.withFields,Value.owner] using congrArg Value.owner shell
    have addressEq := typed.1.2.2.2.2.2.2.2.1 _ _ resident old (stored.residentAt inside) oldFound (same.trans ownerEq)
    have absent := cleared.cleared (List.mem_map.mpr ⟨source,List.mem_of_getElem? sourceFound,rfl⟩) path
    rw [addressEq,World.resident_iff_stores.mp current] at absent
    cases absent
  · intro index value found path resident pack inside head
    obtain ⟨source,_,stored⟩ := input index value found
    simpa only [proofs,regions,counter] using
      typed.1.2.2.2.2.2.1 _ resident pack (stored.residentAt inside) head
  · intro index value found path resident id inside head
    obtain ⟨source,_,stored⟩ := input index value found
    simpa only [cleared.loans] using
      typed.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ resident id (stored.residentAt inside) head

end Memory
end Glorious.Language
