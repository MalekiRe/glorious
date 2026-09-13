import GloriousLanguage.ClearPreservation
import GloriousLanguage.ReferencePersistence

/-! The common resident-shell mutation and fresh-region boundary. Runtime
resources are retained by the actual write; typing uses the shared transport. -/
namespace Glorious.Language

theorem Value.replace_resident_type {before after resident replacement : Value} {path : List Nat}
    (found : before.atPath path = some resident)
    (written : before.replace path (some replacement) = some after)
    (same : replacement.type = resident.type) : after.type = before.type := by
  cases path with
  | nil =>
      have original := Option.some.inj found
      have result := Option.some.inj written
      simpa only [← original,← result] using same
  | cons index path =>
      simpa [Value.shell,Value.withFields,Value.type] using congrArg Value.type (Value.replace_shell written (by simp))

theorem Typing.ValueTyped.replace_resident {program : Kernel.Program} {world : World}
    {before after resident replacement : Value} {path : List Nat}
    (typed : Typing.ValueTyped program world before) (found : before.atPath path = some resident)
    (written : before.replace path (some replacement) = some after)
    (checked : Typing.ValueTyped program world replacement) (same : replacement.type = resident.type) :
    Typing.ValueTyped program world after := by
  induction path generalizing before after with
  | nil =>
      have equal := Option.some.inj written
      simpa only [← equal] using checked
  | cons index path ih =>
      obtain ⟨child,selected,inside⟩ := Option.bind_eq_some_iff.mp found
      have slot : before.fields[index]? = some (some child) := by
        cases field : before.fields[index]? <;> simp_all
      rcases Value.replace_cons_shape written with ⟨_,fieldFound,⟨rfl,rfl⟩ | ⟨original,changed,link,nested,rfl⟩⟩
      · have equal := Option.some.inj inside
        subst child
        exact typed.replace_child slot checked same
      · have equal : original = child := by
          exact (Option.some.inj ((Option.some.inj (slot.symm.trans fieldFound)).trans link)).symm
        subst original
        exact typed.replace_child slot (ih (typed.child slot) inside nested)
          (Value.replace_resident_type inside nested same)

theorem World.rewrite_typed_roots {program : Kernel.Program} {before after typingWorld : World}
    {address : Address} {resident replacement : Value}
    (roots : ∀ id root value, before.roots.get id = some root → root.live = true → root.value = some value →
      Typing.ValueTyped program typingWorld value ∧ value.type = root.type)
    (stored : before.Stores address resident) (written : before.write address (some replacement) = some after)
    (checked : Typing.ValueTyped program typingWorld replacement) (same : replacement.type = resident.type) :
    ∀ id root value, after.roots.get id = some root → root.live = true → root.value = some value →
      Typing.ValueTyped program typingWorld value ∧ value.type = root.type := by
  obtain ⟨original,selected,contents⟩ := Option.bind_eq_some_iff.mp stored
  obtain ⟨whole,present,inside⟩ := Option.bind_eq_some_iff.mp contents
  have originalFacts := World.root_found selected
  have wholeTyped := roots _ _ _ originalFacts.1 originalFacts.2.1 present
  unfold World.write at written
  simp only [selected] at written
  dsimp at written
  split at written
  next empty =>
    have fieldsEmpty : address.fields = [] := List.isEmpty_iff.mp empty
    have wholeEq : whole = resident := by simpa [fieldsEmpty,Value.atPath] using inside
    have result := Option.some.inj written
    subst after
    intro id root value found _ storedValue
    by_cases changed : id = address.root
    · subst id
      simp only [Table.get_set] at found
      cases found
      cases storedValue
      exact ⟨checked,same.trans (wholeEq ▸ wholeTyped.2)⟩
    · exact roots id root value (by simpa only [Table.get_set_other _ _ _ _ changed] using found)
        (by assumption) storedValue
  next nonempty =>
    simp only [present] at written
    dsimp at written
    cases replaced : whole.replace address.fields (some replacement) with
    | none => simp [replaced] at written
    | some changed =>
        simp only [replaced] at written
        dsimp at written
        have result := Option.some.inj written
        subst after
        intro id root value found live contents
        by_cases sameRoot : id = address.root
        · subst id
          simp only [Table.get_set] at found
          cases found
          cases contents
          exact ⟨wholeTyped.1.replace_resident inside replaced checked same,
            (Value.replace_resident_type inside replaced same).trans wholeTyped.2⟩
        · exact roots id root value (by simpa only [Table.get_set_other _ _ _ _ sameRoot] using found) live contents

theorem Typing.ValueTyped.shellLive {program : Kernel.Program} {world : World} {value : Value}
    (typed : Typing.ValueTyped program world value) (live : Bool) :
    Typing.ValueTyped program world (.resident value.owner value.type value.head live value.fields value.resources) := by
  cases typed <;> first
    | apply Typing.ValueTyped.unit
    | apply Typing.ValueTyped.scalar; assumption
    | apply Typing.ValueTyped.aggregate <;> assumption
    | apply Typing.ValueTyped.reference <;> assumption
    | apply Typing.ValueTyped.pointer <;> assumption
    | apply Typing.ValueTyped.callable <;> assumption
    | apply Typing.ValueTyped.operation; assumption
    | apply Typing.ValueTyped.label
    | apply Typing.ValueTyped.continuation; assumption
    | apply Typing.ValueTyped.available <;> assumption
    | apply Typing.ValueTyped.bindings <;> assumption

theorem World.write_shell_origin {before after : World} {address observed : Address} {resident value : Value} {live : Bool}
    (stored : before.Stores address resident)
    (written : before.write address (some (.resident resident.owner resident.type resident.head live resident.fields resident.resources)) = some after)
    (found : after.Resident observed value) : ∃ original,
    before.Resident observed original ∧ value.owner = original.owner ∧ value.head = original.head ∧
      value.fields.length = original.fields.length := by
  have valueFound := World.resident_iff_stores.mp found
  by_cases included : address.Prefix observed
  · obtain ⟨suffix,equal⟩ := Address.prefix_extension included
    have inside := World.write_read_inside written suffix
    rw [← equal,valueFound] at inside
    cases suffix with
    | nil =>
        have located : observed = address := by simpa using equal
        have same := Option.some.inj inside
        subst value
        exact ⟨resident,located ▸ World.resident_iff_stores.mpr stored,rfl,rfl,rfl⟩
    | cons index suffix =>
        refine ⟨value,World.resident_iff_stores.mpr ?_,rfl,rfl,rfl⟩
        change before.read observed = some value
        rw [equal,World.read_append,stored]
        exact inside.symm
  · have framed := World.write_read_shell written included
    rw [valueFound] at framed
    obtain ⟨original,selected,shell⟩ := Option.map_eq_some_iff.mp framed.symm
    refine ⟨original,World.resident_iff_stores.mpr selected,?_,?_,?_⟩
    · simpa [Value.shell,Value.withFields,Value.owner] using congrArg Value.owner shell.symm
    · simpa [Value.shell,Value.withFields,Value.head] using congrArg Value.head shell.symm
    · simpa [Value.shell,Value.withFields,Value.fields] using congrArg (fun value => value.fields.length) shell.symm

theorem World.write_shell_worldTyped {program : Kernel.Program} {before after : World}
    {address : Address} {authority : Authority} {resident : Value} {live : Bool}
    (typed : Typing.WorldTyped program before) (stored : before.Stores address resident)
    (permission : Permitted before authority .owned address)
    (written : before.write address
      (some (.resident resident.owner resident.type resident.head live resident.fields resident.resources)) = some after) :
    Typing.WorldTyped program after := by
  have checked := (typed.2.1 address resident (World.resident_iff_stores.mpr stored)).shellLive live
  have roots := World.rewrite_typed_roots typed.roots stored written checked rfl
  have rest := World.write_rest written
  have loansEq := congrArg World.loans rest
  have proofEq := congrArg World.availability rest
  refine ⟨World.write_wellFormed_of_origin typed.1 permission written
    (fun _ _ found => World.write_shell_origin stored written found),?_,?_,?_,
    typed.2.2.2.2.of_locations (World.write_locations written)⟩
  · intro observed value resident
    apply (World.stores_typed roots (World.resident_iff_stores.mp resident)).transport
      ?_ proofEq (fun _ origin => origin.transport (World.write_locations written))
    intro id loan found live
    exact ⟨by simpa only [loansEq] using found,fun _ type =>
      (World.write_address_types written
        (permission.owned_no_loan_descendant (World.loanParents typed.1) found live)).mp type⟩
  · intro id root value found contents
    by_cases live : root.live = true
    · exact (roots id root value found live contents).2
    · exact typed.2.2.1 id root value (World.write_dead_root written found live) contents
  · apply World.root_regions_transport typed.2.2.2.1 (World.write_locations written)
    exact Nat.le_of_eq (congrArg World.nextRegion rest).symm

theorem Deconstructs.worldTyped {program : Kernel.Program} {context : Context} {before after : World}
    {authority : Authority} {address : Address} (typed : Typing.WorldTyped program before)
    (consumed : Deconstructs program context before authority address after) :
    Typing.WorldTyped program after := by
  cases consumed with
  | shell stored _ permission _ _ written => exact World.write_shell_worldTyped typed stored permission written

theorem FreshRegion.wellFormed {before after : World} {region : Identity}
    (valid : before.WellFormed) (fresh : FreshRegion before region after) : after.WellFormed := by
  obtain ⟨rfl,rfl⟩ := fresh
  rcases valid with ⟨rootUnique,loanUnique,proofUnique,regionUnique,proofs,packs,owners,ownerUnique,
    roots,regions,bases,ranges,loans,references,overlaps,parents,locations,guards⟩
  refine ⟨rootUnique,loanUnique,proofUnique,?_,?_,?_,owners,ownerUnique,?_,?_,bases,ranges,?_,references,?_,parents,locations,guards⟩
  · exact List.nodup_cons.mpr ⟨fun member => Nat.lt_irrefl _ (regions _ member),regionUnique⟩
  · intro id available found
    obtain ⟨identity,bound,brand,active,recorded⟩ := proofs id available found
    exact ⟨identity,bound,brand,fun live => ⟨List.mem_cons_of_mem _ (active live).1,(active live).2⟩,recorded⟩
  · intro address value pack resident head
    obtain ⟨bound,live,length,distinct,facts⟩ := packs address value pack resident head
    exact ⟨bound,List.mem_cons_of_mem _ live,length,distinct,facts⟩
  · intro id root found
    obtain ⟨bound,active,layout,bytes,bounds⟩ := roots id root found
    exact ⟨bound,fun live => List.mem_cons_of_mem _ (active live),layout,bytes,bounds⟩
  · intro id member
    rcases List.mem_cons.mp member with rfl | old
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (regions _ old)
  · intro id loan found
    obtain ⟨identity,bound,active⟩ := loans id loan found
    exact ⟨identity,bound,fun live => ⟨List.mem_cons_of_mem _ (active live).1,(active live).2⟩⟩
  · intro a b left right first second leftLive rightLive overlap unique
    exact (overlaps a b left right first second leftLive rightLive overlap unique).imp
      (fun related => related.transport (before := before) rfl)
      (fun related => related.transport (before := before) rfl)

theorem FreshRegion.worldTyped {program : Kernel.Program} {before after : World} {region : Identity}
    (typed : Typing.WorldTyped program before) (fresh : FreshRegion before region after) :
    Typing.WorldTyped program after := by
  have valid := fresh.wellFormed typed.1
  obtain ⟨rfl,rfl⟩ := fresh
  refine ⟨valid,?_,typed.2.2.1,?_,typed.2.2.2.2⟩
  · intro address value resident
    apply (typed.2.1 address value resident).transport
    · intro id loan found _
      exact ⟨found,fun _ type => type.retained (fun _ selected => selected) (fun _ => rfl)⟩
    · rfl
    · exact fun _ origin => origin
  · intro id root found
    exact (typed.2.2.2.1 id root found).mono (Nat.le_succ _)

/-- Reservation activity governs use, not the representation of a retained
witness. This is an instance of the shared structural typing transport. -/
theorem Typing.ValueTyped.deactivateAvailability {program : Kernel.Program} {world : World} {value : Value}
    {id : Identity} {available : Availability} (selected : world.availability.get id = some available)
    (typed : Typing.ValueTyped program world value) :
    Typing.ValueTyped program { world with availability := world.availability.set id { available with active := false } } value := by
  apply typed.transport_observed (fun _ => True) (fun _ _ _ _ => trivial) trivial
  · intro resident key loan _ _ found active
    exact ⟨loan,found,active,rfl,rfl,fun _ located =>
      located.retained (fun _ found => found) (fun _ => rfl)⟩
  · intro key original found
    by_cases same : key = id
    · subst key
      have equal := Option.some.inj (selected.symm.trans found)
      subst original
      exact ⟨{ available with active := false },Table.get_set _ _ _,rfl,rfl,rfl⟩
    · exact ⟨original,by simpa only [Table.get_set_other _ _ _ _ same] using found,rfl,rfl,rfl⟩
  · exact fun _ origin => origin

theorem World.deactivateAvailability_wellFormed {world : World} {id : Identity} {available : Availability}
    (valid : world.WellFormed) (selected : world.availability.get id = some available) :
    ({ world with availability := world.availability.set id { available with active := false } } : World).WellFormed := by
  rcases valid with ⟨rootsUnique,loansUnique,proofsUnique,regionsUnique,proofs,packs,owners,unique,
    roots,regions,bases,ranges,loans,references,overlaps,parents,locations,guards⟩
  refine ⟨rootsUnique,loansUnique,proofsUnique.set _ _,regionsUnique,?_,packs,owners,unique,
    roots,regions,bases,ranges,loans,references,?_,parents,locations,guards⟩
  · intro key proof found
    by_cases same : key = id
    · subst key
      simp only [Table.get_set] at found
      cases found
      obtain ⟨identity,bound,brand,_,recorded⟩ := proofs id available selected
      exact ⟨identity,bound,brand,by simp,recorded⟩
    · exact proofs key proof (by simpa only [Table.get_set_other _ _ _ _ same] using found)
  · intro a b left right first second leftLive rightLive overlap unique
    exact (overlaps a b left right first second leftLive rightLive overlap unique).imp
      (fun ancestor => ancestor.transport (before := world) rfl)
      (fun ancestor => ancestor.transport (before := world) rfl)

theorem World.deactivateAvailability_worldTyped {program : Kernel.Program} {world : World} {id : Identity} {available : Availability}
    (typed : Typing.WorldTyped program world) (selected : world.availability.get id = some available) :
    Typing.WorldTyped program { world with availability := world.availability.set id { available with active := false } } :=
  ⟨World.deactivateAvailability_wellFormed typed.1 selected,
    fun address value resident => (typed.2.1 address value resident).deactivateAvailability selected,typed.2.2⟩


/-- Shell-liveness changes preserve every existing resident's head, even
inside the rewritten object. A parent may observe changed child liveness but
does not acquire a different constructor or reference identity. -/
theorem World.write_shell_stores_head {before after : World} {address observed : Address}
    {resident value : Value} {live : Bool}
    (stored : before.Stores address resident)
    (written : before.write address (some (.resident resident.owner resident.type resident.head live resident.fields resident.resources)) = some after)
    (found : before.Stores observed value) :
    ∃ changed, after.Stores observed changed ∧ changed.head = value.head := by
  by_cases included : address.Prefix observed
  · obtain ⟨suffix,equal⟩ := Address.prefix_extension included
    change before.read observed = some value at found
    rw [equal,World.read_append,stored] at found
    cases suffix with
    | nil =>
      have same : resident = value := Option.some.inj found
      have location : observed = address := by simpa using equal
      refine ⟨.resident resident.owner resident.type resident.head live resident.fields resident.resources,?_,same ▸ rfl⟩
      rw [location]
      simpa [World.Stores,Value.atPath] using World.write_read_inside written []
    | cons index rest =>
      refine ⟨value,?_,rfl⟩
      change after.read observed = some value
      rw [equal,World.write_read_inside written (index :: rest)]
      exact found
  · obtain ⟨changed,present,same⟩ := World.write_retains_shell written included (World.resident_iff_stores.mpr found)
    refine ⟨changed,World.resident_iff_stores.mp present,?_⟩
    simpa only [Value.shell,Value.withFields,Value.head] using congrArg Value.head same

theorem World.write_shell_references {before after : World} {address : Address} {resident : Value} {live : Bool}
    (stored : before.Stores address resident)
    (written : before.write address (some (.resident resident.owner resident.type resident.head live resident.fields resident.resources)) = some after)
    {id : Identity} (referenced : before.References id) : after.References id := by
  obtain ⟨observed,value,found,head⟩ := referenced
  obtain ⟨changed,present,same⟩ := World.write_shell_stores_head stored written (World.resident_iff_stores.mp found)
  exact ⟨observed,changed,World.resident_iff_stores.mpr present,same.trans head⟩


theorem Typing.ValueTyped.available_fields {program : Kernel.Program} {world : World} {value : Value} {id : Identity}
    (typed : Typing.ValueTyped program world value) (head : value.head = .available id) : value.fields = [] := by
  cases typed with
  | aggregate shape _ =>
    rcases shape with ⟨_,_,impossible⟩ | ⟨_,_,_,_,_,_,impossible,_,_⟩ | ⟨_,_,_,_,_,_,_,impossible,_⟩
    all_goals simp_all only [Value.head]
    all_goals cases head
  | callable => cases head
  | bindings => cases head
  | unit => rfl
  | scalar => rfl
  | reference => rfl
  | pointer => rfl
  | operation => rfl
  | label => rfl
  | continuation => rfl
  | available => rfl

end Glorious.Language
