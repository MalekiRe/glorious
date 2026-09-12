import GloriousLanguage.CleanupPreservation

/-! General storage typing preservation for ordinary local machine execution.
Scope entry, invocation binding and receiver/shell consumption use the same
storage relations as cleanup, without a typed post-state admission premise. -/
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
    Typing.ValueTyped program world (.resident value.owner value.type value.head live value.fields) := by
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
    (written : before.write address (some (.resident resident.owner resident.type resident.head live resident.fields)) = some after)
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
      (some (.resident resident.owner resident.type resident.head live resident.fields)) = some after) :
    Typing.WorldTyped program after := by
  have checked := (typed.2.1 address resident (World.resident_iff_stores.mpr stored)).shellLive live
  have roots := World.rewrite_typed_roots typed.roots stored written checked rfl
  have rest := World.write_rest written
  have loansEq := congrArg World.loans rest
  have proofEq := congrArg World.availability rest
  refine ⟨World.write_wellFormed_of_origin typed.1 permission written
    (fun _ _ found => World.write_shell_origin stored written found),?_,?_,?_⟩
  · intro observed value resident
    apply (World.stores_typed roots (World.resident_iff_stores.mp resident)).transport
      ?_ proofEq (fun _ origin => origin.write written)
    intro id loan found live
    exact ⟨by simpa only [loansEq] using found,fun _ type =>
      (World.write_address_types written
        (permission.owned_no_loan_descendant (World.loanParents typed.1) found live)).mp type⟩
  · intro id root value found contents
    by_cases live : root.live = true
    · exact (roots id root value found live contents).2
    · exact typed.2.2.1 id root value (World.write_dead_root written found live) contents
  · apply World.root_regions_transport typed.2.2.2 (World.write_locations written)
    exact Nat.le_of_eq (congrArg World.nextRegion rest).symm

theorem Deconstructs.worldTyped {program : Kernel.Program} {context : Context} {before after : World}
    {authority : Authority} {address : Address} (typed : Typing.WorldTyped program before)
    (consumed : Deconstructs program.declarations context before authority address after) :
    Typing.WorldTyped program after := by
  cases consumed with
  | shell stored _ permission _ written => exact World.write_shell_worldTyped typed stored permission written

theorem FreshRegion.wellFormed {before after : World} {region : Identity}
    (valid : before.WellFormed) (fresh : FreshRegion before region after) : after.WellFormed := by
  obtain ⟨rfl,rfl⟩ := fresh
  rcases valid with ⟨rootUnique,loanUnique,proofUnique,regionUnique,proofs,packs,owners,ownerUnique,
    roots,regions,bases,ranges,loans,references,overlaps,parents,locations⟩
  refine ⟨rootUnique,loanUnique,proofUnique,?_,?_,?_,owners,ownerUnique,?_,?_,bases,ranges,?_,references,?_,parents,locations⟩
  · exact List.nodup_cons.mpr ⟨fun member => Nat.lt_irrefl _ (regions _ member),regionUnique⟩
  · intro id available found
    obtain ⟨identity,bound,brand,active⟩ := proofs id available found
    exact ⟨identity,bound,brand,fun live => ⟨List.mem_cons_of_mem _ (active live).1,(active live).2⟩⟩
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
  refine ⟨valid,?_,typed.2.2.1,?_⟩
  · intro address value resident
    apply (typed.2.1 address value resident).transport
    · intro id loan found _
      exact ⟨found,fun _ type => type.retained (fun _ selected => selected) (fun _ => rfl)⟩
    · rfl
    · exact fun _ origin => origin
  · intro id root found
    exact (typed.2.2.2 id root found).mono (Nat.le_succ _)

namespace Execution

theorem ConsumesReceiver.worldTyped {program : Kernel.Program} {before after : World}
    {address : Address} {authority : Authority} {access : Access}
    (typed : Typing.WorldTyped program before) (consumed : ConsumesReceiver before address authority access after) :
    Typing.WorldTyped program after := by
  cases consumed with
  | lent => exact typed
  | owned stored _ _ permission written => exact World.write_shell_worldTyped typed stored permission written

theorem Protect.worldTyped {program : Kernel.Program} {context : Context} {before after : World}
    {source destination : Address} {authority : Authority}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (kept : Protect program context before source authority destination after) :
    Typing.WorldTyped program after := by
  obtain ⟨_,_,_,allocated,moved⟩ := kept
  exact moved.worldTyped valid inventory (allocated.worldTyped typed)

theorem Protects.worldTyped {program : Kernel.Program} {context : Context} {before after : World}
    {sources : List ResolvedPlace} {destinations : List Address}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (kept : Protects program context before sources destinations after) :
    Typing.WorldTyped program after := by
  induction kept with
  | nil => exact typed
  | cons first _ ih => exact ih (first.worldTyped valid inventory typed)

theorem EnterWorld.worldTyped {program : Kernel.Program} {before : State} {after : World}
    {caller context : Context} {function : Kernel.Function} {inputs : List Kernel.InvocationInput}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (entered : EnterWorld program before caller function inputs context after) :
    Typing.WorldTyped program after := by
  obtain ⟨_,_,_,_,fresh,bound,_,_⟩ := entered
  exact bound.worldTyped valid inventory (fresh.worldTyped typed)

/-- Every ordinary local transition preserves the world typing invariant.
This includes owned receiver consumption, fresh scope and invocation entry,
pattern binding/deconstruction and destructor handle creation. It is a storage
preservation theorem, not yet a task/frame preservation or progress theorem. -/
theorem LocalStep.worldTyped {program : Kernel.Program} {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world) (step : LocalStep program before event after) :
    Typing.WorldTyped program after.world := by
  cases step <;> try exact typed
  case evaluate allocated => exact allocated.worldTyped typed
  case bind allocated => exact allocated.worldTyped typed
  case result kept => exact kept.worldTyped valid inventory typed
  case transfer moved => exact moved.worldTyped valid inventory typed
  case invoke allocated => exact allocated.worldTyped typed
  case call consumed => exact consumed.worldTyped typed
  case enter entered => exact entered.worldTyped valid inventory typed
  case enterTail => apply EnterWorld.worldTyped valid inventory typed; assumption
  case bindReturn moved => exact moved.worldTyped valid inventory typed
  case activationReturn => apply Protect.worldTyped valid inventory typed; assumption
  case scope => apply FreshRegion.worldTyped typed; assumption
  case scopeReturn => apply Protect.worldTyped valid inventory typed; assumption
  case patternBind bound => exact bound.worldTyped valid inventory typed
  case patternShell consumed => exact consumed.worldTyped typed
  case destroyHook => apply Borrows.worldTyped valid inventory (program := program); apply Temporary.worldTyped typed <;> assumption; assumption
  case destroyReference => apply World.clear_worldTyped typed <;> assumption
  case shellDone => apply World.clear_worldTyped typed <;> assumption
  case retire retired => exact retired.worldTyped typed
  case regionEnd ended => exact ended.worldTyped typed
  case loanEnd ended => exact ended.worldTyped typed
  case releaseRoot ended => exact ended.worldTyped typed
  case releaseChild ended => exact ended.worldTyped typed

end Execution

end Glorious.Language
