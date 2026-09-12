import GloriousLanguage.EffectContextTyping
import GloriousLanguage.TestPreservation

/-! The actual reservation and pattern-test transitions preserve retained
lexical storage declarations. Availability consumption destroys only its
fieldless witness; contextual receiver consumption retains the owned fields.
Test publication uses the existing future-owner invariant of its constructor. -/
namespace Glorious.Language

/-- Shell-liveness changes preserve every existing resident's head, even
inside the rewritten object. A parent may observe changed child liveness but
does not acquire a different constructor or reference identity. -/
theorem World.write_shell_stores_head {before after : World} {address observed : Address}
    {resident value : Value} {live : Bool}
    (stored : before.Stores address resident)
    (written : before.write address (some (.resident resident.owner resident.type resident.head live resident.fields)) = some after)
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
      refine ⟨.resident resident.owner resident.type resident.head live resident.fields,?_,same ▸ rfl⟩
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
    (written : before.write address (some (.resident resident.owner resident.type resident.head live resident.fields)) = some after)
    {id : Identity} (referenced : before.References id) : after.References id := by
  obtain ⟨observed,value,found,head⟩ := referenced
  obtain ⟨changed,present,same⟩ := World.write_shell_stores_head stored written (World.resident_iff_stores.mp found)
  exact ⟨observed,changed,World.resident_iff_stores.mpr present,same.trans head⟩

theorem World.write_shell_bindingStorageTyped {program : Program} {before after : World}
    {address : Address} {authority : Authority} {resident : Value} {live : Bool}
    (valid : before.WellFormed) (stored : before.Stores address resident)
    (permission : Permitted before authority .owned address)
    (written : before.write address (some (.resident resident.owner resident.type resident.head live resident.fields)) = some after)
    {observed : Address} {type : Term} (binding : Typing.BindingStorageTyped program before observed type) :
    Typing.BindingStorageTyped program after observed type := by
  cases binding with
  | root whole declared =>
    exact .root whole (by rw [World.root_types_of_locations (World.write_locations written)]; exact declared)
  | lent found active referent referenced located =>
    refine .lent (by simpa only [World.write_loans written] using found) active referent
      (World.write_shell_references stored written referenced) ?_
    apply (World.write_address_types written ?_).mp located
    rw [← referent]
    exact permission.owned_no_loan_descendant (World.loanParents valid) found active

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

theorem Typing.BindingStorageTyped.withProofs {program : Program} {world : World} {address : Address} {type : Term}
    (binding : Typing.BindingStorageTyped program world address type) (proofs : Table Availability) (next : Identity) :
    Typing.BindingStorageTyped program (world.withProofs proofs next) address type :=
  binding.roots_loans (before := world) (after := world.withProofs proofs next) rfl rfl

namespace Execution

theorem ConsumesReceiver.stores_head {before after : World} {address : Address} {authority : Authority} {access : Access}
    (consumed : ConsumesReceiver before address authority access after)
    {observed : Address} {value : Value} (stored : before.Stores observed value) :
    ∃ changed, after.Stores observed changed ∧ changed.head = value.head := by
  cases consumed with
  | lent => exact ⟨value,stored,rfl⟩
  | owned found _ _ _ written => exact World.write_shell_stores_head found written stored

theorem ConsumesReceiver.bindingStorageTyped {program : Program} {before after : World}
    {address : Address} {authority : Authority} {access : Access} (valid : before.WellFormed)
    (consumed : ConsumesReceiver before address authority access after)
    {observed : Address} {type : Term} (binding : Typing.BindingStorageTyped program before observed type) :
    Typing.BindingStorageTyped program after observed type := by
  cases consumed with
  | lent => exact binding
  | owned stored _ _ permission written => exact World.write_shell_bindingStorageTyped valid stored permission written binding

theorem ConsumesAvailability.bindingStorageTyped {program : Kernel.Program} {before after : World}
    {address : Address} {id : Identity} {authority : Authority} {access : Access} {value : Value}
    (typed : Typing.WorldTyped program before) (stored : before.Stores address value) (head : value.head = .available id)
    (permission : access = .owned → Permitted before authority .owned address)
    (consumed : ConsumesAvailability before address id access after)
    {observed : Address} {type : Term} (binding : Typing.BindingStorageTyped program.declarations before observed type) :
    Typing.BindingStorageTyped program.declarations after observed type := by
  cases consumed with
  | lent => exact binding
  | owned _ written =>
    have valueTyped := World.stores_typed typed.roots stored
    have retained := World.clear_nonreference_leaf_bindingStorageTyped typed.1 stored
      (valueTyped.available_fields head) (by intro loan; rw [head]; exact ValueHead.noConfusion) (permission rfl) written binding
    exact retained.withProofs _ _

theorem CopiesObservations.bindingStorageTyped {program : Kernel.Program} {context : Context}
    {before after : World} {observations bindings}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (copied : CopiesObservations program context before observations bindings after)
    {address : Address} {type : Term} (binding : Typing.BindingStorageTyped program.declarations before address type) :
    Typing.BindingStorageTyped program.declarations after address type := by
  induction copied with
  | nil => exact binding
  | copy _ _ temporary copied _ ih =>
    obtain ⟨_,allocated⟩ := temporary
    have middle := allocated.worldTyped typed
    exact ih (copied.worldTyped valid inventory middle)
      (copied.bindingStorageTyped middle.1 (allocated.bindingStorageTyped typed.1 binding))
  | borrow _ _ temporary borrowed _ ih =>
    obtain ⟨_,allocated⟩ := temporary
    have middle := allocated.worldTyped typed
    exact ih (borrowed.worldTyped valid inventory middle)
      (borrowed.bindingStorageTyped middle.1 (allocated.bindingStorageTyped typed.1 binding))

theorem PacksBindings.bindingStorageTyped {program : Kernel.Program} {context : Context} {before after : World}
    {pattern resultOrigin positive bindings pack originBound}
    (typed : Typing.WorldTypedWithOrigins program before originBound)
    (packed : PacksBindings program context before pattern resultOrigin positive bindings pack after)
    {address : Address} {type : Term} (binding : Typing.BindingStorageTyped program.declarations before address type) :
    Typing.BindingStorageTyped program.declarations after address type := by
  obtain ⟨_,_,_,_,⟨_,allocated⟩,_,constructed,rfl⟩ := packed
  have retained := constructed.bindingStorageTyped (allocated.wellFormedWithOrigins typed.1)
    (allocated.bindingStorageTyped typed.1 binding)
  exact retained.withProofs _ _

theorem UnitFields.bindingStorageTyped {program : Kernel.Program} {context : Context} {before after : World}
    {types selected pack fields originBound}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTypedWithOrigins program before originBound)
    (assembled : UnitFields program context before types selected pack fields after)
    {address : Address} {type : Term} (binding : Typing.BindingStorageTyped program.declarations before address type) :
    Typing.BindingStorageTyped program.declarations after address type := by
  induction assembled with
  | done => exact binding
  | selected _ _ _ ih => exact ih typed binding
  | unitBefore temporary unit _ ih | unitAfter temporary unit _ ih =>
    obtain ⟨_,allocated⟩ := temporary
    have middle := allocated.worldTypedWithOrigins typed
    exact ih (unit.worldTypedWithOrigins valid inventory middle)
      (unit.2.bindingStorageTyped middle.1 (allocated.bindingStorageTyped typed.1 binding))

theorem TestResult.bindingStorageTyped {program : Kernel.Program} {context : Context} {before after : World}
    {destination type pattern positive observations}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (tested : TestResult program context before destination type pattern positive observations after)
    {address : Address} {expected : Term} (binding : Typing.BindingStorageTyped program.declarations before address expected) :
    Typing.BindingStorageTyped program.declarations after address expected := by
  cases tested with
  | @result carrier arguments copied bindings packed pack fields assembled after _ _ observed made carrierFields constructed =>
    have copiedTyped := observed.worldTyped valid inventory typed
    have bindingTypes := observed.binding_types valid inventory typed
    obtain ⟨_,_,_,_,_,assembledFields⟩ := carrierFields
    have originBound : copied.nextOwner ≤ assembled.nextOwner+1 := by
      have one := made.nextOwner
      have many := assembledFields.nextOwner
      rw [one] at many
      exact Nat.le_trans (Nat.le_succ _) (Nat.le_trans many (Nat.le_succ _))
    have packedTyped := made.worldTypedWithOrigins valid inventory (copiedTyped.mono originBound)
      bindingTypes (Nat.lt_succ_self _)
    have assembledTyped := assembledFields.worldTypedWithOrigins valid inventory packedTyped
    exact constructed.bindingStorageTyped assembledTyped.1
      (assembledFields.bindingStorageTyped valid inventory packedTyped
        (made.bindingStorageTyped (copiedTyped.mono originBound)
          (observed.bindingStorageTyped valid inventory typed binding)))

/-- Reservation, test publication and contextual entry preserve every saved
original context. No read access is inferred from a retained declaration. -/
theorem ControlStep.contextBindingsTyped {program : Kernel.Program} {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program before.world) (step : ControlStep program before event after)
    {source : Typing.Context} {runtime : Context}
    (typed : Typing.ContextBindingsTyped program before.world source runtime) :
    Typing.ContextBindingsTyped program after.world source runtime := by
  cases step <;> try exact typed
  case leave kept _ _ => exact kept.contextBindingsTyped worldTyped typed
  case reserve _ _ _ _ _ _ allocated created =>
    have retained := typed.world (fun _ _ binding => created.bindingStorageTyped
      (allocated.wellFormed worldTyped.1) (allocated.bindingStorageTyped worldTyped.1 binding))
    exact retained.world (fun _ _ binding => binding.withProofs _ _)
  case available moved => exact typed.world (fun _ _ binding => moved.bindingStorageTyped worldTyped.1 binding)
  case destroyAvailable stored head _ _ permission written =>
    have valueTyped := World.stores_typed worldTyped.roots stored
    have retained := typed.world (fun _ _ binding => World.clear_nonreference_leaf_bindingStorageTyped worldTyped.1 stored
      (valueTyped.available_fields head) (by intro id; rw [head]; exact ValueHead.noConfusion) permission written binding)
    exact retained.world (fun _ _ binding => binding.withProofs _ _)
  case destroySpentAvailable stored head _ _ permission written =>
    have valueTyped := World.stores_typed worldTyped.roots stored
    exact typed.world (fun _ _ binding => World.clear_nonreference_leaf_bindingStorageTyped worldTyped.1 stored
      (valueTyped.available_fields head) (by intro id; rw [head]; exact ValueHead.noConfusion) permission written binding)
  case contextualCall _ _ _ _ _ _ _ _ _ _ witnessStored _ witnessHead witnessPermission _ _ _ _ _ _ _ consumed used =>
    have consumedWorld := consumed.worldTyped worldTyped
    have consumedContext := typed.world (fun _ _ binding => consumed.bindingStorageTyped worldTyped.1 binding)
    obtain ⟨witness,present,head⟩ := consumed.stores_head witnessStored
    apply consumedContext.world
    intro address type binding
    exact used.bindingStorageTyped consumedWorld present (head.trans witnessHead)
      (fun access => by simpa only [access] using witnessPermission.transport consumed.locations consumed.loans) binding
  case positiveTest allocated tested | negativeTest allocated tested =>
    exact typed.world (fun _ _ binding => tested.bindingStorageTyped valid inventory (allocated.worldTyped worldTyped)
      (allocated.bindingStorageTyped worldTyped.1 binding))
  case bindings moved => exact typed.world (fun _ _ binding => moved.bindingStorageTyped worldTyped.1 binding)

end Execution
end Glorious.Language
