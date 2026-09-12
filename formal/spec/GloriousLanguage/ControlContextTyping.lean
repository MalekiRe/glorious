import GloriousLanguage.EffectContextTyping
import GloriousLanguage.TestPreservation

/-! The actual reservation and pattern-test transitions preserve retained
lexical storage declarations. Availability consumption destroys only its
fieldless witness; contextual receiver consumption retains the owned fields.
Test publication uses the existing future-owner invariant of its constructor. -/
namespace Glorious.Language

theorem Typing.BindingStorageTyped.withProofs {program : Program} {world : World} {address : Address} {type : Term}
    (binding : Typing.BindingStorageTyped program world address type) (proofs : Table Availability) (next : Identity) :
    Typing.BindingStorageTyped program (world.withProofs proofs next) address type :=
  binding.roots_loans (before := world) (after := world.withProofs proofs next) rfl rfl

namespace Execution

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
