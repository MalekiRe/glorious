import GloriousLanguage.PrivateEffectPreservation

/-! Sealed reservations and test carriers preserve the same private caller
slot. Freshness comes from actual allocation; reservation exclusion comes
from the authoritative resolved operands and current availability ledger. -/
namespace Glorious.Language


namespace Execution
open _root_.Glorious.Language.Kernel

theorem CopiesObservations.private_slot {program : Kernel.Program} {context : Context}
    {before after : World} {observations : List (Local × Address × Authority)} {bindings : List (Local × Address)}
    {id : Identity} {root : Root} (copied : CopiesObservations program context before observations bindings after)
    (bound : id < before.nextRoot) (slot : before.PrivateSlot id root) : after.PrivateSlot id root := by
  induction copied with
  | nil => exact slot
  | copy _ _ allocated copied _ ih =>
    exact ih (Nat.lt_of_lt_of_le bound (allocated.suspensionExtension.trans copied.suspensionExtension).counter)
      (copied.private_slot (allocated.choose_spec.private_slot bound slot) (allocated.choose_spec.fresh_avoids bound))
  | borrow _ _ allocated borrowed _ ih =>
    exact ih (Nat.lt_of_lt_of_le bound (allocated.suspensionExtension.trans borrowed.suspensionExtension).counter)
      (borrowed.private_slot (allocated.choose_spec.private_slot bound slot) (allocated.choose_spec.fresh_avoids bound))

theorem PacksBindings.private_slot {program : Kernel.Program} {context : Context} {before after : World}
    {pattern resultOrigin positive bindings pack} {id : Identity} {root : Root}
    (packed : PacksBindings program context before pattern resultOrigin positive bindings pack after)
    (bound : id < before.nextRoot) (slot : before.PrivateSlot id root) : after.PrivateSlot id root := by
  obtain ⟨allocated,created,type,_,temporary,_,constructed,rfl⟩ := packed
  have kept := constructed.private_slot (temporary.choose_spec.private_slot bound slot)
    (temporary.choose_spec.fresh_avoids bound)
  exact ⟨kept.found,kept.vacant,kept.safe,kept.internalHome⟩

theorem UnitFields.private_slot {program : Kernel.Program} {context : Context} {before after : World}
    {types : List Term} {index : Option Nat} {pack : Address} {fields : List Address} {id : Identity} {root : Root}
    (assembled : UnitFields program context before types index pack fields after)
    (bound : id < before.nextRoot) (slot : before.PrivateSlot id root) : after.PrivateSlot id root := by
  induction assembled with
  | done => exact slot
  | selected _ _ _ ih => exact ih bound slot
  | unitBefore allocated created _ ih | unitAfter allocated created _ ih =>
    exact ih (Nat.lt_of_lt_of_le bound (allocated.suspensionExtension.trans created.2.suspensionExtension).counter)
      (created.2.private_slot (allocated.choose_spec.private_slot bound slot) (allocated.choose_spec.fresh_avoids bound))

theorem TestResult.private_slot {program : Kernel.Program} {context : Context} {before after : World}
    {destination type pattern positive observations} {id : Identity} {root : Root}
    (tested : TestResult program context before destination type pattern positive observations after)
    (bound : id < before.nextRoot) (slot : before.PrivateSlot id root) (outside : destination.root ≠ id) :
    after.PrivateSlot id root := by
  cases tested with
  | result _ _ copied packed fields constructed =>
    have middle := copied.private_slot bound slot
    have copiedBound := Nat.lt_of_lt_of_le bound copied.suspensionExtension.counter
    have packedBound := Nat.lt_of_lt_of_le copiedBound packed.suspensionExtension.counter
    exact constructed.private_slot
      (fields.choose_spec.2.2.2.2.private_slot packedBound (packed.private_slot copiedBound middle)) outside


theorem ControlStep.private_slot {program : Kernel.Program} {before after : State} {event : Option Event}
    {id owner : Identity} {returning : Bool} {root : Root}
    (step : ControlStep program before event after) (well : before.world.WellFormed)
    (slot : before.world.PrivateSlot id root) (taskOutside : id ∉ before.task.rootSupport)
    (taskOwner : before.task.PrivateActivation owner returning) : after.world.PrivateSlot id root := by
  cases step
  all_goals try exact slot
  all_goals simp_all only [Task.PrivateActivation,Task.rootSupport,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,not_or]
  case available moved | bindings moved => exact moved.private_slot slot (Ne.symm taskOutside.2)
  case destroyAvailable stored _ _ _ _ written =>
    exact (slot.write written (slot.stored_outside stored)).availability_set (by simp)
  case destroySpentAvailable stored _ _ _ _ written => exact slot.write written (slot.stored_outside stored)
  case positiveTest _ _ _ _ _ _ _ allocated tested | negativeTest _ _ _ _ _ _ _ _ allocated tested =>
    exact tested.private_slot (Nat.lt_of_lt_of_le (slot.bound well) (allocated.suspensionExtension (by simp)).counter)
      (allocated.private_slot (slot.bound well) slot) (allocated.fresh_avoids (slot.bound well))
  case reserve context lexical bound localSlot brand places next reserved types allocatedWorld destination world layout task boundDef localDef resolved _ _ _ _ _ allocated created =>
    have first := created.private_slot (allocated.private_slot (slot.bound well) slot)
      (allocated.fresh_avoids (slot.bound well))
    have operandsOutside := resolved.avoids_root (Context.bindings_avoid_root taskOutside) slot.safe
    have kept := first.availability_set (key := before.world.nextProof)
      (available := ⟨before.world.nextProof,.runtimeBrand (.proof before.world.nextProof),context.region,reserved,types,true⟩)
      (fun _ place member same => operandsOutside (List.mem_map.mpr ⟨place,member,same⟩))
    exact ⟨kept.found,kept.vacant,kept.safe,kept.internalHome⟩

theorem ReservationInputs.avoids_root {world : World} {available : Availability} {access : Access}
    {formals : List Local} {inputs : List InvocationInput} {id : Identity} {root : Root}
    (prepared : ReservationInputs world available access formals inputs) (slot : world.PrivateSlot id root) :
    id ∉ inputs.flatMap InvocationInput.rootSupport := by
  intro member
  obtain ⟨input,present,member⟩ := List.mem_flatMap.mp member
  have same : id = input.storage.root := by simpa only [InvocationInput.rootSupport,
    List.mem_cons,List.not_mem_nil,or_false] using member
  obtain ⟨value,stored,_⟩ := (prepared.2.2.2 input present).2
  exact slot.stored_outside stored same.symm

theorem DisposesReservations.avoids_root {context : Context} {places : List ResolvedPlace} {next : Task} {id : Identity}
    (contextOutside : id ∉ context.rootSupport)
    (outside : ∀ place ∈ places, place.address.root ≠ id) (continued : id ∉ next.rootSupport) :
    id ∉ (DisposesReservations context places next).rootSupport := by
  induction places with
  | nil => exact continued
  | cons place rest ih =>
    simp only [DisposesReservations,List.foldr_cons,Task.rootSupport,List.mem_append,List.mem_cons,not_or]
    exact ⟨contextOutside,Ne.symm (outside place List.mem_cons_self),
      ih (fun place member => outside place (List.mem_cons_of_mem _ member))⟩

theorem DisposesReservations.private_activation {context : Context} {places : List ResolvedPlace}
    {next : Task} {owner : Identity} {returning : Bool}
    (contextOutside : context.activation ≠ owner) (continued : next.PrivateActivation owner returning) :
    (DisposesReservations context places next).PrivateActivation owner returning := by
  induction places with
  | nil => exact continued
  | cons _ _ ih => exact ⟨contextOutside,ih⟩

theorem ControlStep.private_control {program : Kernel.Program} {before after : State} {event : Option Event}
    {id owner : Identity} {root : Root} {inner : List Frame}
    (step : ControlStep program before event after) (well : before.world.WellFormed)
    (slot : before.world.PrivateSlot id root) (control : PrivateControl id owner inner before.task)
    (noLeave : ∀ brand, event ≠ some (.leave brand)) :
    after.frames = before.frames ∧ PrivateControl id owner inner after.task := by
  obtain ⟨taskRoots,frameRoots,taskOwner,frameOwners⟩ := control
  cases step
  all_goals simp_all only [Task.rootSupport,Task.PrivateActivation,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,not_or]
  all_goals try (solve | exact ⟨True.intro,taskRoots.1,frameRoots,taskOwner,frameOwners⟩)
  case labelCall => exact False.elim (noLeave _ rfl)
  case reserve _ _ _ _ _ _ _ _ allocated _ |
      positiveTest _ _ _ _ _ _ _ allocated _ | negativeTest _ _ _ _ _ _ _ _ allocated _ =>
    have outside := allocated.fresh_avoids (slot.bound well)
    refine ⟨True.intro,?_,frameRoots,taskOwner,frameOwners⟩
    exact Context.bind_avoids_root taskRoots outside
  case closeAvailable resolved _ _ =>
    have outside := Context.resolves_avoids_root taskRoots slot.safe resolved
    refine ⟨True.intro,?_⟩
    simp_all [PrivateControl,Task.rootSupport,Task.PrivateActivation,ne_comm]
  case primitiveCloseAvailable =>
    refine ⟨True.intro,?_⟩
    simp_all [PrivateControl,Task.rootSupport,Task.PrivateActivation]
  case destroyAvailable _ _ found closable _ _ =>
    have reservedOutside := slot.safe.2.1 _ _ found
    refine ⟨True.intro,?_,frameRoots,?_,frameOwners⟩
    · apply DisposesReservations.avoids_root taskRoots.1 _ taskRoots.2.2
      intro place member
      exact reservedOutside closable.1 place (List.mem_reverse.mp member)
    · exact DisposesReservations.private_activation taskOwner.1 taskOwner.2
  case destroySpentAvailable => exact ⟨True.intro,taskRoots.2.2,frameRoots,taskOwner.2,frameOwners⟩
  case contextualCall _ _ resolved _ _ _ _ _ _ _ witness _ _ captures inputs resources =>
    have receiverOutside := Context.resolves_avoids_root taskRoots slot.safe resolved
    have witnessOutside := Context.resolves_avoids_root taskRoots slot.safe witness
    have capturesOutside := captures.avoids_root slot
    have inputsOutside := inputs.avoids_root taskRoots slot.safe
    have resourcesOutside := resources.avoids_root (Context.bindings_avoid_root taskRoots) slot.safe
    refine ⟨True.intro,?_⟩
    simp_all [PrivateControl,Task.rootSupport,EntrySource.rootSupport,Task.PrivateActivation,
      List.mem_flatMap,InvocationInput.rootSupport,ne_comm]

end Execution
end Glorious.Language
