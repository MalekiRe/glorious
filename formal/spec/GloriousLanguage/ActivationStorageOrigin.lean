import GloriousLanguage.ActivationOrigin
import GloriousLanguage.ControlStorageOrigin

/-! Ordinary storage producers preserve activation provenance. New local
homes use their actual invocation/context owner; value writes, moves, loans
and retirement cannot replace that owner with an unrelated activation. -/
namespace Glorious.Language

theorem World.ActivationsBelow.of_homes {before after : World} {limit : Identity}
    (bounded : before.ActivationsBelow limit)
    (homes : ∀ id, (after.roots.get id).map Root.home = (before.roots.get id).map Root.home) :
    after.ActivationsBelow limit := by
  intro id root found
  have same := homes id
  rw [found,Option.map_some] at same
  obtain ⟨original,present,equal⟩ := Option.map_eq_some_iff.mp same.symm
  exact equal ▸ bounded id original present

theorem World.ActivationsBelow.of_locations {before after : World} {limit : Identity}
    (bounded : before.ActivationsBelow limit)
    (locations : ∀ id, (after.roots.get id).map Root.location = (before.roots.get id).map Root.location) :
    after.ActivationsBelow limit := by
  apply bounded.of_homes
  intro id
  have same := congrArg (Option.map Root.home) (locations id)
  simpa only [Option.map_map,Function.comp_def,Root.location] using same

theorem World.write_activationsBelow {before after : World} {address : Address} {value : Option Value}
    {limit : Identity} (written : before.write address value = some after)
    (bounded : before.ActivationsBelow limit) : after.ActivationsBelow limit :=
  bounded.of_locations (World.write_locations written)

theorem Allocates.activationsBelow {program : Program} {before after : World}
    {home region type layout mutable address} {limit : Identity}
    (allocated : Allocates program before home region type layout mutable address after)
    (bounded : before.ActivationsBelow limit) (owner : home.ActivationsBelow limit) :
    after.ActivationsBelow limit := by
  cases allocated
  intro id root found
  by_cases same : id = before.nextRoot
  · subst id
    simp only [Table.get_set,Option.some.injEq] at found
    subst root
    exact owner
  · exact bounded id root (by simpa only [Table.get_set_other _ _ _ _ same] using found)

theorem Transfers.activationsBelow {program : RuntimeProgram} {before after : World}
    {authority source destination} {limit : Identity}
    (transferred : Transfers program before authority source destination after)
    (bounded : before.ActivationsBelow limit) : after.ActivationsBelow limit :=
  bounded.of_locations transferred.locations

theorem Copies.activationsBelow {program : RuntimeProgram} {before after : World}
    {authority source destination} {limit : Identity}
    (copied : Copies program before authority source destination after)
    (bounded : before.ActivationsBelow limit) : after.ActivationsBelow limit :=
  bounded.of_locations copied.locations

theorem Acquires.activationsBelow {program : RuntimeProgram} {before after : World}
    {authority force source destination} {limit : Identity}
    (acquired : Acquires program before authority force source destination after)
    (bounded : before.ActivationsBelow limit) : after.ActivationsBelow limit := by
  cases acquired with
  | explicitMove moved => exact moved.activationsBelow bounded
  | copy copied => exact copied.activationsBelow bounded
  | move _ _ _ moved => exact moved.activationsBelow bounded

theorem FormsLoan.activationsBelow {program : RuntimeProgram} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent destination} {limit : Identity}
    (borrowed : FormsLoan program purpose before authority mode region referent destination after)
    (bounded : before.ActivationsBelow limit) : after.ActivationsBelow limit :=
  bounded.of_locations borrowed.locations

theorem EndsLoan.activationsBelow {program : RuntimeProgram} {before after : World} {id limit : Identity}
    (ended : EndsLoan program before id after) (bounded : before.ActivationsBelow limit) :
    after.ActivationsBelow limit := by cases ended; exact bounded

theorem Retires.activationsBelow {before after : World} {id limit : Identity}
    (retired : Retires before id after) (bounded : before.ActivationsBelow limit) :
    after.ActivationsBelow limit := by
  cases retired with
  | vacant selected _ _ _ =>
    apply bounded.of_homes
    intro key
    by_cases same : key = id
    · subst key
      simp only [Table.get_set,selected,Option.map_some]
    · simp only [Table.get_set_other _ _ _ _ same]

theorem Clears.activationsBelow {before after : World} {addresses : List Address} {limit : Identity}
    (cleared : Clears before addresses after) (bounded : before.ActivationsBelow limit) :
    after.ActivationsBelow limit := bounded.of_locations cleared.locations

theorem NewValue.activationsBelow {program : RuntimeProgram} {before after : World}
    {destination type head sources} {limit : Identity}
    (constructed : NewValue program before destination type head sources after)
    (bounded : before.ActivationsBelow limit) : after.ActivationsBelow limit :=
  bounded.of_locations constructed.locations

theorem FreshRegion.activationsBelow {before after : World} {region limit : Identity}
    (fresh : FreshRegion before region after) (bounded : before.ActivationsBelow limit) :
    after.ActivationsBelow limit := by rcases fresh with ⟨_,rfl⟩; exact bounded

theorem ReleasesStorageClaims.activationsBelow {before after : World} {place : ResolvedPlace} {limit : Identity}
    (released : ReleasesStorageClaims before place after) (bounded : before.ActivationsBelow limit) :
    after.ActivationsBelow limit := by
  cases released
  exact bounded

theorem RelinquishesCustody.activationsBelow {before after : World} {custody : ClaimCustody} {limit : Identity}
    (relinquished : RelinquishesCustody before custody after) (bounded : before.ActivationsBelow limit) :
    after.ActivationsBelow limit := by
  cases relinquished
  exact bounded

theorem ReturnsStorageLoan.activationsBelow {before after : World} {identity limit : Identity}
    (returned : ReturnsStorageLoan before identity after) (bounded : before.ActivationsBelow limit) :
    after.ActivationsBelow limit := by
  cases returned
  exact bounded


namespace Kernel

theorem LendsResident.activationsBelow {program : RuntimeProgram} {before after : World}
    {activation scope region address authority access lease permission} {limit : Identity}
    (lent : LendsResident program activation scope region before address authority access lease permission after)
    (bounded : before.ActivationsBelow limit) (owner : activation < limit) :
    after.ActivationsBelow limit := by
  cases lent with
  | owned => exact bounded
  | lent _ _ _ allocated borrowed =>
    exact borrowed.activationsBelow (allocated.activationsBelow bounded (by simpa using owner))

theorem BindsInputAt.activationsBelow {program : RuntimeProgram} {recipient : ClaimCustody} {before after : World}
    {activation scope region input binding} {limit : Identity}
    (bound : BindsInputAt program recipient activation scope region before input binding after)
    (bounded : before.ActivationsBelow limit) (owner : activation < limit) : after.ActivationsBelow limit := by
  cases bound with
  | lent _ _ _ _ _ _ _ borrowed => exact borrowed.activationsBelow bounded owner
  | owned _ _ _ _ _ allocated moved =>
    exact moved.activationsBelow (allocated.activationsBelow bounded (by simpa using owner))
  | storage _ _ _ claimed | guardedAllocation _ _ _ _ _ claimed => cases claimed; exact bounded
  | allocation _ _ _ _ moved | loan _ _ _ _ moved => cases moved <;> exact bounded

theorem BindsInputsAttemptFor.activationsBelow {program : RuntimeProgram} {recipient : ClaimCustody}
    {footprint : List Address} {before after : World} {activation scope region inputs environment}
    {outcome : PreparationOutcome} {limit : Identity}
    (bound : BindsInputsAttemptFor program recipient activation scope region footprint before inputs environment after outcome)
    (bounded : before.ActivationsBelow limit) (owner : activation < limit) : after.ActivationsBelow limit := by
  induction bound with
  | nil | exhausted => exact bounded
  | cons _ first _ ih => exact ih (first.activationsBelow bounded owner)

theorem BindsPattern.activationsBelow {program : RuntimeProgram} {before after : World}
    {activation scope region localSlot source authority access binding} {limit : Identity}
    (bound : BindsPattern program activation scope region before localSlot source authority access binding after)
    (bounded : before.ActivationsBelow limit) (owner : activation < limit) : after.ActivationsBelow limit := by
  cases bound with
  | owned bound => exact bound.activationsBelow bounded owner
  | borrowed _ _ allocated borrowed =>
    exact borrowed.activationsBelow (allocated.activationsBelow bounded (by simpa using owner))

end Kernel

namespace Execution

open _root_.Glorious.Language.Kernel
theorem ReturnsResources.activation {program : Kernel.Program} {source receiver : Context}
    {before after : World} {result : Address} {context : Context}
    (returned : ReturnsResources program source receiver before result context after) :
    context.activation = receiver.activation := by
  cases returned <;> rfl

theorem ReturnsResources.activationsBelow {program : Kernel.Program} {source receiver : Context}
    {before after : World} {result : Address} {context : Context} {limit : Identity}
    (returned : ReturnsResources program source receiver before result context after)
    (bounded : before.ActivationsBelow limit) (owner : receiver.activation < limit) : after.ActivationsBelow limit := by
  cases returned with
  | localReturn => exact bounded
  | invocationReturn _ _ _ bound relinquished => exact relinquished.activationsBelow (bound.activationsBelow bounded owner)



theorem Temporary.activationsBelow {program : Kernel.Program} {context : Context}
    {type : Term} {before after : World} {address : Address} {limit : Identity}
    (allocated : Temporary program context type before address after)
    (bounded : before.ActivationsBelow limit) (owner : context.activation < limit) : after.ActivationsBelow limit :=
  allocated.choose_spec.activationsBelow bounded (by simpa using owner)

theorem Protect.activationsBelow {program : Kernel.Program} {context : Context}
    {before after : World} {source destination : Address} {authority : Authority} {limit : Identity}
    (kept : Protect program context before source authority destination after)
    (bounded : before.ActivationsBelow limit) (owner : context.activation < limit) : after.ActivationsBelow limit := by
  obtain ⟨_,_,_,allocated,transferred⟩ := kept
  exact transferred.activationsBelow (allocated.activationsBelow bounded owner)

theorem ProtectsAttemptFor.activationsBelow {program : Kernel.Program} {context : Context}
    {before after : World} {footprint : List Address} {sources : List ResolvedPlace} {destinations : List Address}
    {outcome : PreparationOutcome} {limit : Identity}
    (kept : ProtectsAttemptFor program context footprint before sources destinations after outcome)
    (bounded : before.ActivationsBelow limit) (owner : context.activation < limit) : after.ActivationsBelow limit := by
  induction kept with
  | nil | exhausted => exact bounded
  | cons _ first _ ih => exact ih (first.activationsBelow bounded owner)

theorem Captures.activationsBelow {program : Kernel.Program} {context : Context}
    {before after : World} {captures : List Capture} {addresses : List Address} {limit : Identity}
    (captured : Captures program context before captures addresses after)
    (bounded : before.ActivationsBelow limit) (owner : context.activation < limit) : after.ActivationsBelow limit := by
  induction captured with
  | nil => exact bounded
  | owned _ _ allocated acquired _ ih | borrowed _ _ _ allocated acquired _ ih =>
    exact ih (acquired.activationsBelow (allocated.activationsBelow bounded owner))

theorem ConsumesReceiver.activationsBelow {before after : World} {address authority access} {limit : Identity}
    (consumed : ConsumesReceiver before address authority access after)
    (bounded : before.ActivationsBelow limit) : after.ActivationsBelow limit := by
  cases consumed with
  | lent => exact bounded
  | owned _ _ _ _ written => exact World.write_activationsBelow written bounded

theorem ConsumesAvailability.activationsBelow {before after : World} {address authority id access} {limit : Identity}
    (consumed : ConsumesAvailability before address authority id access after)
    (bounded : before.ActivationsBelow limit) : after.ActivationsBelow limit := by
  cases consumed with
  | lent => exact bounded
  | owned _ _ _ _ _ _ written =>
    have retained := World.write_activationsBelow written bounded
    exact retained

theorem FinishesReceiver.activationsBelow {before after : World} {receiver : ResolvedPlace} {access : Access}
    {limit : Identity} (finished : FinishesReceiver before receiver access after)
    (bounded : before.ActivationsBelow limit) : after.ActivationsBelow limit := by
  cases finished with
  | lent => exact bounded
  | owned _ _ _ _ _ _ written => exact World.write_activationsBelow written bounded

theorem FinishesEntry.activationsBelow {before after : World} {source : EntrySource} {limit : Identity}
    (finished : FinishesEntry before source after) (bounded : before.ActivationsBelow limit) :
    after.ActivationsBelow limit := by
  cases finished with
  | supplied => exact bounded
  | resident inner | contextual inner => exact inner.activationsBelow bounded

theorem PreparesEntryAttempt.activationsBelow {program : Kernel.Program} {callee : Context} {function : Function}
    {before after : World} {source : EntrySource} {inputs : List InvocationInput} {outcome : PreparationOutcome}
    {limit : Identity} (prepared : PreparesEntryAttempt program callee function before source inputs after outcome)
    (bounded : before.ActivationsBelow limit) (owner : callee.activation < limit) : after.ActivationsBelow limit := by
  cases prepared with
  | supplied => exact bounded
  | resident _ _ lent _ consumed => exact consumed.activationsBelow (lent.activationsBelow bounded owner)
  | contextual _ _ _ _ receiver witness _ consumed finished =>
    exact finished.activationsBelow (consumed.activationsBelow
      (witness.activationsBelow (receiver.activationsBelow bounded owner) owner))
  | residentExhausted | contextualReceiverExhausted => exact bounded
  | contextualWitnessExhausted _ _ _ _ lent _ => exact lent.activationsBelow bounded owner

theorem EnterWorldAttempt.activationsBelow {program : Kernel.Program} {before : State} {caller context : Context}
    {function : Function} {source : EntrySource} {after : World} {outcome : PreparationOutcome}
    (attempted : EnterWorldAttempt program before caller function source context after outcome)
    (bounded : before.world.ActivationsBelow before.nextActivation) :
    after.ActivationsBelow (before.nextActivation+1) := by
  have owner : context.activation < before.nextActivation+1 := by
    simpa only [attempted.fresh_context.1] using Nat.lt_succ_self before.nextActivation
  cases attempted with
  | inputs _ region prepared _ bound finished _ _ =>
    have retained := bound.activationsBelow
      (prepared.activationsBelow (region.activationsBelow (bounded.mono (Nat.le_succ _))) owner) (Nat.lt_succ_self _)
    cases outcome with
    | complete => exact finished.activationsBelow retained
    | exhausted => rw [finished]; exact retained
  | preparationExhausted _ region prepared _ _ _ =>
    exact prepared.activationsBelow (region.activationsBelow (bounded.mono (Nat.le_succ _))) owner

theorem EnterWorld.activation_lt {program : Kernel.Program} {before : State} {caller context : Context}
    {function : Function} {source : EntrySource} {after : World}
    (entered : EnterWorld program before caller function source context after) :
    context.activation < before.nextActivation+1 := by
  rw [entered.fresh_context.1]
  exact Nat.lt_succ_self _

/-- Entry's owner is fresh against all recorded homes, including dead roots.
The allocation supply is the authority; callers do not provide a separate
cleanup-exclusion certificate for this particular invocation. -/
theorem EnterWorld.prior_home_not_owned {program : Kernel.Program} {before : State}
    {caller context : Context} {function : Function} {source : EntrySource} {after : World}
    {id : Identity} {root : Root}
    (entered : EnterWorld program before caller function source context after)
    (bounded : before.world.ActivationsBelow before.nextActivation)
    (found : before.world.roots.get id = some root) : ¬ OwnedByActivation root context.activation := by
  rw [entered.fresh_context.1]
  exact bounded.no_future_home (Nat.le_refl _) found

theorem RegionEnds.activationsBelow {before after : World} {region limit : Identity}
    (ended : RegionEnds before region after) (bounded : before.ActivationsBelow limit) :
    after.ActivationsBelow limit := by rcases ended with ⟨_,rfl⟩; exact bounded


end Execution
end Glorious.Language
