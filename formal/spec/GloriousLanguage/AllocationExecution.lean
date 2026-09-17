import GloriousLanguage.PreparationOutcomes
import GloriousLanguage.AllocationPreservation
import GloriousLanguage.InputBatchProgress

/-! Positively admitted local allocation requests progress in the actual
machine, either to fresh storage or to terminal resource exhaustion. Entry
exhaustion retains its successful preparation prefix and partial world. -/
namespace Glorious.Language
open Kernel

theorem Kernel.LendsResidentExhausted.allocation {program : RuntimeProgram} {region : Identity}
    {before : World} {address : Address} {authority : Authority} {access : Access}
    (failed : LendsResidentExhausted program region before address authority access) :
    ∃ type layout, AllocationExhausted program.declarations before region type layout := by
  cases failed with
  | lent _ _ _ _ _ _ exhausted => exact ⟨_,_,exhausted⟩

theorem Kernel.BindsInputExhausted.allocation {program : RuntimeProgram} {region : Identity}
    {before : World} {input : InvocationInput} (failed : BindsInputExhausted program region before input) :
    ∃ type layout, AllocationExhausted program.declarations before region type layout := by
  cases failed with
  | owned _ _ _ exhausted => exact ⟨_,_,exhausted⟩
  | lent _ _ exhausted => exact exhausted.allocation

namespace Execution

theorem ConsumesReceiver.region_state {before after : World}
    {address : Address} {authority : Authority} {access : Access}
    (consumed : ConsumesReceiver before address authority access after) :
    after.liveRegions = before.liveRegions ∧ after.nextRegion = before.nextRegion := by
  cases consumed with
  | lent => exact ⟨rfl,rfl⟩
  | owned _ _ _ _ written => exact World.write_region_state written

theorem ConsumesAvailability.region_state {before after : World}
    {address : Address} {authority : Authority} {id : Identity} {access : Access}
    (consumed : ConsumesAvailability before address authority id access after) :
    after.liveRegions = before.liveRegions ∧ after.nextRegion = before.nextRegion := by
  cases consumed with
  | lent => exact ⟨rfl,rfl⟩
  | owned _ _ _ _ _ _ written =>
    have state := World.write_region_state written
    exact ⟨state.1,state.2⟩

theorem PreparesEntryAttempt.region_state {program : Kernel.Program} {callee : Context}
    {function : Function} {before after : World} {source : EntrySource}
    {inputs : List InvocationInput} {outcome : PreparationOutcome}
    (prepared : PreparesEntryAttempt program callee function before source inputs after outcome) :
    after.liveRegions = before.liveRegions ∧ after.nextRegion = before.nextRegion := by
  cases prepared with
  | supplied | residentExhausted | contextualReceiverExhausted => exact ⟨rfl,rfl⟩
  | resident _ _ lent _ consumed =>
    have a := Kernel.LendsResident.region_state lent
    have b := consumed.region_state
    exact ⟨b.1.trans a.1,b.2.trans a.2⟩
  | contextual _ _ _ _ receiver witness _ consumed finished =>
    have a := Kernel.LendsResident.region_state receiver
    have b := Kernel.LendsResident.region_state witness
    have c := consumed.region_state
    have d := finished.region_state
    exact ⟨d.1.trans (c.1.trans (b.1.trans a.1)),d.2.trans (c.2.trans (b.2.trans a.2))⟩
  | contextualWitnessExhausted _ _ _ _ lent _ => exact Kernel.LendsResident.region_state lent

theorem FinishesEntry.region_state {before after : World} {source : EntrySource}
    (finished : FinishesEntry before source after) :
    after.liveRegions = before.liveRegions ∧ after.nextRegion = before.nextRegion := by
  cases finished with
  | supplied => exact ⟨rfl,rfl⟩
  | resident finished | contextual finished =>
    cases finished with
    | lent => exact ⟨rfl,rfl⟩
    | owned _ _ _ _ _ _ written => exact World.write_region_state written

/-- Preparation, ordered input binding and receiver finishing preserve the
actual fresh lifetime, even when an allocation exhausts midway through entry. -/
theorem EnterWorldAttempt.region_live {program : Kernel.Program} {before : State}
    {caller callee : Context} {function : Function} {source : EntrySource}
    {after : World} {outcome : PreparationOutcome}
    (attempted : EnterWorldAttempt program before caller function source callee after outcome) :
    callee.region ∈ after.liveRegions := by
  have region := attempted.fresh_context.2.2
  rw [region]
  cases attempted with
  | @inputs withRegion preparedWorld inputs environment declaration boundWorld _ _ _ fresh prepared _ bound finished _ _ =>
    have finalRegions : after.liveRegions = boundWorld.liveRegions := by
      cases outcome with
      | complete => exact finished.region_state.1
      | exhausted => subst after; rfl
    rw [finalRegions,bound.region_state.1,prepared.region_state.1,fresh.2]
    exact List.mem_cons_self
  | preparationExhausted _ fresh prepared _ _ _ =>
    rw [prepared.region_state.1,fresh.2]
    exact List.mem_cons_self

theorem PreparesEntryAttempt.exhausted_allocation {program : Kernel.Program} {callee : Context}
    {function : Function} {before after : World} {source : EntrySource} {inputs : List InvocationInput}
    (attempted : PreparesEntryAttempt program callee function before source inputs after .exhausted) :
    ∃ type layout, AllocationExhausted program.declarations after callee.region type layout := by
  cases attempted with
  | residentExhausted _ _ failed => exact failed.allocation
  | contextualReceiverExhausted _ _ _ _ failed => exact failed.allocation
  | contextualWitnessExhausted _ _ _ _ _ failed => exact failed.allocation


/-- Fatal states have no executable suffix at all, including cleanup,
completion clauses, foreign callbacks and source-level cancellation. -/
theorem Step.fatal_no_step {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {reason : Fatal} {event : Option Event}
    (fatal : before.task = .fatal reason) : ¬ Step program host before event after := by
  intro step
  rcases step with ordinary | atom | effect | control | primitive | foreign
  · cases ordinary <;> simp_all
  · cases atom <;> simp_all
  · cases effect <;> simp_all
  · cases control <;> simp_all
  · cases primitive <;> simp_all
  · cases foreign <;> simp_all

theorem Run.fatal_refl {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {reason : Fatal} {trace : List Event}
    (fatal : before.task = .fatal reason) (run : Run program host before trace after) :
    trace = [] ∧ after = before := by
  cases run with
  | refl => exact ⟨rfl,rfl⟩
  | silent step _ | visible step _ => exact False.elim (Step.fatal_no_step fatal step)

/-- The failed entry identifies its actual phase: a preparation lease prefix,
or the original whole input batch with its completed binding prefix and still
ready failing suffix. Neither alternative invents a successful preparation. -/
theorem EnterWorldAttempt.exhausted_prefix {program : Kernel.Program} {before : State}
    {caller callee : Context} {function : Function} {source : EntrySource} {after : World}
    (attempted : EnterWorldAttempt program before caller function source callee after .exhausted) :
    (∃ withRegion, FreshRegion before.world before.world.nextRegion withRegion ∧
      PreparesEntryAttempt program callee function withRegion source [] after .exhausted) ∨
    (∃ withRegion prepared inputs front input rest bindings,
      FreshRegion before.world before.world.nextRegion withRegion ∧
      PreparesEntry program callee function withRegion source inputs prepared ∧
      IncomingResources program function before.world (source.originalInputs function) ∧
      InvocationInputsReadyFor program prepared (inputs.flatMap InvocationInput.clearedStorage) inputs ∧
      inputs = front ++ input :: rest ∧
      BindsInputsFor program (.activation before.nextActivation)
        before.nextActivation before.world.nextRegion before.world.nextRegion
        (inputs.flatMap InvocationInput.clearedStorage) prepared front bindings after ∧
      InvocationInputsReadyFor program after (inputs.flatMap InvocationInput.clearedStorage) (input :: rest) ∧
      BindsInputExhausted program before.world.nextRegion after input) := by
  cases attempted
  case preparationExhausted freshWorld declaration selected fresh incoming contextEq unsafeOk prepared =>
    exact Or.inl ⟨_,fresh,prepared⟩
  case inputs withRegion prepared inputs bindings declaration bound selected fresh entry incoming contextEq unsafeOk binding ending =>
    change after = bound at ending
    subst after
    obtain ⟨front,input,rest,equation,beginning,remaining,failed⟩ := binding.exhausted_prefix
    exact Or.inr ⟨withRegion,prepared,inputs,front,input,rest,bindings,
      fresh,entry,incoming,binding.ready,equation,beginning,remaining,failed⟩

theorem EnterWorldAttempt.exhausted_allocation {program : Kernel.Program} {before : State}
    {caller callee : Context} {function : Function} {source : EntrySource} {after : World}
    (attempted : EnterWorldAttempt program before caller function source callee after .exhausted) :
    ∃ type layout, AllocationExhausted program.declarations after before.world.nextRegion type layout := by
  have region := attempted.fresh_context.2.2
  rcases attempted.exhausted_prefix with ⟨_,_,failed⟩ | ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,failed⟩
  · simpa only [region] using failed.exhausted_allocation
  · exact failed.allocation

/-- No allocation success is assumed. The positive request supplies all static
premises, and the physical alternative constructs the actual executable step. -/
theorem Step.evaluate_allocation_progress {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {context : Context} {lexical : Local} {value next : Code} {layout : Layout}
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .run context (.evaluate lexical value next))
    (request : AllocationRequest program.declarations before.world context.region (context.local lexical).type layout) :
    ∃ event after, Step program host before event after ∧ Typing.WorldTyped program after.world := by
  rcases request.success_or_exhausted (.localSlot context.activation context.scope) (context.local lexical).mutable with
    ⟨address,allocated,allocation⟩ | exhausted
  · exact ⟨_,_,Or.inl (.evaluate task rfl allocation),allocation.worldTyped typed⟩
  · exact ⟨_,_,Or.inl (.evaluateExhausted task rfl exhausted),typed⟩

theorem Step.bind_allocation_progress {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {context : Context} {lexical : Local} {atom : Atom} {next : Code} {layout : Layout}
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .run context (.bind lexical atom next))
    (request : AllocationRequest program.declarations before.world context.region (context.local lexical).type layout) :
    ∃ event after, Step program host before event after ∧ Typing.WorldTyped program after.world := by
  rcases request.success_or_exhausted (.localSlot context.activation context.scope) (context.local lexical).mutable with
    ⟨address,allocated,allocation⟩ | exhausted
  · exact ⟨_,_,Or.inl (.bind task rfl allocation),allocation.worldTyped typed⟩
  · exact ⟨_,_,Or.inl (.bindExhausted task rfl exhausted),typed⟩

theorem Step.invoke_allocation_progress {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {context : Context} {lexical : Local} {call : Invocation} {next : Code} {layout : Layout}
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .run context (.invoke lexical call next))
    (request : AllocationRequest program.declarations before.world context.region (context.local lexical).type layout) :
    ∃ event after, Step program host before event after ∧ Typing.WorldTyped program after.world := by
  rcases request.success_or_exhausted (.localSlot context.activation context.scope) (context.local lexical).mutable with
    ⟨address,allocated,allocation⟩ | exhausted
  · exact ⟨_,_,Or.inl (.invoke task rfl allocation),allocation.worldTyped typed⟩
  · exact ⟨_,_,Or.inl (.invokeExhausted task rfl exhausted),typed⟩

/-- Resource exhaustion is a real terminal event. It neither starts cleanup
nor restores a pre-preparation world, even at a mandatory-tail entry. -/
theorem Step.enter_exhausted {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {caller callee : Context} {function : Function} {source : EntrySource}
    {tail : Bool} {after : World}
    (task : before.task = .enter caller function source tail)
    (attempted : EnterWorldAttempt program before caller function source callee after .exhausted) :
    Step program host before (some (.fatal .resource))
      { before with
        world := after, task := .fatal .resource,
        nextActivation := before.nextActivation+1, nextBrand := before.nextBrand+1 } :=
  Or.inl (.enterExhausted task attempted)

end Execution
end Glorious.Language
