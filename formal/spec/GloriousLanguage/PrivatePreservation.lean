import GloriousLanguage.PrivateLocalControl
import GloriousLanguage.PrivateForeignPreservation
import GloriousLanguage.ControlOriginPreservation

/-! The complete executable relation preserves a saved private caller slot
through an admitted invocation interval. The proof follows all six transition
families and excludes a hook pop using the current invocation boundary. -/
namespace Glorious.Language.Execution

open _root_.Glorious.Language.Kernel

theorem LocalStep.hook_pop_yield {program : Kernel.Program} {before after : State} {event : Option Event}
    {caller : Context} {address handle : Address} {authority : Authority} {loan : Identity}
    {next : Task} {outer : List Frame} (step : LocalStep program before event after)
    (stack : before.frames = .hook caller address authority handle loan next :: outer)
    (popped : after.frames = outer) : ∃ context result, before.task = .yield context result := by
  cases step
  all_goals try exact ⟨_,_,by assumption⟩
  all_goals simp_all only [reduceCtorEq]
  all_goals try (have size := congrArg List.length popped; simp at size <;> omega)
  case enterTail _ _ route _ _ _ => cases route <;> simp_all

theorem Step.private_guard {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {event : Option Event}
    {id owner savedScope loan : Identity} {root : Root} {inner outer : List Frame}
    {caller : Context} {address handle : Address} {authority : Authority} {next : Task}
    (step : Step program host before event after)
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (admitted : before.ControlWellFormed) (slot : before.world.PrivateSlot id root)
    (home : root.home = .temporary owner savedScope) (control : PrivateControl id owner inner before.task)
    (stack : before.frames = inner ++ .hook caller address authority handle loan next :: outer)
    (outerOutside : id ∉ outer.flatMap Frame.rootSupport)
    (noLeave : ∀ brand, event ≠ some (.leave brand))
    (noReplay : ∀ key last, event ≠ some (.replay key last))
    (noSuspend : ∀ key, event ≠ some (.suspend key))
    (internalOperation : ∀ context operation arguments payload,
      before.task = .perform context operation arguments payload →
      (Contracts.InvocationBoundary.caller caller (.hook caller address authority handle loan next :: outer)).InternalOperation
        program before operation arguments payload) :
    after.world.PrivateSlot id root ∧
      ((∃ remaining, after.frames = remaining ++ .hook caller address authority handle loan next :: outer ∧
        PrivateControl id owner remaining after.task) ∨
      (LocalStep program before event after ∧ event = none ∧ inner = [] ∧ after.frames = outer)) := by
  have ownerBound : owner < before.nextActivation :=
    admitted.activations.homes id root slot.found owner (by simp [HomeOwnedByActivation,home])
  rcases step with localStep | atom | effect | branch | primitive | foreign
  · refine ⟨localStep.private_slot typed.1 slot control.1
      (fun context destination body rest frames => control.binding_outside (stack.symm.trans frames)),?_⟩
    exact (localStep.private_control typed.1 slot home ownerBound control stack).elim Or.inl
      (fun returned => Or.inr ⟨localStep,returned⟩)
  · have frames : after.frames = before.frames := by cases atom <;> rfl
    exact ⟨atom.private_slot typed.1 slot control.1,
      Or.inl ⟨inner,frames.trans stack,atom.private_control typed.1 slot control⟩⟩
  · exact ⟨effect.private_slot valid inventory typed admitted.suspensions slot home control.2.2.2 stack
      internalOperation noReplay noSuspend,
      Or.inl (effect.private_control valid inventory typed admitted.suspensions slot home ownerBound control stack
        internalOperation noReplay noSuspend)⟩
  · obtain ⟨frames,afterControl⟩ := branch.private_control typed.1 slot control noLeave
    exact ⟨branch.private_slot typed.1 slot control.1 control.2.2.1,
      Or.inl ⟨inner,frames.trans stack,afterControl⟩⟩
  · have frames : after.frames = before.frames := by cases primitive <;> rfl
    exact ⟨primitive.private_slot typed.1 slot control.1,
      Or.inl ⟨inner,frames.trans stack,primitive.private_control typed.1 slot control⟩⟩
  · exact ⟨foreign.private_slot lawful typed.1 slot control.1,
      Or.inl (foreign.private_control lawful typed.1 slot control stack outerOutside)⟩

/-- Interval guards supply the actual internal route at every pre-state.
A hook pop would require a caller handoff at that same pre-state, which the
admitted invocation excludes. No future slot-privacy certificate is assumed. -/
theorem _root_.Glorious.Language.Contracts.InvocationRun.private_guard
    {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event}
    {id owner savedScope loan : Identity} {root : Root} {inner outer : List Frame}
    {caller returnTo : Context} {address handle : Address} {authority : Authority} {next : Task}
    (run : Contracts.InvocationRun program host
      (.caller returnTo (.hook caller address authority handle loan next :: outer)) before trace after)
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (admitted : before.ControlWellFormed) (slot : before.world.PrivateSlot id root)
    (home : root.home = .temporary owner savedScope) (control : PrivateControl id owner inner before.task)
    (stack : before.frames = inner ++ .hook caller address authority handle loan next :: outer)
    (outerOutside : id ∉ outer.flatMap Frame.rootSupport)
    (safe : ∀ event ∈ trace, (∀ brand, event ≠ .leave brand) ∧
      (∀ key last, event ≠ .replay key last) ∧ (∀ key, event ≠ .suspend key)) :
    ∃ remaining, after.frames = remaining ++ .hook caller address authority handle loan next :: outer ∧
      after.world.PrivateSlot id root ∧ PrivateControl id owner remaining after.task := by
  refine TransitionSystem.Steps.rec
    (system := Contracts.InvocationSystem program host
      (.caller returnTo (.hook caller address authority handle loan next :: outer)))
    (motive := fun before trace after _ => ∀ {inner : List Frame},
      Typing.WorldTyped program before.world → before.ControlWellFormed → before.world.PrivateSlot id root →
      PrivateControl id owner inner before.task →
      before.frames = inner ++ .hook caller address authority handle loan next :: outer →
      (∀ event ∈ trace, (∀ brand, event ≠ .leave brand) ∧
        (∀ key last, event ≠ .replay key last) ∧ (∀ key, event ≠ .suspend key)) →
      ∃ remaining, after.frames = remaining ++ .hook caller address authority handle loan next :: outer ∧
        after.world.PrivateSlot id root ∧ PrivateControl id owner remaining after.task)
    ?_ ?_ ?_ run typed admitted slot control stack safe
  · intro before inner _ _ slot control stack _
    exact ⟨inner,stack,slot,control⟩
  · intro before middle after trace step rest ih inner typed admitted slot control stack safe
    have actual := step.2
    obtain ⟨middleSlot,middleControl⟩ := actual.private_guard valid inventory lawful typed admitted slot home control stack outerOutside
      (by simp) (by simp) (by simp) (fun context operation arguments payload task => step.1.2.2.1 _ _ _ _ task)
    rcases middleControl with ⟨remaining,middleFrames,middleControl⟩ | ⟨localStep,_,rfl,middleFrames⟩
    · exact ih (actual.worldTyped valid inventory lawful typed) (actual.controlWellFormed valid inventory lawful typed admitted (by simp))
        middleSlot middleControl middleFrames safe
    · obtain ⟨context,result,yieldTask⟩ := localStep.hook_pop_yield stack middleFrames
      exact False.elim (Contracts.InvocationStep.not_handoff step ⟨context,result,yieldTask,stack⟩)
  · intro before middle after event trace step rest ih inner typed admitted slot control stack safe
    have actual := step.2
    have safeEvent := safe event List.mem_cons_self
    obtain ⟨middleSlot,middleControl⟩ := actual.private_guard valid inventory lawful typed admitted slot home control stack outerOutside
      (fun brand equal => safeEvent.1 brand (Option.some.inj equal))
      (fun key last equal => safeEvent.2.1 key last (Option.some.inj equal))
      (fun key equal => safeEvent.2.2 key (Option.some.inj equal))
      (fun context operation arguments payload task => step.1.2.2.1 _ _ _ _ task)
    rcases middleControl with ⟨remaining,middleFrames,middleControl⟩ | ⟨_,impossible,_⟩
    · by_cases fatal : event = Event.fatal .resource
      · subst event
        rw [(Contracts.InvocationRun.execution rest).after_eq_of_fatal actual.fatal_task]
        exact ⟨remaining,middleFrames,middleSlot,middleControl⟩
      · exact ih (actual.worldTyped valid inventory lawful typed)
          (actual.controlWellFormed valid inventory lawful typed admitted (fun equal => fatal (Option.some.inj equal)))
          middleSlot middleControl middleFrames (fun observed member => safe observed (List.mem_cons_of_mem event member))
    · cases impossible

end Glorious.Language.Execution
