import GloriousLanguage.PrivateBranchPreservation

/-! Foreign mutation, real callback inputs and retained callback cleanup
preserve the same unexposed caller slot. Ambient exposure projects enclosing
host handoffs only; a source hook guard does not expose its saved handle. -/
namespace Glorious.Language

open _root_.Glorious.Language.Kernel Execution

theorem Execution.ForeignSession.known_avoids_root {session : ForeignSession} {id : Identity}
    (outside : id ∉ session.rootSupport) : ∀ place ∈ session.known, place.address.root ≠ id := by
  simp only [ForeignSession.rootSupport,ForeignCall.rootSupport,List.mem_append,List.mem_cons,not_or] at outside
  intro place member same
  simp only [ForeignSession.known,List.mem_append,List.mem_map] at member
  rcases member with ⟨address,present,rfl⟩ | present
  · exact outside.1.2.2 (List.mem_map.mpr ⟨address,present,same⟩)
  · exact outside.2 (List.mem_map.mpr ⟨place,present,same⟩)

namespace Foreign

theorem Model.Lawful.host_private {program : Kernel.Program} {model : Model} {before after : World}
    {session : ForeignSession} {imported : Import} {contract : Contract}
    {observation next : List Nat} {actions : List MutationAction} {action : HostAction} {id : Identity} {root : Root}
    (lawful : model.Lawful program) (well : before.WellFormed)
    (selected : Selected program model session.call imported contract) (active : contract.session before session)
    (transition : model.step session.call.binding.declaration before session observation actions after action next)
    (slot : before.PrivateSlot id root) (outside : id ∉ session.rootSupport) :
    after.PrivateSlot id root ∧
      id ∉ (session.advance (TransactionOutputs (.host session.call.destination.root) actions) next).rootSupport := by
  have preserved := lawful.advance_internal_root well selected active transition
    ⟨slot.found,slot.internalHome,Execution.ForeignSession.known_avoids_root outside,slot.safe.1⟩
  have changed := (lawful.step _ _ _ _ _ _ _ _ _ selected well active transition).1
  refine ⟨slot.retain preserved.1 preserved.2.2.2 ?_,?_⟩
  · simpa only [changed.availability] using slot.safe.2.1
  · intro member
    simp only [ForeignSession.rootSupport,List.mem_append] at member
    rcases member with currentCall | exposed
    · exact outside (List.mem_append_left _ currentCall)
    · obtain ⟨place,present,same⟩ := List.mem_map.mp exposed
      exact preserved.2.2.1 place (List.mem_append_right _ present) same


theorem Step.private_slot {program : Kernel.Program} {model : Model} {before after : State} {event : Option Event}
    {id : Identity} {root : Root} (step : Step program model before event after)
    (lawful : model.Lawful program) (well : before.world.WellFormed)
    (slot : before.world.PrivateSlot id root) (outside : id ∉ before.task.rootSupport) :
    after.world.PrivateSlot id root := by
  cases step
  all_goals simp_all only [Task.rootSupport,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
  case enter kept _ _ _ => exact (ProtectsAttemptFor.private_slot kept well slot).1
  case host selected active transition | fault selected active transition =>
    exact (lawful.host_private well selected active transition slot outside).1
  case result selected active transition _ moved =>
    have middle := (lawful.host_private well selected active transition slot outside).1
    have destinationOutside : _ := outside
    simp only [ForeignSession.rootSupport,ForeignCall.rootSupport,List.mem_append,List.mem_cons,not_or] at destinationOutside
    exact moved.private_slot middle (Ne.symm destinationOutside.1.2.1)
  case callback selected active transition _ _ =>
    exact (lawful.host_private well selected active transition slot outside).1
  case callbackResult kept retired =>
    exact retired.private_slot (kept.private_slot well slot).1 (Ne.symm outside.2)

theorem AmbientExposed.avoids_root {frames : List Frame} {id : Identity}
    (outside : id ∉ frames.flatMap Frame.rootSupport) :
    id ∉ (AmbientExposed frames).map (fun place => place.address.root) := by
  induction frames with
  | nil => simp [AmbientExposed]
  | cons frame rest ih =>
    simp only [List.flatMap_cons,List.mem_append,not_or] at outside
    cases frame <;> simp only [AmbientExposed,List.flatMap_cons,List.nil_append,List.map_append]
    all_goals try exact ih outside.2
    simp only [List.mem_append,not_or]
    refine ⟨?_,ih outside.2⟩
    intro member
    obtain ⟨place,present,same⟩ := List.mem_map.mp member
    exact (Execution.ForeignSession.known_avoids_root
      (fun member => outside.1 (List.mem_append_left _ member))) place present same

theorem AmbientExposed.private_stack {inner outer : List Frame} {id loan : Identity}
    {caller : Execution.Context} {address handle : Address} {authority : Authority} {next : Task}
    (innerOutside : id ∉ inner.flatMap Frame.rootSupport) (outerOutside : id ∉ outer.flatMap Frame.rootSupport) :
    id ∉ (AmbientExposed (inner ++ .hook caller address authority handle loan next :: outer)).map
      (fun place => place.address.root) := by
  simpa only [AmbientExposed,List.flatMap_append,List.flatMap_cons,List.nil_append,
    List.map_append,List.mem_append,not_or] using
    And.intro (AmbientExposed.avoids_root innerOutside) (AmbientExposed.avoids_root outerOutside)

theorem CallbackInputs.avoids_root {world : World} {formals : List Local}
    {arguments : List ResolvedPlace} {inputs : List InvocationInput} {id : Identity} {root : Root}
    (prepared : CallbackInputs world formals arguments inputs) (slot : world.PrivateSlot id root) :
    id ∉ inputs.flatMap InvocationInput.rootSupport := by
  rw [prepared.1]
  intro member
  obtain ⟨input,present,member⟩ := List.mem_flatMap.mp member
  obtain ⟨⟨⟨formal,argument⟩,index⟩,pairMember,rfl⟩ := List.mem_map.mp present
  have same : id = argument.address.root := by simpa only [InvocationInput.rootSupport,
    List.mem_cons,List.not_mem_nil,or_false] using member
  have argumentAt := (List.getElem?_zip_eq_some.mp (List.mem_zipIdx_iff_getElem?.mp pairMember)).2
  obtain ⟨_,_,value,stored,_⟩ := prepared.2.get_right argumentAt
  exact slot.stored_outside stored same.symm

theorem CallbackReturnTask.avoids_root {session : ForeignSession} {registration : CallbackEntry} {result : Address}
    {lease : Option ReceiverLease} {next : Code} {id : Identity}
    (sessionOutside : id ∉ session.rootSupport) (resultOutside : id ≠ result.root)
    (leaseOutside : id ∉ lease.toList.map (fun lease => lease.handle.root)) :
    id ∉ (CallbackReturnTask session registration result lease next).rootSupport := by
  have contextOutside : id ∉ session.call.context.rootSupport :=
    fun member => sessionOutside (List.mem_append_left _ (List.mem_append_left _ member))
  cases lease <;> simp_all [CallbackReturnTask,Task.rootSupport]

theorem CallbackReturnTask.private_activation {session : ForeignSession} {registration : CallbackEntry} {result : Address}
    {lease : Option ReceiverLease} {next : Code} {owner : Identity} {returning : Bool}
    (outside : session.call.context.activation ≠ owner) :
    (CallbackReturnTask session registration result lease next).PrivateActivation owner returning := by
  cases lease <;> simp_all [CallbackReturnTask,Task.PrivateActivation]

theorem Step.private_control {program : Kernel.Program} {model : Model} {before after : State} {event : Option Event}
    {id owner loan : Identity} {root : Root} {inner outer : List Frame}
    {caller : Execution.Context} {address handle : Address} {authority : Authority} {next : Task}
    (step : Step program model before event after)
    (lawful : model.Lawful program) (well : before.world.WellFormed)
    (slot : before.world.PrivateSlot id root) (control : PrivateControl id owner inner before.task)
    (stack : before.frames = inner ++ .hook caller address authority handle loan next :: outer)
    (outerOutside : id ∉ outer.flatMap Frame.rootSupport) :
    ∃ remaining, after.frames = remaining ++ .hook caller address authority handle loan next :: outer ∧
      PrivateControl id owner remaining after.task := by
  obtain ⟨taskRoots,frameRoots,taskOwner,frameOwners⟩ := control
  cases step
  all_goals simp_all only [Task.rootSupport,Task.PrivateActivation,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,not_or]
  case enter kept _ _ _ =>
    have argumentsOutside := (ProtectsAttemptFor.private_slot kept well slot).2
    have ambientOutside := AmbientExposed.private_stack
      (caller := caller) (address := address) (authority := authority) (handle := handle)
      (loan := loan) (next := next) frameRoots outerOutside
    refine ⟨inner,rfl,?_,frameRoots,taskOwner,frameOwners⟩
    simp only [Task.rootSupport,ForeignSession.rootSupport,ForeignCall.rootSupport,List.mem_append,List.mem_cons,not_or]
    exact ⟨⟨taskRoots.1,taskRoots.2.1,by
      intro member
      obtain ⟨address,present,same⟩ := List.mem_map.mp member
      exact argumentsOutside address present same⟩,ambientOutside⟩
  case host selected active transition =>
    exact ⟨inner,rfl,(lawful.host_private well selected active transition slot taskRoots).2,
      frameRoots,taskOwner,frameOwners⟩
  case result selected active transition _ moved =>
    have middle := (lawful.host_private well selected active transition slot taskRoots).1
    have resultOutside : _ := moved
    cases resultOutside with
    | move stored _ _ _ _ _ _ _ _ =>
      have resultOutside := middle.stored_outside stored
      refine ⟨inner,rfl,?_,frameRoots,taskOwner,frameOwners⟩
      have contextOutside : _ := taskRoots
      simp only [ForeignSession.rootSupport,ForeignCall.rootSupport,List.mem_append,List.mem_cons,not_or] at contextOutside
      simpa only [Task.rootSupport,List.mem_cons,not_or] using And.intro (Ne.symm resultOutside) contextOutside.1.1
  case callback selected active transition admitted inputs =>
    have middle := lawful.host_private well selected active transition slot taskRoots
    have receiverOutside := middle.1.stored_outside admitted.receiver.choose_spec.1
    have inputsOutside := inputs.avoids_root middle.1
    have contextOutside : id ∉ _ :=
      fun member => taskRoots (List.mem_append_left _ (List.mem_append_left _ member))
    refine ⟨_ :: inner,rfl,?_,?_,taskOwner,⟨taskOwner,frameOwners⟩⟩
    · simp only [Task.rootSupport,EntrySource.rootSupport,List.mem_append,List.mem_cons,not_or]
      exact ⟨contextOutside,Ne.symm receiverOutside,inputsOutside⟩
    · simpa only [List.flatMap_cons,Frame.rootSupport,Option.toList_none,List.map_nil,List.append_nil,
        List.mem_append,not_or] using And.intro middle.2 frameRoots

  case callbackResult context result session registration resultType lease code rest value kept world after task frames stored type keptValue retired =>
    have keptOutside := (keptValue.private_slot well slot).2
    cases inner with
    | nil => cases List.cons.inj stack |>.1
    | cons frame remaining =>
      obtain ⟨head,tail⟩ := List.cons.inj stack
      subst frame
      have frameOutside := frameRoots
      simp only [List.flatMap_cons,Frame.rootSupport,List.mem_append,not_or] at frameOutside
      refine ⟨.hostCallback session registration resultType lease code :: remaining,rfl,
        CallbackReturnTask.avoids_root frameOutside.1.1 (Ne.symm keptOutside) frameOutside.1.2,
        frameRoots,CallbackReturnTask.private_activation frameOwners.1,frameOwners⟩
  case callbackReturned =>
    cases inner with
    | nil => cases List.cons.inj stack |>.1
    | cons frame remaining =>
      obtain ⟨head,tail⟩ := List.cons.inj stack
      subst frame
      refine ⟨remaining,tail,?_⟩
      simp_all [PrivateControl,Task.rootSupport,Task.PrivateActivation,PrivateFrames,
        Frame.PrivateActivation,Frame.rootSupport,ForeignSession.returned,ForeignSession.rootSupport]
  case fault =>
    exact ⟨inner,rfl,by simp [PrivateControl,Task.rootSupport,Task.PrivateActivation,frameRoots,frameOwners]⟩

end Foreign
end Glorious.Language
