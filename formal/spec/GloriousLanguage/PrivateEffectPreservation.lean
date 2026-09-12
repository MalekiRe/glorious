import GloriousLanguage.PrivatePrimitivePreservation

/-! Actual handler storage and cancellation preserve a private caller slot.
An active suspension owns exactly its current suspended roots; its historical
restoration table cannot rehome a distinct private logical root. -/
namespace Glorious.Language.Execution

open Kernel

theorem Protects.private_slot {program : Kernel.Program} {context : Context} {before after : World}
    {sources : List ResolvedPlace} {destinations : List Address} {id : Identity} {root : Root}
    (kept : Protects program context before sources destinations after)
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before) (slot : before.PrivateSlot id root) :
    after.PrivateSlot id root ∧ ∀ address ∈ destinations, address.root ≠ id := by
  induction kept with
  | nil => exact ⟨slot,by simp⟩
  | cons first _ ih =>
    obtain ⟨middle,outside⟩ := first.private_slot typed.1 slot
    obtain ⟨finish,rest⟩ := ih (first.worldTyped valid inventory typed) middle
    exact ⟨finish,fun address member => (List.mem_cons.mp member).elim (fun same => same ▸ outside) (rest address)⟩

theorem RetiresEmpty.private_slot {before after : World} {addresses : List Address} {id : Identity} {root : Root}
    (retired : RetiresEmpty before addresses after) (slot : before.PrivateSlot id root)
    (outside : ∀ address ∈ addresses, address.root ≠ id) : after.PrivateSlot id root := by
  induction retired with
  | nil => exact slot
  | cons _ first _ ih =>
    exact ih (first.private_slot slot (outside _ List.mem_cons_self))
      (fun address member => outside address (List.mem_cons_of_mem _ member))

theorem Installs.private_slot {program : Kernel.Program} {before : State} {after : World}
    {outer : Context} {syntaxNode : Handler} {handler : InstalledHandler} {id : Identity} {root : Root}
    (installed : Installs program before outer syntaxNode handler after)
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world) (slot : before.world.PrivateSlot id root) :
    after.PrivateSlot id root ∧ id ∉ handler.environment.rootSupport := by
  obtain ⟨first,second,sources,captures,captured,bindings,bound,disposed,one,two,_,capturedValues,boundValues,retired,rfl,rfl⟩ := installed
  have secondTyped := two.worldTyped (one.worldTyped typed)
  obtain ⟨capturedSlot,sourcesOutside⟩ := capturedValues.private_slot secondTyped.1
    (FreshRegion.private_slot two (FreshRegion.private_slot one slot))
  obtain ⟨boundSlot,bindingsOutside⟩ := boundValues.private_slot
    (capturedValues.worldTyped valid inventory secondTyped).1 capturedSlot
  refine ⟨retired.private_slot boundSlot sourcesOutside,?_⟩
  intro member
  obtain ⟨binding,present,same⟩ := List.mem_map.mp member
  exact bindingsOutside binding present same

theorem State.SuspensionsWellFormed.private_excluded {state : State} {id key : Identity}
    {root : Root} {suspension : Suspension} (valid : state.SuspensionsWellFormed)
    (slot : state.world.PrivateSlot id root) (found : state.resumptions.get key = some suspension)
    (active : suspension.active = true) : id ∉ suspension.roots := by
  intro member
  obtain ⟨actual,selected,_,suspended⟩ := (valid.active key suspension found active id).mp member
  exact slot.safe.2.2 actual selected key suspended

theorem State.SuspensionsWellFormed.restore_private {state : State} {id key : Identity}
    {root : Root} {suspension : Suspension} (valid : state.SuspensionsWellFormed)
    (slot : state.world.PrivateSlot id root) (found : state.resumptions.get key = some suspension)
    (active : suspension.active = true) :
    (restoreRoots state.world suspension.homes).PrivateSlot id root := by
  have outside := valid.private_excluded slot found active
  have absent : suspension.homes.get id = none := by
    cases selected : suspension.homes.get id with
    | none => rfl
    | some home => exact False.elim (outside (((valid.origin key suspension found).domain id).mp ⟨home,selected⟩))
  apply slot.stable
  · simp only [restoreRoots.get,slot.found,Option.map_some,absent,Option.getD_none]
  · rfl
  · rfl

theorem EffectStep.private_slot {program : Kernel.Program} {before after : State} {event : Option Event}
    {id owner : Identity} {returning : Bool} {root : Root}
    (step : EffectStep program before event after)
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world) (suspensions : before.SuspensionsWellFormed)
    (slot : before.world.PrivateSlot id root) (taskOwner : before.task.PrivateActivation owner returning)
    (noReplay : ∀ key last, event ≠ some (.replay key last)) : after.world.PrivateSlot id root := by
  cases step
  all_goals try exact slot
  all_goals simp_all only [Task.PrivateActivation]
  case install installed => exact (installed.private_slot valid inventory typed slot).1
  case resumeLast => exact False.elim (noReplay _ _ rfl)
  case resumeCopy => exact False.elim (noReplay _ _ rfl)
  case resumeReturns kept | completed _ kept _ _ | serviced _ kept _ _ => exact (kept.private_slot typed.1 slot).1
  case completionIdentity _ started kept _ _ | completion started kept _ _ _ _ =>
    exact (kept.private_slot (started.worldTyped typed).1 (FreshRegion.private_slot started.1 slot)).1
  case disposeContinuation stored _ _ _ cleared => exact slot.write cleared (slot.stored_outside stored)
  case cancel found active _ _ => exact suspensions.restore_private slot found active.1

theorem EffectStep.private_control {program : Kernel.Program} {before after : State} {event : Option Event}
    {id owner savedScope loan : Identity} {root : Root} {inner outer : List Frame}
    {caller : Context} {address handle : Address} {authority : Authority} {next : Task}
    (step : EffectStep program before event after)
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world) (suspensions : before.SuspensionsWellFormed)
    (slot : before.world.PrivateSlot id root) (home : root.home = .temporary owner savedScope)
    (ownerBound : owner < before.nextActivation) (control : PrivateControl id owner inner before.task)
    (stack : before.frames = inner ++ .hook caller address authority handle loan next :: outer)
    (noOperation : ∀ operation arguments, event ≠ some (.perform operation arguments))
    (noReplay : ∀ key last, event ≠ some (.replay key last)) :
    ∃ remaining, after.frames = remaining ++ .hook caller address authority handle loan next :: outer ∧
      PrivateControl id owner remaining after.task := by
  have slotAfter := step.private_slot valid inventory typed suspensions slot control.2.2.1 noReplay
  obtain ⟨taskRoots,frameRoots,taskOwner,frameOwners⟩ := control
  cases step
  all_goals simp_all only [Task.rootSupport,Task.PrivateActivation,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,not_or]
  case operationCall => exact False.elim (noOperation _ _ rfl)
  case resumeLast | resumeCopy => exact False.elim (noReplay _ _ rfl)
  case install installed =>
    have environmentOutside := (installed.private_slot valid inventory typed slot).2
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,rfl⟩ := installed
    refine ⟨_ :: inner,rfl,?_⟩
    have fresh := (Nat.ne_of_lt ownerBound).symm
    simp_all [PrivateControl,Task.rootSupport,Frame.rootSupport,InstalledHandler.rootSupport,
      Task.PrivateActivation,PrivateFrames,Frame.PrivateActivation,InstalledHandler.activationSupport,
      Context.rootSupport,ne_comm]
  case continuationCall resolved _ _ _ argument =>
    obtain ⟨place,_,resolvedArgument⟩ := argument
    have outside := Context.resolves_avoids_root taskRoots slotAfter.safe resolvedArgument
    exact ⟨inner,rfl,⟨by simpa only [Task.rootSupport,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false,not_or] using And.intro taskRoots (Ne.symm outside),
      frameRoots,taskOwner,frameOwners⟩⟩
  case tailArmReturn =>
    cases inner with
    | nil => cases List.cons.inj stack |>.1
    | cons frame remaining =>
      obtain ⟨head,tail⟩ := List.cons.inj stack
      subst frame
      simp only [List.flatMap_cons,Frame.rootSupport,List.mem_append,not_or] at frameRoots
      refine ⟨remaining,tail,?_⟩
      simp_all [PrivateControl,Task.rootSupport,Task.PrivateActivation,PrivateFrames,Frame.PrivateActivation]
  case resumeReturns keptValue =>
    have keptOutside := (keptValue.private_slot typed.1 slot).2
    cases inner with
    | nil => cases List.cons.inj stack |>.1
    | cons frame remaining =>
      obtain ⟨head,tail⟩ := List.cons.inj stack
      subst frame
      refine ⟨remaining,tail,?_⟩
      simp_all [PrivateControl,Task.rootSupport,Task.PrivateActivation,PrivateFrames,
        Frame.PrivateActivation,Frame.rootSupport,ne_comm]
  case completionIdentity context value handler owns rest clause withRegion kept world roots task frames empty started keptValue selected _ =>
    cases inner with
    | nil => cases List.cons.inj stack |>.1
    | cons frame remaining =>
      obtain ⟨head,tail⟩ := List.cons.inj stack
      subst frame
      simp only [List.flatMap_cons,Frame.rootSupport,List.mem_append,not_or] at frameRoots
      have handlerOwners := frameOwners.1
      simp only [Frame.PrivateActivation,InstalledHandler.activationSupport,List.mem_cons,
        List.not_mem_nil,or_false,not_or] at handlerOwners
      have rootsOutside := selected.avoids_private slotAfter home (Ne.symm handlerOwners.2.1)
      have keptOutside := (keptValue.private_slot (started.worldTyped typed).1
        (FreshRegion.private_slot started.1 slot)).2
      have clauseFresh : clause.activation ≠ owner := by rw [started.2]; exact (Nat.ne_of_lt ownerBound).symm
      have clauseOutside : id ∉ clause.rootSupport := by
        rw [started.2]
        exact fun member => frameRoots.1 (List.mem_append_left _ (List.mem_append_left _ member))
      refine ⟨.completion handler owns clause :: remaining,by rw [tail]; rfl,?_⟩
      simp_all [PrivateControl,Task.rootSupport,Task.PrivateActivation,PrivateFrames,
        Frame.PrivateActivation,Frame.rootSupport,ne_comm]
  case completion context value handler owns rest clause withRegion kept world roots arm actions task frames started keptValue selected _ _ planned =>
    cases inner with
    | nil => cases List.cons.inj stack |>.1
    | cons frame remaining =>
      obtain ⟨head,tail⟩ := List.cons.inj stack
      subst frame
      simp only [List.flatMap_cons,Frame.rootSupport,List.mem_append,not_or] at frameRoots
      have handlerOwners := frameOwners.1
      simp only [Frame.PrivateActivation,InstalledHandler.activationSupport,List.mem_cons,
        List.not_mem_nil,or_false,not_or] at handlerOwners
      have rootsOutside := selected.avoids_private slotAfter home (Ne.symm handlerOwners.2.1)
      have keptOutside := (keptValue.private_slot (started.worldTyped typed).1
        (FreshRegion.private_slot started.1 slot)).2
      have actionsOutside := planned.avoids_root slotAfter.safe (Ne.symm keptOutside)
      have clauseFresh : clause.activation ≠ owner := by rw [started.2]; exact (Nat.ne_of_lt ownerBound).symm
      have clauseOutside : id ∉ clause.rootSupport := by
        rw [started.2]
        exact fun member => frameRoots.1 (List.mem_append_left _ (List.mem_append_left _ member))
      refine ⟨.completion handler owns clause :: remaining,by rw [tail]; rfl,?_⟩
      simp_all [PrivateControl,Task.rootSupport,Task.PrivateActivation,PrivateFrames,
        Frame.PrivateActivation,Frame.rootSupport,ne_comm]
  case completed _ keptValue selected _ | serviced _ keptValue selected _ =>
    cases inner with
    | nil => cases List.cons.inj stack |>.1
    | cons frame remaining =>
      obtain ⟨head,tail⟩ := List.cons.inj stack
      subst frame
      simp only [List.flatMap_cons,Frame.rootSupport,List.mem_append,not_or] at frameRoots
      have rootsOutside := selected.avoids_private slotAfter home frameOwners.1.1
      have keptOutside := (keptValue.private_slot typed.1 slot).2
      refine ⟨remaining,tail,?_⟩
      simp_all [PrivateControl,Task.rootSupport,Task.PrivateActivation,PrivateFrames,
        Frame.PrivateActivation,Frame.rootSupport,ne_comm]
  case finishedOwnedClause _ selected _ =>
    have handlerOwners := taskOwner
    simp only [InstalledHandler.activationSupport,List.mem_cons,List.not_mem_nil,or_false,not_or] at handlerOwners
    have rootsOutside := selected.avoids_private slotAfter home (Ne.symm handlerOwners.1)
    refine ⟨inner,rfl,?_⟩
    simp_all [PrivateControl,Task.rootSupport,Task.PrivateActivation,InstalledHandler.rootSupport,
      InstalledHandler.activationSupport,ne_comm]
  case finishedLentClause =>
    refine ⟨inner,rfl,?_⟩
    simp_all [PrivateControl,Task.rootSupport,Task.PrivateActivation,InstalledHandler.rootSupport,
      InstalledHandler.activationSupport,ne_comm]
  case disposeContinuation =>
    refine ⟨inner,rfl,?_⟩
    split <;> simp_all [PrivateControl,Task.rootSupport,Task.PrivateActivation]
  case cancel found active _ _ =>
    have rootsOutside := suspensions.private_excluded slot found active.1
    refine ⟨inner,rfl,?_⟩
    simp_all [PrivateControl,Task.rootSupport,Task.PrivateActivation,CloseRegions.root_support]

end Glorious.Language.Execution
