import GloriousLanguage.PrivatePrimitivePreservation
import GloriousLanguage.InvocationBoundary

/-! Actual handler storage and cancellation preserve a private caller slot.
An active suspension owns exactly its current suspended roots; its historical
restoration table cannot rehome a distinct private logical root. -/
namespace Glorious.Language.Execution

open _root_.Glorious.Language.Kernel

/-- First-handler routing has one delimiter position. The selected arm need
not be identified to show that the actual transition stays above a boundary. -/
theorem Routes.same_position {program : Kernel.Program} {state : State} {operation : DeclId}
    {arguments : List Term} {payload : List ResolvedPlace}
    {firstInner lastInner firstOuter lastOuter : List Frame} {firstHandler lastHandler : InstalledHandler}
    {firstOwns lastOwns : Bool} {firstArm lastArm : OperationArm}
    (first : Routes program state operation arguments payload firstInner firstHandler firstOwns firstArm firstOuter)
    (last : Routes program state operation arguments payload lastInner lastHandler lastOwns lastArm lastOuter) :
    firstInner = lastInner ∧ firstHandler = lastHandler ∧ firstOwns = lastOwns ∧ firstOuter = lastOuter := by
  have frames := first.1.symm.trans last.1
  rcases List.append_eq_append_iff.mp frames with ⟨middle,inner,outer⟩ | ⟨middle,inner,outer⟩
  · cases middle with
    | nil =>
        simp only [List.append_nil] at inner
        simp only [List.nil_append,List.cons.injEq,Frame.handler.injEq] at outer
        exact ⟨inner.symm,outer.1.1,outer.1.2,outer.2⟩
    | cons frame middle =>
        have head := (List.cons.inj outer).1
        subst frame
        have skipped := last.2.1 (.handler firstHandler firstOwns) (by rw [inner]; simp)
        exact False.elim (skipped.2 ⟨firstArm,first.2.2⟩)
  · cases middle with
    | nil =>
        simp only [List.append_nil] at inner
        simp only [List.nil_append,List.cons.injEq,Frame.handler.injEq] at outer
        exact ⟨inner,outer.1.1.symm,outer.1.2.symm,outer.2.symm⟩
    | cons frame middle =>
        have head := (List.cons.inj outer).1
        subst frame
        have skipped := first.2.1 (.handler lastHandler lastOwns) (by rw [inner]; simp)
        exact False.elim (skipped.2 ⟨lastArm,last.2.2⟩)

theorem Routes.internal_outer {program : Kernel.Program} {state : State} {operation : DeclId}
    {arguments : List Term} {payload : List ResolvedPlace} {inner outer : List Frame}
    {handler : InstalledHandler} {owns : Bool} {arm : OperationArm}
    {returnTo : Context} {ambient : List Frame}
    (route : Routes program state operation arguments payload inner handler owns arm outer)
    (internal : (Contracts.InvocationBoundary.caller returnTo ambient).InternalOperation
      program state operation arguments payload) : ∃ between, outer = between ++ ambient := by
  obtain ⟨_,_,_,_,between,selected⟩ := internal
  exact ⟨between,(route.same_position selected).2.2.2⟩

theorem DelimitedRoots.avoids_private {world : World} {handler : InstalledHandler} {frames : List Frame}
    {kept roots : List Identity} {id owner savedScope : Identity} {root : Root}
    (selected : DelimitedRoots world handler frames kept roots) (slot : world.PrivateSlot id root)
    (home : root.home = .temporary owner savedScope) (handlerPrivate : owner ∉ handler.activationSupport)
    (framesPrivate : ∀ frame ∈ frames, ∃ returning, frame.PrivateActivation owner returning) : id ∉ roots := by
  intro member
  obtain ⟨actual,found,_,_,captured⟩ := (selected.2 id).mp member
  have same := Option.some.inj (found.symm.trans slot.found)
  subst actual
  rw [home] at captured
  rcases captured with handlerOwns | ⟨frame,member,owns⟩
  · apply handlerPrivate
    simp_all [InstalledHandler.activationSupport,HomeOwnedByScope]
  · obtain ⟨returning,privateOwner⟩ := framesPrivate frame member
    exact privateOwner.not_owns_temporary owns

theorem Routes.delimited_avoids_private {program : Kernel.Program} {before : State} {operation : DeclId}
    {arguments : List Term} {payload : List ResolvedPlace} {captured rest inner ambient : List Frame}
    {handler : InstalledHandler} {owns : Bool} {arm : OperationArm} {returnTo : Context}
    {world : World} {kept roots : List Identity} {id owner savedScope : Identity} {root : Root}
    (route : Routes program before operation arguments payload captured handler owns arm rest)
    (stack : before.frames = inner ++ ambient)
    (internal : (Contracts.InvocationBoundary.caller returnTo ambient).InternalOperation
      program before operation arguments payload)
    (frames : PrivateFrames owner inner) (selected : DelimitedRoots world handler captured kept roots)
    (slot : world.PrivateSlot id root) (home : root.home = .temporary owner savedScope) : id ∉ roots := by
  obtain ⟨between,restShape⟩ := route.internal_outer internal
  have innerShape : inner = captured ++ .handler handler owns :: between := by
    apply List.append_cancel_right (bs := ambient)
    rw [← stack,route.1,restShape]
    simp only [List.append_assoc,List.cons_append]
  rw [innerShape] at frames
  exact selected.avoids_private slot home (PrivateFrames.append_right frames).1
    (fun frame member => frames.member (List.mem_append_left _ member))


theorem PayloadPlan.avoids_root {program : Language.Program} {world : World}
    {addresses : List Address} {patterns : List Pattern} {actions : PatternActions} {id : Identity}
    (planned : PayloadPlan program world addresses patterns actions) (safe : CanEndStorage world id)
    (outside : ∀ address ∈ addresses, address.root ≠ id) :
    id ∉ (ScheduledPattern actions).flatMap PatternAction.rootSupport := by
  induction planned with
  | nil => simp [ScheduledPattern]
  | cons first rest ih =>
      have firstOutside := first.avoids_root safe (Ne.symm (outside _ List.mem_cons_self))
      have restOutside := ih (fun address member => outside address (List.mem_cons_of_mem _ member))
      simp_all [ScheduledPattern,List.flatMap_append,List.mem_append]

theorem ProtectsAttemptFor.private_slot {program : Kernel.Program} {context : Context} {before after : World}
    {footprint destinations : List Address} {sources : List ResolvedPlace} {outcome : PreparationOutcome}
    {id : Identity} {root : Root}
    (kept : ProtectsAttemptFor program context footprint before sources destinations after outcome)
    (well : before.WellFormed) (slot : before.PrivateSlot id root) :
    after.PrivateSlot id root ∧ ∀ address ∈ destinations, address.root ≠ id := by
  induction kept with
  | nil | exhausted => exact ⟨slot,by simp⟩
  | cons _ first _ ih =>
    obtain ⟨middle,outside⟩ := first.private_slot well slot
    obtain ⟨finish,rest⟩ := ih (first.wellFormed well) middle
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
  obtain ⟨boundSlot,bindingsOutside⟩ := BindsInputsAttemptFor.private_slot boundValues
    (capturedValues.worldTyped valid inventory secondTyped).1 capturedSlot (by
      intro input member
      obtain ⟨⟨localSlot,address⟩,present,rfl⟩ := List.mem_map.mp member
      exact sourcesOutside address (List.of_mem_zip present).2)
  refine ⟨retired.private_slot boundSlot sourcesOutside,?_⟩
  intro member
  simp only [Context.rootSupport,List.flatMap_nil,List.append_nil] at member
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

theorem suspendRoots.private_slot {world : World} {roots : List Identity} {key id : Identity} {root : Root}
    (slot : world.PrivateSlot id root) (outside : id ∉ roots) :
    (suspendRoots world roots key).PrivateSlot id root := by
  apply slot.stable
  · simp only [suspendRoots.get,slot.found,Option.map_some,if_neg outside]
  · rfl
  · rfl

theorem CopiesSnapshot.private_slot {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation} {id : Identity} {root : Root}
    (copied : CopiesSnapshot program before suspension map after)
    (well : before.world.WellFormed) (slot : before.world.PrivateSlot id root) :
    after.world.PrivateSlot id root := by
  rw [copied.result]
  refine slot.retain (Relocation.old_root slot.found) ?_ slot.safe.2.1
  intro key loan found live
  rcases Relocation.loan_origin well.2.1 found with present | ⟨old,original,present,_,rfl,rfl⟩
  · exact slot.safe.1 key loan present live
  · have outside := slot.safe.1 old original present live
    change (map.address original.referent).root ≠ id
    by_cases included : original.referent.root ∈ map.roots
    · simp only [Relocation.address,Relocation.root,relocateId,if_pos included,copied.relocation.rootBase]
      exact (Nat.ne_of_lt (Nat.lt_of_lt_of_le (slot.bound well) (Nat.le_add_right _ _))).symm
    · simpa only [Relocation.address,Relocation.root,relocateId,if_neg included] using outside


theorem EffectStep.private_slot {program : Kernel.Program} {before after : State} {event : Option Event}
    {id owner savedScope loan : Identity} {root : Root} {inner outer : List Frame}
    {caller : Context} {address handle : Address} {authority : Authority} {next : Task}
    (step : EffectStep program before event after)
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world) (suspensions : before.SuspensionsWellFormed)
    (slot : before.world.PrivateSlot id root) (home : root.home = .temporary owner savedScope)
    (frames : PrivateFrames owner inner)
    (stack : before.frames = inner ++ .hook caller address authority handle loan next :: outer)
    (internalOperation : ∀ context operation arguments payload,
      before.task = .perform context operation arguments payload →
      (Contracts.InvocationBoundary.caller caller (.hook caller address authority handle loan next :: outer)).InternalOperation
        program before operation arguments payload)
    (noReplay : ∀ key last, event ≠ some (.replay key last))
    (noSuspend : ∀ key, event ≠ some (.suspend key)) : after.world.PrivateSlot id root := by
  cases step
  all_goals try exact slot
  case install installed => exact (installed.private_slot valid inventory typed slot).1
  case terminal _ _ _ _ started kept _ _ _ |
      terminalPayloadExhausted started kept | suspendTailPayloadExhausted started kept =>
    exact (ProtectsAttemptFor.private_slot kept (started.worldTyped typed).1
      (FreshRegion.private_slot started.1 slot)).1
  case suspendPayloadExhausted started kept =>
    obtain ⟨_,_,started,_,_,_⟩ := started
    exact (ProtectsAttemptFor.private_slot kept (started.worldTyped typed).1
      (FreshRegion.private_slot started.1 slot)).1
  case suspendContinuationExhausted route started kept selected _ _ _ =>
    obtain ⟨_,_,started,_,_,_⟩ := started
    have movedSlot := (ProtectsAttemptFor.private_slot kept (started.worldTyped typed).1
      (FreshRegion.private_slot started.1 slot)).1
    exact suspendRoots.private_slot movedSlot
      (route.delimited_avoids_private stack (internalOperation _ _ _ _ (by assumption)) frames selected movedSlot home)
  case suspend | suspendTailArm => exact False.elim (noSuspend _ rfl)
  case resumeLast | resumeCopy => exact False.elim (noReplay _ _ rfl)
  case resumeLastExhausted found active _ restored _ =>
    rw [restored]
    exact suspensions.restore_private slot found active.1
  case resumeCopyExhausted _ _ _ copied _ => exact copied.private_slot typed.1 slot
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
    (internalOperation : ∀ context operation arguments payload,
      before.task = .perform context operation arguments payload →
      (Contracts.InvocationBoundary.caller caller (.hook caller address authority handle loan next :: outer)).InternalOperation
        program before operation arguments payload)
    (noReplay : ∀ key last, event ≠ some (.replay key last))
    (noSuspend : ∀ key, event ≠ some (.suspend key)) :
    ∃ remaining, after.frames = remaining ++ .hook caller address authority handle loan next :: outer ∧
      PrivateControl id owner remaining after.task := by
  have slotAfter := step.private_slot valid inventory typed suspensions slot home control.2.2.2 stack internalOperation noReplay noSuspend
  obtain ⟨taskRoots,frameRoots,taskOwner,frameOwners⟩ := control
  cases step
  all_goals simp_all only [Task.rootSupport,Task.PrivateActivation,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,not_or]
  case terminalPayloadExhausted | suspendPayloadExhausted | suspendTailPayloadExhausted |
      suspendContinuationExhausted | resumeLastExhausted | resumeCopyBlocked =>
    exact ⟨inner,rfl,by simp [PrivateControl,Task.rootSupport,Task.PrivateActivation,frameRoots,frameOwners]⟩
  case resumeCopyExhausted _ _ _ copied _ =>
    rw [copied.result]
    exact ⟨inner,by simpa using stack,by simp [PrivateControl,Task.rootSupport,Task.PrivateActivation,frameRoots,frameOwners]⟩
  case operationCall _ _ _ _ _ _ _ resolved =>
    have payloadOutside := resolved.avoids_root (Context.bindings_avoid_root taskRoots) slotAfter.safe
    refine ⟨inner,rfl,?_,frameRoots,taskOwner,frameOwners⟩
    simpa only [Task.rootSupport,List.mem_append,not_or] using And.intro taskRoots payloadOutside
  case suspend | suspendTailArm => exact False.elim (noSuspend _ rfl)
  case resumeLast | resumeCopy => exact False.elim (noReplay _ _ rfl)
  case terminal context operation arguments payload abandoned handler owns arm rest declaration signature
      clause withRegion kept moved roots actions _task _ _ _ route started keptPayload selected _ planned =>
    obtain ⟨between,restShape⟩ := route.internal_outer (internalOperation context operation arguments payload rfl)
    have innerShape : inner = abandoned ++ .handler handler owns :: between := by
      apply List.append_cancel_right (bs := .hook caller address authority handle loan next :: outer)
      rw [← stack,route.1,restShape]
      simp only [List.append_assoc,List.cons_append]
    rw [innerShape] at frameRoots frameOwners
    have suffixOwners := PrivateFrames.append_right frameOwners
    have handlerPrivate : owner ∉ handler.activationSupport := suffixOwners.1
    have rootsOutside := selected.avoids_private slotAfter home handlerPrivate
      (fun frame member => frameOwners.member (List.mem_append_left _ member))
    have keptOutside := (ProtectsAttemptFor.private_slot keptPayload (started.worldTyped typed).1
      (FreshRegion.private_slot started.1 slot)).2
    have actionsOutside := planned.avoids_root slotAfter.safe keptOutside
    simp only [List.flatMap_append,List.flatMap_cons,Frame.rootSupport,List.mem_append,not_or] at frameRoots
    have clauseOutside : id ∉ clause.rootSupport := by
      rw [started.2]
      exact fun member => frameRoots.2.1 (List.mem_append_left _ (List.mem_append_left _ member))
    have clauseFresh : clause.activation ≠ owner := by
      rw [started.2]
      exact (Nat.ne_of_lt ownerBound).symm
    refine ⟨.serviced handler owns clause none :: between,by rw [restShape]; rfl,?_⟩
    simp_all [PrivateControl,Task.rootSupport,CloseRegions.root_support,Task.PrivateActivation,
      CloseRegions.private_activation,PrivateFrames,Frame.PrivateActivation,Frame.rootSupport]
  case install installed =>
    have environmentOutside := (installed.private_slot valid inventory typed slot).2
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,rfl⟩ := installed
    refine ⟨_ :: inner,rfl,?_⟩
    have fresh := (Nat.ne_of_lt ownerBound).symm
    simp_all [PrivateControl,Task.rootSupport,Frame.rootSupport,InstalledHandler.rootSupport,
      Task.PrivateActivation,PrivateFrames,Frame.PrivateActivation,InstalledHandler.activationSupport,
      Context.rootSupport,ne_comm]
    exact taskRoots.2
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
