import GloriousLanguage.PrivateControl

/-! The actual local machine preserves a hidden caller handle until it pops
that handle's hook guard. The frame prefix, including its cleanup owners and
pending continuations, is derived from the real transition. -/
namespace Glorious.Language.Execution

open _root_.Glorious.Language.Kernel

theorem TailFrames.private_prefix {frames finish inner outer : List Frame}
    {activeOwner owner id regionLoan : Identity} {outerContext guardContext : Context}
    {regions : List Identity} {address handle : Address} {authority : Authority} {next : Task}
    (route : TailFrames frames activeOwner outerContext regions finish)
    (stack : frames = inner ++ .hook guardContext address authority handle regionLoan next :: outer)
    (roots : id ∉ inner.flatMap Frame.rootSupport) (owners : PrivateFrames owner inner) :
    ∃ remaining, finish = remaining ++ .hook guardContext address authority handle regionLoan next :: outer ∧
      id ∉ outerContext.rootSupport ∧ id ∉ remaining.flatMap Frame.rootSupport ∧
      (remaining.isEmpty = true ∨ outerContext.activation ≠ owner) ∧ PrivateFrames owner remaining := by
  induction route generalizing inner with
  | activation =>
    cases inner with
    | nil => cases List.cons.inj stack |>.1
    | cons frame inner =>
      obtain ⟨head,tail⟩ := List.cons.inj stack
      subst frame
      simp only [List.flatMap_cons,Frame.rootSupport,List.mem_append,not_or] at roots
      exact ⟨inner,tail,roots.1,roots.2,owners.1.2,owners.2⟩
  | scope _ ih | label _ ih =>
    cases inner with
    | nil => cases List.cons.inj stack |>.1
    | cons frame inner =>
      obtain ⟨head,tail⟩ := List.cons.inj stack
      subst frame
      exact ih tail (fun member => roots (List.mem_append_right _ member)) owners.2

theorem PrivateFrames.fresh_named {function : Function} {context : Context} {brand region owner : Identity}
    {rest : List Frame} (fresh : context.activation ≠ owner) (continued : PrivateFrames owner rest) :
    PrivateFrames owner (FreshNamedFrame function context brand region ++ rest) := by
  unfold FreshNamedFrame
  split
  · exact continued
  · exact ⟨fresh,continued⟩

theorem FreshNamedFrame.avoids_root {function : Function} {context : Context} {brand region id : Identity}
    (outside : id ∉ context.rootSupport) :
    id ∉ (FreshNamedFrame function context brand region).flatMap Frame.rootSupport := by
  unfold FreshNamedFrame
  split
  · simp
  · simpa only [List.flatMap_cons,List.flatMap_nil,List.append_nil,Frame.rootSupport] using outside

/-- The sole exceptional outcome is the actual pop of the saved hook guard.
Its pre-state still contains the exact private slot. No future frame or
post-world privacy certificate is assumed. -/
theorem LocalStep.private_control {program : Kernel.Program} {before after : State} {event : Option Event}
    {id owner savedScope loan : Identity} {root : Root} {inner outer : List Frame}
    {caller : Context} {address handle : Address} {authority : Authority} {next : Task}
    (step : LocalStep program before event after) (well : before.world.WellFormed)
    (slot : before.world.PrivateSlot id root) (home : root.home = .temporary owner savedScope)
    (ownerBound : owner < before.nextActivation) (control : PrivateControl id owner inner before.task)
    (stack : before.frames = inner ++ .hook caller address authority handle loan next :: outer) :
    (∃ remaining, after.frames = remaining ++ .hook caller address authority handle loan next :: outer ∧
      PrivateControl id owner remaining after.task) ∨
    (event = none ∧ inner = [] ∧ after.frames = outer) := by
  have slotAfter := step.private_slot well slot control.1
    (fun context destination body rest frames => control.binding_outside (stack.symm.trans frames))
  obtain ⟨taskRoots,frameRoots,taskOwner,frameOwners⟩ := control
  cases step
  all_goals simp_all only [Task.rootSupport,Task.PrivateActivation,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,not_or,true_and]
  all_goals try (solve |
    apply Or.inl
    refine ⟨inner,rfl,?_⟩
    simp_all [PrivateControl,Task.rootSupport,Task.PrivateActivation,PatternAction.rootSupport,Address.child])

  case evaluate allocated | invoke allocated =>
    have outside := allocated.fresh_avoids (slot.bound well)
    refine Or.inl ⟨_ :: inner,rfl,?_⟩
    have contextOutside (localSlot : Local) (permission : Authority) :=
      Context.bind_avoids_root (localSlot := localSlot) (authority := permission) taskRoots outside
    simp_all [PrivateControl,Task.rootSupport,Frame.rootSupport,PrivateFrames,Frame.PrivateActivation,
      Task.PrivateActivation,Context.bind,ne_comm]
  case bind allocated =>
    have outside := allocated.fresh_avoids (slot.bound well)
    refine Or.inl ⟨inner,rfl,?_,frameRoots,taskOwner,frameOwners⟩
    exact fun member => (List.mem_append.mp member).elim (Context.bind_avoids_root taskRoots outside)
      (by simpa using Ne.symm outside)
  case result kept =>
    refine Or.inl ⟨inner,rfl,?_,frameRoots,Or.inr taskOwner,frameOwners⟩
    exact fun member => (List.mem_append.mp member).elim taskRoots
      (by simpa using Ne.symm (kept.private_slot well slot).2)
  case discard resolved | endLoan resolved _ _ =>
    have outside := Context.resolves_avoids_root taskRoots slotAfter.safe resolved
    refine Or.inl ⟨inner,rfl,?_⟩
    simp_all [PrivateControl,Task.rootSupport,Task.PrivateActivation,ne_comm]
  case assign target source _ _ =>
    have targetOutside := Context.resolves_avoids_root taskRoots slotAfter.safe target
    have sourceOutside := Context.resolves_avoids_root taskRoots slotAfter.safe source
    refine Or.inl ⟨inner,rfl,?_⟩
    simp_all [PrivateControl,Task.rootSupport,Task.PrivateActivation,ne_comm]
  case call resolved _ _ _ _ inputs resources =>
    have receiverOutside := Context.resolves_avoids_root taskRoots slotAfter.safe resolved
    have argumentsOutside := inputs.avoids_root taskRoots slotAfter.safe
    have resourcesOutside := resources.avoids_root (Context.bindings_avoid_root taskRoots) slotAfter.safe
    refine Or.inl ⟨inner,rfl,?_⟩
    simp_all [PrivateControl,Task.rootSupport,EntrySource.rootSupport,Task.PrivateActivation,
      List.mem_flatMap,InvocationInput.rootSupport,ne_comm]
  case choose resolved _ planned =>
    have sourceOutside := Context.resolves_avoids_root taskRoots slotAfter.safe resolved
    exact Or.inl ⟨inner,rfl,⟨fun member => (List.mem_append.mp member).elim taskRoots
      (planned.avoids_root slotAfter.safe (Ne.symm sourceOutside)),frameRoots,taskOwner,frameOwners⟩⟩
  case patternBind bound =>
    have contextOutside (localSlot : Local) (permission : Authority) :=
      Context.bind_avoids_root (localSlot := localSlot) (authority := permission) taskRoots.1 (bound.private_slot well slot).2
    refine Or.inl ⟨inner,rfl,?_⟩
    simp_all [PrivateControl,Task.rootSupport,Task.PrivateActivation,PatternAction.rootSupport,Context.bind]
  case scope fresh definition | label _ definition =>
    refine Or.inl ⟨_ :: inner,rfl,?_⟩
    simp_all [PrivateControl,Task.rootSupport,Frame.rootSupport,PrivateFrames,Frame.PrivateActivation,
      Task.PrivateActivation,Context.bindRegion,Context.bindBrand,Context.rootSupport]
    exact taskRoots.2
  case unsafeAllowed =>
    refine Or.inl ⟨inner,rfl,?_⟩
    simpa only [PrivateControl,Task.rootSupport,Task.PrivateActivation,Context.rootSupport] using
      And.intro taskRoots (And.intro frameRoots (And.intro taskOwner frameOwners))

  case bindReturn moved returned =>
    cases inner with
    | nil => cases List.cons.inj stack |>.1
    | cons frame remaining =>
      obtain ⟨head,tail⟩ := List.cons.inj stack
      subst frame
      simp only [List.flatMap_cons,Frame.rootSupport,List.mem_append,List.mem_cons,
        List.not_mem_nil,or_false,not_or] at frameRoots
      have returnedOutside := returned.private_context (moved.wellFormed well)
        (moved.private_slot slot (Ne.symm frameRoots.1.2)) taskRoots.1 frameRoots.1.1
      refine Or.inl ⟨remaining,tail,?_,frameRoots.2,?_,frameOwners.2⟩
      · simpa only [Task.rootSupport,ReleaseCustodyLoans.root_support,List.mem_append,List.mem_cons,not_or] using
          And.intro taskRoots.2 returnedOutside
      · simp only [ReleaseCustodyLoans.private_activation,Task.PrivateActivation,returned.activation]
        exact frameOwners.1
  case labelReturn returned =>
    cases inner with
    | nil => cases List.cons.inj stack |>.1
    | cons frame remaining =>
      obtain ⟨head,tail⟩ := List.cons.inj stack
      subst frame
      simp only [List.flatMap_cons,Frame.rootSupport,List.mem_append,not_or] at frameRoots
      have returnedOutside := returned.private_context well slot taskRoots.1 frameRoots.1
      refine Or.inl ⟨remaining,tail,?_,frameRoots.2,?_,frameOwners.2⟩
      · simpa only [Task.rootSupport,ReleaseCustodyLoans.root_support,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,not_or] using And.intro returnedOutside taskRoots.2
      · simp only [ReleaseCustodyLoans.private_activation,Task.PrivateActivation,returned.activation]
        exact Or.inr frameOwners.1

  case enter callContext function source context world task entered =>
    have fresh : context.activation ≠ owner := by rw [entered.fresh_context.1]; exact (Nat.ne_of_lt ownerBound).symm
    have contextOutside := (EnterWorldAttempt.private_slot entered well slot taskRoots.2).2
    have namedOutside := FreshNamedFrame.avoids_root (function := function) (brand := before.nextBrand)
      (region := context.region) contextOutside
    refine Or.inl ⟨FreshNamedFrame function context before.nextBrand context.region ++
      .activation callContext context.activation context.region :: inner,by simp only [List.append_assoc,List.cons_append],
      contextOutside,?_,fresh,?_⟩
    · simpa only [List.flatMap_append,List.flatMap_cons,Frame.rootSupport,List.mem_append,not_or] using
        And.intro namedOutside (And.intro taskRoots.1 frameRoots)
    · exact PrivateFrames.fresh_named fresh ⟨⟨fresh,Or.inr taskOwner⟩,frameOwners⟩
  case enterTail callContext function source context enteredWorld world boundCaller regions rest roots task entered relinquished route selected _ _ =>
    have fresh : context.activation ≠ owner := by rw [entered.fresh_context.1]; exact (Nat.ne_of_lt ownerBound).symm
    let tailContext : Context := { context with resourceContracts := context.resourceContracts ++ callContext.resourceContracts }
    have contextOutside : id ∉ tailContext.rootSupport := by
      have newParts := (EnterWorldAttempt.private_slot entered well slot taskRoots.2).2
      have oldParts := taskRoots.1
      simp only [tailContext,Context.rootSupport,List.flatMap_append,List.mem_append,not_or] at newParts oldParts ⊢
      exact ⟨newParts.1,newParts.2,oldParts.2⟩
    have namedOutside := FreshNamedFrame.avoids_root (function := function) (brand := before.nextBrand)
      (region := context.region) contextOutside
    obtain ⟨remaining,tail,callerOutside,remainingOutside,callerOwner,remainingOwners⟩ :=
      route.private_prefix rfl frameRoots frameOwners
    have rootsOutside := selected.avoids_private slotAfter home taskOwner
    refine Or.inl ⟨FreshNamedFrame function tailContext before.nextBrand context.region ++
      .activation boundCaller context.activation context.region :: remaining,
      by simp only [tail,tailContext,List.append_assoc,List.cons_append],?_,?_,?_,?_⟩
    · simpa only [Task.rootSupport,ReleaseCustodyLoans.root_support,CloseRegions.root_support,List.mem_append,not_or,and_assoc] using
        And.intro taskRoots.1 (And.intro rootsOutside contextOutside)
    · simpa only [List.flatMap_append,List.flatMap_cons,Frame.rootSupport,List.mem_append,not_or] using
        And.intro namedOutside (And.intro callerOutside remainingOutside)
    · simpa only [Task.PrivateActivation,ReleaseCustodyLoans.private_activation,CloseRegions.private_activation] using And.intro taskOwner fresh
    · exact PrivateFrames.fresh_named fresh ⟨⟨fresh,callerOwner⟩,remainingOwners⟩
  case activationReturn active keptValue returned selected _ =>
    cases inner with
    | nil => cases List.cons.inj stack |>.1
    | cons frame remaining =>
      obtain ⟨head,tail⟩ := List.cons.inj stack
      subst frame
      simp only [List.flatMap_cons,Frame.rootSupport,List.mem_append,not_or] at frameRoots
      have rootsOutside := selected.avoids_private slotAfter home frameOwners.1.1
      have keptPrivate := keptValue.private_slot well slot
      have returnedOutside := returned.private_context (keptValue.wellFormed well) keptPrivate.1 taskRoots.1 frameRoots.1
      refine Or.inl ⟨remaining,tail,?_,frameRoots.2,?_,frameOwners.2⟩
      · simpa only [Task.rootSupport,ReleaseCustodyLoans.root_support,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,not_or,and_assoc] using
          And.intro taskRoots.1 (And.intro rootsOutside (And.intro returnedOutside (Ne.symm keptPrivate.2)))
      · simp only [ReleaseCustodyLoans.private_activation,Task.PrivateActivation]
        refine ⟨?_,?_⟩
        · rw [active]
          exact frameOwners.1.1
        · rw [returned.activation]
          exact frameOwners.1.2
  case scopeReturn keptValue returned selected _ =>
    cases inner with
    | nil => cases List.cons.inj stack |>.1
    | cons frame remaining =>
      obtain ⟨head,tail⟩ := List.cons.inj stack
      subst frame
      simp only [List.flatMap_cons,Frame.rootSupport,List.mem_append,not_or] at frameRoots
      have rootsOutside := selected.avoids_private slotAfter home frameOwners.1
      have keptPrivate := keptValue.private_slot well slot
      have returnedOutside := returned.private_context (keptValue.wellFormed well) keptPrivate.1 taskRoots.1 frameRoots.1
      refine Or.inl ⟨remaining,tail,?_,frameRoots.2,?_,frameOwners.2⟩
      · simpa only [Task.rootSupport,ReleaseCustodyLoans.root_support,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,not_or,and_assoc] using
          And.intro taskRoots.1 (And.intro rootsOutside (And.intro returnedOutside (Ne.symm keptPrivate.2)))
      · simp only [ReleaseCustodyLoans.private_activation,Task.PrivateActivation]
        refine ⟨?_,?_⟩
        · simpa only [List.isEmpty_cons,Bool.false_eq_true,false_or] using taskOwner
        · rw [returned.activation]
          exact Or.inr frameOwners.1
  case destroyHook temporary borrowed _ =>
    have outside := temporary.choose_spec.fresh_avoids (slot.bound well)
    refine Or.inl ⟨_ :: inner,rfl,?_⟩
    simp_all [PrivateControl,Task.rootSupport,EntrySource.rootSupport,InvocationInput.rootSupport,Frame.rootSupport,
      Task.PrivateActivation,PrivateFrames,Frame.PrivateActivation,Context.rootSupport,ne_comm]
    exact taskRoots.1.2
  case hookReturned context result boundCaller target permission savedHandle savedLoan continued rest receiver task frames stored =>
    cases inner with
    | nil => exact Or.inr ⟨rfl,(List.cons.inj stack).2⟩
    | cons frame remaining =>
      obtain ⟨head,tail⟩ := List.cons.inj stack
      subst frame
      refine Or.inl ⟨remaining,tail,?_⟩
      simp_all [PrivateControl,Task.rootSupport,Frame.rootSupport,Task.PrivateActivation,
        PrivateFrames,Frame.PrivateActivation]
  case shellDone | releaseStorageReturned | releaseRoot | releaseChild =>
    refine Or.inl ⟨inner,rfl,?_⟩
    simp_all [PrivateControl,ReleaseLoans.root_support,ReleaseCustodyLoans.root_support]

end Glorious.Language.Execution
