import GloriousLanguage.PrivateControl

/-! The actual local machine preserves a hidden caller handle until it pops
that handle's hook guard. The frame prefix, including its cleanup owners and
pending continuations, is derived from the real transition. -/
namespace Glorious.Language.Execution

open Kernel

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
  case call resolved _ _ _ _ inputs _ =>
    have receiverOutside := Context.resolves_avoids_root taskRoots slot.safe resolved
    have argumentsOutside := inputs.avoids_root taskRoots slot.safe
    refine Or.inl ⟨inner,rfl,?_⟩
    simp_all [PrivateControl,Task.rootSupport,EntrySource.rootSupport,Task.PrivateActivation,ne_comm]
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
  case unsafeAllowed =>
    refine Or.inl ⟨inner,rfl,?_⟩
    simpa only [PrivateControl,Task.rootSupport,Task.PrivateActivation,Context.rootSupport] using
      And.intro taskRoots (And.intro frameRoots (And.intro taskOwner frameOwners))

  case bindReturn context value boundCaller destination body rest after task frames moved =>
    cases inner with
    | nil => cases List.cons.inj stack |>.1
    | cons frame remaining =>
      obtain ⟨head,tail⟩ := List.cons.inj stack
      subst frame
      simp only [List.flatMap_cons,Frame.rootSupport,List.mem_append,List.mem_cons,
        List.not_mem_nil,or_false,not_or] at frameRoots
      refine Or.inl ⟨remaining,tail,?_,frameRoots.2,frameOwners.1,frameOwners.2⟩
      simpa only [Task.rootSupport,List.mem_append,List.mem_cons,not_or] using
        And.intro taskRoots.2 frameRoots.1.1
  case labelReturn context value boundCaller brand region result rest task frames =>
    cases inner with
    | nil => cases List.cons.inj stack |>.1
    | cons frame remaining =>
      obtain ⟨head,tail⟩ := List.cons.inj stack
      subst frame
      simp only [List.flatMap_cons,Frame.rootSupport,List.mem_append,not_or] at frameRoots
      refine Or.inl ⟨remaining,tail,?_,frameRoots.2,Or.inr frameOwners.1,frameOwners.2⟩
      simpa only [Task.rootSupport,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] using
        And.intro frameRoots.1 taskRoots.2

  case enter callContext function source context world task entered =>
    have fresh : context.activation ≠ owner := by rw [entered.activation]; exact (Nat.ne_of_lt ownerBound).symm
    have contextOutside := (entered.private_slot well slot).2
    have namedOutside := FreshNamedFrame.avoids_root (function := function) (brand := before.nextBrand)
      (region := context.region) contextOutside
    refine Or.inl ⟨FreshNamedFrame function context before.nextBrand context.region ++
      .activation callContext context.activation context.region :: inner,by simp only [List.append_assoc,List.cons_append],
      contextOutside,?_,fresh,?_⟩
    · simpa only [List.flatMap_append,List.flatMap_cons,Frame.rootSupport,List.mem_append,not_or] using
        And.intro namedOutside (And.intro taskRoots.1 frameRoots)
    · exact PrivateFrames.fresh_named fresh ⟨⟨fresh,Or.inr taskOwner⟩,frameOwners⟩
  case enterTail callContext function source context world boundCaller regions rest roots task entered route selected _ _ =>
    have fresh : context.activation ≠ owner := by rw [entered.activation]; exact (Nat.ne_of_lt ownerBound).symm
    have contextOutside := (entered.private_slot well slot).2
    have namedOutside := FreshNamedFrame.avoids_root (function := function) (brand := before.nextBrand)
      (region := context.region) contextOutside
    obtain ⟨remaining,tail,callerOutside,remainingOutside,callerOwner,remainingOwners⟩ :=
      route.private_prefix rfl frameRoots frameOwners
    have rootsOutside := selected.avoids_private slotAfter home taskOwner
    refine Or.inl ⟨FreshNamedFrame function context before.nextBrand context.region ++
      .activation boundCaller context.activation context.region :: remaining,
      by simp only [tail,List.append_assoc,List.cons_append],?_,?_,?_,?_⟩
    · simpa only [Task.rootSupport,CloseRegions.root_support,List.mem_append,not_or,and_assoc] using
        And.intro taskRoots.1 (And.intro rootsOutside contextOutside)
    · simpa only [List.flatMap_append,List.flatMap_cons,Frame.rootSupport,List.mem_append,not_or] using
        And.intro namedOutside (And.intro callerOutside remainingOutside)
    · simpa only [Task.PrivateActivation,CloseRegions.private_activation] using And.intro taskOwner fresh
    · exact PrivateFrames.fresh_named fresh ⟨⟨fresh,callerOwner⟩,remainingOwners⟩
  case activationReturn context value boundCaller activeOwner region rest kept world roots task frames active keptValue selected _ =>
    cases inner with
    | nil => cases List.cons.inj stack |>.1
    | cons frame remaining =>
      obtain ⟨head,tail⟩ := List.cons.inj stack
      subst frame
      simp only [List.flatMap_cons,Frame.rootSupport,List.mem_append,not_or] at frameRoots
      have rootsOutside := selected.avoids_private slotAfter home frameOwners.1.1
      have resultOutside := (keptValue.private_slot well slot).2
      have contextAway : context.activation ≠ owner := by rw [active]; exact frameOwners.1.1
      refine Or.inl ⟨remaining,tail,?_,frameRoots.2,⟨contextAway,frameOwners.1.2⟩,frameOwners.2⟩
      simpa only [Task.rootSupport,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or,and_assoc] using
        And.intro taskRoots.1 (And.intro rootsOutside (And.intro frameRoots.1 (Ne.symm resultOutside)))
  case scopeReturn context value boundCaller scope region rest kept world roots task frames keptValue selected _ =>
    cases inner with
    | nil => cases List.cons.inj stack |>.1
    | cons frame remaining =>
      obtain ⟨head,tail⟩ := List.cons.inj stack
      subst frame
      simp only [List.flatMap_cons,Frame.rootSupport,List.mem_append,not_or] at frameRoots
      have rootsOutside := selected.avoids_private slotAfter home frameOwners.1
      have resultOutside := (keptValue.private_slot well slot).2
      have contextAway : context.activation ≠ owner := by simpa only [List.isEmpty_cons,Bool.false_eq_true,false_or] using taskOwner
      refine Or.inl ⟨remaining,tail,?_,frameRoots.2,⟨contextAway,Or.inr frameOwners.1⟩,frameOwners.2⟩
      simpa only [Task.rootSupport,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or,and_assoc] using
        And.intro taskRoots.1 (And.intro rootsOutside (And.intro frameRoots.1 (Ne.symm resultOutside)))
  case destroyHook temporary borrowed _ =>
    have outside := temporary.choose_spec.fresh_avoids (slot.bound well)
    refine Or.inl ⟨_ :: inner,rfl,?_⟩
    simp_all [PrivateControl,Task.rootSupport,EntrySource.rootSupport,InvocationInput.rootSupport,Frame.rootSupport,
      Task.PrivateActivation,PrivateFrames,Frame.PrivateActivation,Context.rootSupport,ne_comm]
  case hookReturned context result boundCaller target permission savedHandle savedLoan continued rest receiver task frames stored =>
    cases inner with
    | nil => exact Or.inr ⟨rfl,(List.cons.inj stack).2⟩
    | cons frame remaining =>
      obtain ⟨head,tail⟩ := List.cons.inj stack
      subst frame
      refine Or.inl ⟨remaining,tail,?_⟩
      simp_all [PrivateControl,Task.rootSupport,Frame.rootSupport,Task.PrivateActivation,
        PrivateFrames,Frame.PrivateActivation]

end Glorious.Language.Execution
