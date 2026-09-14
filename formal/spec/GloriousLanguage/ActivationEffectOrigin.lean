import GloriousLanguage.ActivationSnapshotOrigin

/-! Handler installation, fresh clauses and both forms of replay preserve
one activation frontier. Saved homes obtain their bounds from the actual
captured ownership roles, never an assumed well-formed replay result. -/
namespace Glorious.Language.Execution

open _root_.Glorious.Language.Kernel

theorem RetiresEmpty.activationsBelow {before after : World} {addresses : List Address} {limit : Identity}
    (retired : RetiresEmpty before addresses after) (bounded : before.ActivationsBelow limit) :
    after.ActivationsBelow limit := by
  induction retired with
  | nil => exact bounded
  | cons _ first _ ih => exact ih (first.activationsBelow bounded)

theorem StartsClause.activation {before : State} {handler : InstalledHandler} {context : Context} {after : World}
    (started : StartsClause before handler context after) : context.activation = before.nextActivation := by
  rw [started.2]

theorem StartsClause.activation_lt {before : State} {handler : InstalledHandler} {context : Context} {after : World}
    (started : StartsClause before handler context after) : context.activation < before.nextActivation+1 := by
  rw [started.activation]
  exact Nat.lt_succ_self _

theorem StartsResumptionClause.activation {before : State} {handler : InstalledHandler} {lexical localSlot : Local}
    {context : Context} {after : World} (started : StartsResumptionClause before handler lexical context localSlot after) :
    context.activation = before.nextActivation := by
  obtain ⟨_,_,started,_,rfl,_⟩ := started
  exact started.activation

theorem StartsResumptionClause.activation_lt {before : State} {handler : InstalledHandler} {lexical localSlot : Local}
    {context : Context} {after : World} (started : StartsResumptionClause before handler lexical context localSlot after) :
    context.activation < before.nextActivation+1 := by
  rw [started.activation]
  exact Nat.lt_succ_self _

theorem StartsClause.activationsBelow {before : State} {handler : InstalledHandler} {context : Context}
    {after : World} {limit : Identity} (started : StartsClause before handler context after)
    (bounded : before.world.ActivationsBelow limit) : after.ActivationsBelow limit :=
  started.1.activationsBelow bounded

theorem StartsResumptionClause.activationsBelow {before : State} {handler : InstalledHandler} {lexical localSlot : Local}
    {context : Context} {after : World} {limit : Identity}
    (started : StartsResumptionClause before handler lexical context localSlot after)
    (bounded : before.world.ActivationsBelow limit) : after.ActivationsBelow limit := by
  obtain ⟨_,_,started,_⟩ := started
  exact started.activationsBelow bounded

theorem Installs.activation_support {program : Kernel.Program} {before : State} {outer : Context}
    {syntaxNode : Handler} {handler : InstalledHandler} {after : World}
    (installed : Installs program before outer syntaxNode handler after)
    (bounded : outer.activation < before.nextActivation) :
    RootSupport.Below handler.activationSupport (before.nextActivation+1) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,rfl⟩ := installed
  simp only [InstalledHandler.activationSupport,RootSupport.below_cons,RootSupport.below_nil,and_true]
  exact ⟨Nat.lt_succ_self _,Nat.lt_succ_of_lt bounded,Nat.lt_succ_of_lt bounded⟩

theorem Installs.homes_activationsBelow {program : Kernel.Program} {before : State} {outer : Context}
    {syntaxNode : Handler} {handler : InstalledHandler} {after : World}
    (installed : Installs program before outer syntaxNode handler after)
    (bounded : before.world.ActivationsBelow before.nextActivation) (owner : outer.activation < before.nextActivation) :
    after.ActivationsBelow (before.nextActivation+1) := by
  obtain ⟨_,_,_,_,_,_,_,_,first,second,_,captured,bound,retired,rfl,_⟩ := installed
  exact retired.activationsBelow (bound.activationsBelow
    (captured.activationsBelow (second.activationsBelow (first.activationsBelow (bounded.mono (Nat.le_succ _))))
      (Nat.lt_succ_of_lt owner)) (Nat.lt_succ_self _))

theorem CreatesContinuation.activationsBelow {program : Kernel.Program} {context : Context} {before after : World}
    {id signature answer effects quantity localSlot address} {limit : Identity}
    (created : CreatesContinuation program context before id signature answer effects quantity localSlot address after)
    (bounded : before.ActivationsBelow limit) (owner : context.activation < limit) : after.ActivationsBelow limit := by
  obtain ⟨_,_,_,allocated,created⟩ := created
  exact created.activationsBelow (allocated.activationsBelow bounded (by simpa using owner))

theorem EffectStep.activation_frontier {program : Kernel.Program} {before after : State} {event : Option Event}
    (step : EffectStep program before event after) : before.nextActivation ≤ after.nextActivation := by
  cases step <;> try first | exact Nat.le_succ _ | exact Nat.le_refl _
  case resumeCopy copied _ | resumeCopyExhausted copied _ => exact copied.activation_frontier

theorem EffectStep.activation_support {program : Kernel.Program} {before after : State} {event : Option Event}
    (valid : before.ActivationsWellFormed) (step : EffectStep program before event after) :
    RootSupport.Below after.task.activationSupport after.nextActivation ∧
      RootSupport.Below (after.frames.flatMap Frame.activationSupport) after.nextActivation := by
  have frontier := step.activation_frontier
  have taskBound := valid.task
  have taskAfter := taskBound.mono frontier
  have frameBound := valid.frames
  have framesAfter := frameBound.mono frontier
  cases step
  all_goals simp_all only [Task.activationSupport,Frame.activationSupport,List.flatMap_cons,List.flatMap_append,
    List.flatMap_nil,RootSupport.below_append,RootSupport.below_cons,RootSupport.below_nil,
    true_and,and_true,CloseRegions.activation_support,Context.bind]
  case install installed =>
    have handlerBound := installed.activation_support taskBound
    have parts := handlerBound
    simp only [InstalledHandler.activationSupport,RootSupport.below_cons,RootSupport.below_nil,and_true] at parts
    exact ⟨parts.2.1,handlerBound⟩
  case terminal route started _ _ _ _ =>
    obtain ⟨_,handlerBound,outerBound⟩ := route.activation_support framesAfter
    exact ⟨started.activation_lt,⟨started.activation_lt,handlerBound⟩,outerBound⟩
  case suspend route started _ _ _ _ _ _ _ =>
    obtain ⟨_,handlerBound,outerBound⟩ := route.activation_support framesAfter
    exact ⟨started.activation_lt,⟨started.activation_lt,handlerBound⟩,outerBound⟩
  case suspendTailArm route started _ _ _ _ _ _ =>
    obtain ⟨_,handlerBound,outerBound⟩ := route.activation_support framesAfter
    exact ⟨started.activation_lt,started.activation_lt,⟨started.activation_lt,handlerBound⟩,outerBound⟩
  case resumeLast found _ _ _ _ =>
    have saved := valid.saved _ _ found
    simp only [Suspension.controlActivationSupport,RootSupport.below_cons,RootSupport.below_append] at saved
    exact ⟨saved.1.1,saved.2,saved.1.2⟩
  case resumeCopy found _ _ copied _ =>
    obtain ⟨contextBound,handlerBound,savedBound⟩ := copied.activation_support (valid.saved _ _ found)
    exact ⟨contextBound,savedBound,handlerBound⟩
  case resumeCopyExhausted copied _ => simpa only [copied.result] using framesAfter
  case completionIdentity started _ _ _ | completion started _ _ _ _ _ =>
    exact ⟨started.activation_lt,started.activation_lt⟩
  case finishedOwnedClause =>
    simp only [InstalledHandler.activationSupport,RootSupport.below_cons,RootSupport.below_nil,and_true] at taskBound
    exact ⟨taskBound.1,taskBound.2.2⟩
  case finishedLentClause =>
    exact (RootSupport.below_cons.mp taskBound).1
  case disposeContinuation => split <;> simp_all only [Task.activationSupport,RootSupport.below_cons,and_self]

theorem EffectStep.homes_activationsBelow {program : Kernel.Program} {before after : State} {event : Option Event}
    (well : before.world.WellFormed) (suspensions : before.SuspensionsWellFormed)
    (valid : before.ActivationsWellFormed) (step : EffectStep program before event after) :
    after.world.ActivationsBelow after.nextActivation := by
  have bounded := valid.homes
  have taskBound := valid.task
  have frameBound := valid.frames
  cases step
  all_goals simp_all only [Task.activationSupport,Frame.activationSupport,List.flatMap_cons,
    RootSupport.below_append,RootSupport.below_cons,RootSupport.below_nil,and_true]
  all_goals try exact bounded
  case install installed => exact installed.homes_activationsBelow bounded taskBound
  case terminalPayloadExhausted started attempted | suspendPayloadExhausted started attempted |
      suspendTailPayloadExhausted started attempted =>
    exact attempted.activationsBelow (started.activationsBelow (bounded.mono (Nat.le_succ _))) started.activation_lt
  case suspendContinuationExhausted started keptPayload _ _ _ _ =>
    exact suspendRoots.activationsBelow
      (keptPayload.activationsBelow (started.activationsBelow (bounded.mono (Nat.le_succ _))) started.activation_lt)
  case terminal started keptTransfer _ _ _ =>
    exact keptTransfer.activationsBelow (started.activationsBelow (bounded.mono (Nat.le_succ _))) started.activation_lt
  case suspend started keptTransfer _ _ _ created _ _ =>
    exact created.activationsBelow (suspendRoots.activationsBelow
      (keptTransfer.activationsBelow (started.activationsBelow (bounded.mono (Nat.le_succ _))) started.activation_lt))
      started.activation_lt
  case suspendTailArm started keptTransfer _ _ _ _ _ =>
    exact suspendRoots.activationsBelow
      (keptTransfer.activationsBelow (started.activationsBelow (bounded.mono (Nat.le_succ _))) started.activation_lt)
  case resumeLast found _ _ restored kept =>
    subst restored
    have saved := valid.saved _ _ found
    exact kept.activationsBelow
      (restoreRoots.activationsBelow bounded (fun _ _ present =>
        (suspensions.origin _ _ found).homes_activationsBelow saved present)) (RootSupport.below_cons.mp saved).1
  case resumeLastExhausted found _ _ restored _ =>
    subst restored
    exact restoreRoots.activationsBelow bounded (fun _ _ present =>
      (suspensions.origin _ _ found).homes_activationsBelow (valid.saved _ _ found) present)
  case resumeCopy found _ _ copied kept =>
    have saved := valid.saved _ _ found
    exact kept.activationsBelow (copied.homes_activationsBelow well bounded (suspensions.origin _ _ found) saved)
      (copied.activation_support saved).1
  case resumeCopyExhausted found _ _ copied _ =>
    exact copied.homes_activationsBelow well bounded (suspensions.origin _ _ found) (valid.saved _ _ found)
  case resumeReturns kept => exact kept.activationsBelow bounded frameBound.1
  case completionIdentity started kept _ _ | completion started kept _ _ _ _ =>
    exact kept.activationsBelow (started.activationsBelow (bounded.mono (Nat.le_succ _))) started.activation_lt
  case completed kept _ _ | serviced kept _ _ =>
    apply kept.activationsBelow bounded
    have handlerBound := frameBound.1.2
    simp only [InstalledHandler.activationSupport,RootSupport.below_cons,RootSupport.below_nil,and_true] at handlerBound
    split <;> first | exact handlerBound.1 | exact handlerBound.2.2
  case disposeContinuation written => exact World.write_activationsBelow written bounded
  case cancel found _ _ _ =>
    exact restoreRoots.activationsBelow bounded (fun _ _ present =>
      (suspensions.origin _ _ found).homes_activationsBelow (valid.saved _ _ found) present)

/-- Capture obtains its new saved activation support from the actual routed
frames and running context. No saved-home bound is admitted after execution. -/
theorem EffectStep.created_activation_origin {program : Kernel.Program} {before after : State} {id : Identity}
    (valid : before.ActivationsWellFormed) (step : EffectStep program before (some (.suspend id)) after) :
    ∃ suspension, after.resumptions.get id = some suspension ∧
      RootSupport.Below suspension.controlActivationSupport before.nextActivation := by
  cases step with
  | suspend task _ _ _ _ _ routes _ _ _ _ _ _ _ suspension
  | suspendTailArm task _ _ _ _ _ _ routes _ _ _ _ _ _ suspension =>
    subst suspension
    have contextBound := valid.task
    rw [task] at contextBound
    obtain ⟨innerBound,handlerBound,_⟩ := routes.activation_support valid.frames
    refine ⟨_,Table.get_set _ _ _,?_⟩
    simp only [Suspension.controlActivationSupport,RootSupport.below_cons,RootSupport.below_append]
    exact ⟨⟨(RootSupport.below_cons.mp contextBound).1,handlerBound⟩,innerBound⟩

end Glorious.Language.Execution
