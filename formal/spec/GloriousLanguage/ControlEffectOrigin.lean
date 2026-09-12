import GloriousLanguage.ControlBranchOrigin

/-! Effect entry, actual capture, copied and final replay, completion and
cancellation consume one control-support invariant. Settled metadata keeps
its historical origin without asserting that discarded frames remain live. -/
namespace Glorious.Language.Execution

open Kernel

theorem CopiesSnapshot.root_frontier {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation} (copied : CopiesSnapshot program before suspension map after) :
    before.world.nextRoot ≤ after.world.nextRoot := by
  rw [copied.result]
  exact Nat.le_add_left _ _

theorem EffectStep.root_frontier {program : Kernel.Program} {before after : State} {event : Option Event}
    (step : EffectStep program before event after) : before.world.nextRoot ≤ after.world.nextRoot := by
  cases step <;> try exact Nat.le_refl _
  case install installed => exact installed.suspensionExtension.counter
  case terminal started keptTransfer _ _ _ =>
    exact Nat.le_trans started.suspensionExtension.counter keptTransfer.suspensionExtension.counter
  case suspend started keptTransfer _ _ _ created _ _ =>
    exact Nat.le_trans (Nat.le_trans started.suspensionExtension.counter keptTransfer.suspensionExtension.counter)
      created.suspensionExtension.counter
  case suspendTailArm started keptTransfer _ _ _ _ _ =>
    exact Nat.le_trans started.suspensionExtension.counter keptTransfer.suspensionExtension.counter
  case resumeLast restored keptTransfer =>
    subst restored
    exact keptTransfer.suspensionExtension.counter
  case resumeCopy copied keptTransfer => exact Nat.le_trans copied.root_frontier keptTransfer.suspensionExtension.counter
  case resumeReturns keptTransfer => exact keptTransfer.suspensionExtension.counter
  case completionIdentity started keptTransfer _ _ =>
    exact Nat.le_trans started.suspensionExtension.counter keptTransfer.suspensionExtension.counter
  case completion started keptTransfer _ _ _ _ =>
    exact Nat.le_trans started.suspensionExtension.counter keptTransfer.suspensionExtension.counter
  case completed keptTransfer _ _ => exact keptTransfer.suspensionExtension.counter
  case serviced keptTransfer _ _ => exact keptTransfer.suspensionExtension.counter
  case disposeContinuation cleared => exact (World.write_suspensionExtension cleared).counter

theorem StartsClause.root_support {before : State} {handler : InstalledHandler} {context : Context}
    {after : World} {limit : Identity} (started : StartsClause before handler context after)
    (bounded : RootSupport.Below handler.rootSupport limit) : RootSupport.Below context.rootSupport limit := by
  rw [started.2]
  exact (RootSupport.below_append.mp (RootSupport.below_append.mp bounded).1).1

theorem StartsResumptionClause.root_support {before : State} {handler : InstalledHandler} {lexical localSlot : Local}
    {context : Context} {after : World} {limit : Identity}
    (started : StartsResumptionClause before handler lexical context localSlot after)
    (bounded : RootSupport.Below handler.rootSupport limit) : RootSupport.Below context.rootSupport limit := by
  obtain ⟨_,_,started,_,rfl,_⟩ := started
  exact started.root_support bounded

theorem CreatesContinuation.root_bound {program : Kernel.Program} {context : Context} {before after : World}
    {id signature answer effects quantity localSlot address}
    (created : CreatesContinuation program context before id signature answer effects quantity localSlot address after) :
    address.root < after.nextRoot := by
  obtain ⟨_,_,_,allocated,created⟩ := created
  exact Nat.lt_of_lt_of_le allocated.root_bound created.suspensionExtension.counter

theorem DelimitedRoots.root_support {world : World} {handler : InstalledHandler} {inner : List Frame}
    {kept roots : List Identity} (well : world.WellFormed)
    (selected : DelimitedRoots world handler inner kept roots) : RootSupport.Below roots world.nextRoot := by
  intro id member
  obtain ⟨root,found,_⟩ := (selected.2 id).mp member
  exact World.root_bound well found

theorem PayloadPlan.root_support {program : Language.Program} {world : World}
    {addresses : List Address} {patterns : List Pattern} {actions : PatternActions}
    (well : world.WellFormed) (planned : PayloadPlan program world addresses patterns actions)
    (bounded : RootSupport.Below (addresses.map Address.root) world.nextRoot) :
    RootSupport.Below ((ScheduledPattern actions).flatMap PatternAction.rootSupport) world.nextRoot := by
  induction planned with
  | nil => simp [ScheduledPattern]
  | cons first _ ih =>
    simp only [List.map_cons,RootSupport.below_cons] at bounded
    have one := first.root_support well bounded.1
    have rest := ih bounded.2
    simp_all only [ScheduledPattern,List.flatMap_append,RootSupport.below_append,true_and]

theorem Installs.root_support {program : Kernel.Program} {before : State} {outer : Context}
    {syntaxNode : Handler} {handler : InstalledHandler} {after : World}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (bounded : RootSupport.Below outer.rootSupport before.world.nextRoot)
    (installed : Installs program before outer syntaxNode handler after) :
    RootSupport.Below handler.rootSupport after.nextRoot := by
  have outerBound := bounded.mono installed.suspensionExtension.counter
  obtain ⟨first,second,sources,captures,captured,bindings,bound,disposed,one,two,_,capturedValues,boundValues,retired,rfl,rfl⟩ := installed
  have inputsWell := (capturedValues.worldTyped valid inventory (two.worldTyped (one.worldTyped typed))).1
  have environmentBound := RootSupport.below_map.mpr (boundValues.bindings_root_bound inputsWell)
  simp only [InstalledHandler.rootSupport,RootSupport.below_append]
  exact ⟨⟨environmentBound.mono retired.suspensionExtension.counter,outerBound⟩,outerBound⟩

theorem EffectStep.control_support {program : Kernel.Program} {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world) (control : before.ControlWellFormed)
    (step : EffectStep program before event after) :
    RootSupport.Below after.task.rootSupport after.world.nextRoot ∧
      RootSupport.Below (after.frames.flatMap Frame.rootSupport) after.world.nextRoot := by
  have frontier := step.root_frontier
  have taskBound := control.task
  have taskAfter := taskBound.mono frontier
  have frameBound := control.frames
  have framesAfter := frameBound.mono frontier
  have afterTyped := step.worldTyped valid inventory typed
  have afterWell := afterTyped.1
  cases step
  all_goals simp_all only [Task.rootSupport,Frame.rootSupport,List.flatMap_cons,List.flatMap_append,
    List.flatMap_nil,RootSupport.below_append,RootSupport.below_cons,RootSupport.below_nil,
    true_and,and_true,CloseRegions.root_support]
  case install installed =>
    have handlerBound := installed.root_support valid inventory typed taskBound
    exact ⟨(RootSupport.below_append.mp (RootSupport.below_append.mp handlerBound).1).2,handlerBound⟩
  case operationCall resolved => exact resolved.root_support afterWell
  case terminal route started keptTransfer roots _ planned =>
    obtain ⟨_,handlerBound,outerBound⟩ := route.control_support framesAfter
    have clauseBound := started.root_support handlerBound
    exact ⟨⟨roots.root_support afterWell,clauseBound,planned.root_support afterWell keptTransfer.root_support⟩,
      ⟨handlerBound,clauseBound⟩,outerBound⟩
  case suspend route started keptTransfer _ _ _ created planned _ =>
    obtain ⟨_,handlerBound,outerBound⟩ := route.control_support framesAfter
    have clauseBound := started.root_support handlerBound
    have keptBound := keptTransfer.root_support.mono created.suspensionExtension.counter
    exact ⟨⟨Context.bind_root_support clauseBound created.root_bound,planned.root_support afterWell keptBound⟩,
      ⟨handlerBound,clauseBound⟩,outerBound⟩
  case suspendTailArm route started keptTransfer _ _ _ planned _ =>
    obtain ⟨_,handlerBound,outerBound⟩ := route.control_support framesAfter
    have clauseBound := started.root_support handlerBound
    have movedWell := (keptTransfer.worldTyped valid inventory (started.worldTyped typed)).1
    have patternBound := planned.root_support movedWell keptTransfer.root_support
    exact ⟨⟨clauseBound,patternBound⟩,
      clauseBound,⟨handlerBound,clauseBound⟩,outerBound⟩
  case continuationCall argument =>
    obtain ⟨_,_,resolved⟩ := argument
    exact Context.resolves_root_bound afterWell taskBound resolved
  case resumeLast found _ _ _ keptTransfer =>
    have savedBound := (control.saved_current found).mono frontier
    simp only [Suspension.controlRootSupport,RootSupport.below_append] at savedBound
    exact ⟨⟨savedBound.1.1,keptTransfer.root_bound⟩,savedBound.2,savedBound.1.2⟩
  case resumeCopy found _ _ copied keptTransfer =>
    obtain ⟨contextBound,handlerBound,savedBound⟩ := copied.control_support (control.saved_current found)
    have transferred := keptTransfer.suspensionExtension.counter
    exact ⟨⟨contextBound.mono transferred,keptTransfer.root_bound⟩,savedBound.mono transferred,handlerBound.mono transferred⟩
  case resumeReturns keptTransfer => exact keptTransfer.root_bound
  case completionIdentity started keptTransfer roots _ =>
    have clauseBound := started.root_support framesAfter.1
    exact ⟨⟨roots.root_support afterWell,clauseBound,keptTransfer.root_bound⟩,clauseBound⟩
  case completion started keptTransfer roots _ _ planned =>
    have clauseBound := started.root_support framesAfter.1
    exact ⟨⟨roots.root_support afterWell,clauseBound,planned.root_support afterWell keptTransfer.root_bound⟩,clauseBound⟩
  case completed keptTransfer roots _ => exact ⟨roots.root_support afterWell,keptTransfer.root_bound⟩
  case serviced keptTransfer roots _ => exact ⟨roots.root_support afterWell,keptTransfer.root_bound⟩
  case finishedOwnedClause roots _ =>
    have handlerBound := taskBound.1
    simp only [InstalledHandler.rootSupport,RootSupport.below_append] at handlerBound
    exact ⟨⟨handlerBound.1.1,roots.root_support afterWell⟩,handlerBound.2⟩
  case finishedLentClause =>
    exact (RootSupport.below_append.mp (RootSupport.below_append.mp taskBound.1).1).1
  case disposeContinuation =>
    split
    · exact RootSupport.below_append.mpr ⟨taskAfter.1,taskAfter.2.2⟩
    · exact taskAfter.2.2
  case cancel found _ _ _ => exact fun root member => control.suspensions.root_bound found member

end Glorious.Language.Execution
