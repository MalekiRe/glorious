import GloriousLanguage.ControlStorageOrigin

/-! Ordinary execution preserves the root-allocation provenance of its
actual task and retained frames, including entry, tail cleanup and Drop. -/
namespace Glorious.Language.Execution

open Kernel

theorem TailFrames.control_support {frames rest : List Frame} {activation : Identity}
    {outer : Context} {regions : List Identity} {limit : Identity}
    (route : TailFrames frames activation outer regions rest)
    (bounded : RootSupport.Below (frames.flatMap Frame.rootSupport) limit) :
    RootSupport.Below outer.rootSupport limit ∧ RootSupport.Below (rest.flatMap Frame.rootSupport) limit := by
  induction route with
  | activation => exact RootSupport.below_append.mp bounded
  | scope _ ih | label _ ih => exact ih (RootSupport.below_append.mp bounded).2

theorem FreshNamedFrame.root_support {function : Function} {context : Context} {brand region limit : Identity}
    (bounded : RootSupport.Below context.rootSupport limit) :
    RootSupport.Below ((FreshNamedFrame function context brand region).flatMap Frame.rootSupport) limit := by
  unfold FreshNamedFrame
  split <;> simp only [List.flatMap_nil,List.flatMap_cons,Frame.rootSupport,List.append_nil,RootSupport.below_nil]
  exact bounded

theorem LocalStep.control_support {program : Kernel.Program} {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (taskBound : RootSupport.Below before.task.rootSupport before.world.nextRoot)
    (frameBound : RootSupport.Below (before.frames.flatMap Frame.rootSupport) before.world.nextRoot)
    (step : LocalStep program before event after) :
    RootSupport.Below after.task.rootSupport after.world.nextRoot ∧
      RootSupport.Below (after.frames.flatMap Frame.rootSupport) after.world.nextRoot := by
  have frontier := step.suspensionExtension.counter
  have taskAfter := taskBound.mono frontier
  have framesAfter := frameBound.mono frontier
  have afterWell := (step.worldTyped valid inventory typed).1
  cases step
  all_goals simp_all only [Task.rootSupport,Frame.rootSupport,PatternAction.rootSupport,
    EntrySource.rootSupport,InvocationInput.rootSupport,List.flatMap_cons,List.flatMap_append,
    List.flatMap_nil,RootSupport.below_append,RootSupport.below_cons,RootSupport.below_nil,
    true_and,and_true,CloseRegions.root_support,Address.child]
  case evaluate allocated => exact ⟨Context.bind_root_support taskAfter allocated.root_bound,allocated.root_bound⟩
  case bind allocated => exact ⟨Context.bind_root_support taskAfter allocated.root_bound,allocated.root_bound⟩
  case result kept => exact kept.root_bound
  case discard resolved => exact Context.resolves_root_bound typed.1 taskBound resolved
  case assign target source _ _ =>
    have targetBound := Context.resolves_root_bound typed.1 taskBound target
    exact ⟨targetBound,Context.resolves_root_bound typed.1 taskBound source,targetBound⟩
  case invoke allocated => exact ⟨Context.bind_root_support taskAfter allocated.root_bound,allocated.root_bound⟩
  case call resolved _ _ _ _ inputs _ =>
    exact ⟨Nat.lt_of_lt_of_le (Context.resolves_root_bound typed.1 taskBound resolved) frontier,
      (inputs.root_support typed.1 taskBound).mono frontier⟩
  case enter entered =>
    have contextBound := entered.context_root_support typed.1
    exact ⟨contextBound,FreshNamedFrame.root_support contextBound⟩
  case enterTail entered route roots _ _ =>
    have contextBound := entered.context_root_support typed.1
    obtain ⟨outerBound,restBound⟩ := route.control_support framesAfter
    exact ⟨⟨roots.root_support afterWell,contextBound⟩,FreshNamedFrame.root_support contextBound,outerBound,restBound⟩
  case activationReturn kept roots _ => exact ⟨roots.root_support afterWell,kept.root_bound⟩
  case scope => exact taskAfter
  case scopeReturn kept roots _ => exact ⟨roots.root_support afterWell,kept.root_bound⟩
  case label => exact taskBound
  case choose resolved _ planned =>
    exact planned.root_support typed.1 (Context.resolves_root_bound typed.1 taskBound resolved)
  case patternBind bound => exact Context.bind_root_support taskAfter.1 (bound.root_bound typed.1)
  case unsafeAllowed => exact taskBound
  case destroyHook allocated borrowed _ =>
    have fresh := Nat.lt_of_lt_of_le allocated.root_bound borrowed.suspensionExtension.counter
    exact ⟨⟨taskAfter.1,fresh⟩,fresh⟩
  case endLoan resolved _ _ => exact Context.resolves_root_bound typed.1 taskBound resolved

theorem AtomStep.control_support {program : Kernel.Program} {before after : State} {event : Option Event}
    (well : before.world.WellFormed)
    (taskBound : RootSupport.Below before.task.rootSupport before.world.nextRoot)
    (frameBound : RootSupport.Below (before.frames.flatMap Frame.rootSupport) before.world.nextRoot)
    (step : AtomStep program before event after) :
    RootSupport.Below after.task.rootSupport after.world.nextRoot ∧
      RootSupport.Below (after.frames.flatMap Frame.rootSupport) after.world.nextRoot := by
  have frontier := step.suspensionExtension.counter
  have taskAfter := taskBound.mono frontier
  have framesAfter := frameBound.mono frontier
  cases step
  all_goals simp_all only [Task.rootSupport,RootSupport.below_append,RootSupport.below_cons,
    RootSupport.below_nil,and_true,true_and]
  case closure captured _ _ created =>
    exact RetireAddresses.root_support (captured.root_support.mono created.suspensionExtension.counter) taskAfter.1
  case primitive resolved _ => exact resolved.root_support well

end Glorious.Language.Execution
