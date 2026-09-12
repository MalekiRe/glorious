import GloriousLanguage.ActivationStorageOrigin

/-! Ordinary evaluation, entry, return and Drop preserve the allocation
frontier of the activations actually present in their storage and control. -/
namespace Glorious.Language.Execution

open Kernel

@[simp] theorem CloseRegions.activation_support (regions : List Identity) (next : Task) :
    (CloseRegions regions next).activationSupport = next.activationSupport := by
  unfold CloseRegions
  induction regions.eraseDups with
  | nil => rfl
  | cons _ _ ih => exact ih

@[simp] theorem RetireAddresses.activation_support (addresses : List Address) (next : Task) :
    (addresses.foldr (fun address nextTask => .retire address.root nextTask) next).activationSupport =
      next.activationSupport := by
  induction addresses with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem TailFrames.activation_support {frames rest : List Frame} {activation : Identity}
    {outer : Context} {regions : List Identity} {limit : Identity}
    (route : TailFrames frames activation outer regions rest)
    (bounded : RootSupport.Below (frames.flatMap Frame.activationSupport) limit) :
    outer.activation < limit ∧ RootSupport.Below (rest.flatMap Frame.activationSupport) limit := by
  induction route with
  | activation =>
    simp only [List.flatMap_cons,Frame.activationSupport,RootSupport.below_append,
      RootSupport.below_cons,RootSupport.below_nil,and_true] at bounded
    exact ⟨bounded.1.1,bounded.2⟩
  | scope _ ih | label _ ih => exact ih (RootSupport.below_append.mp bounded).2

theorem FreshNamedFrame.activation_support {function : Function} {context : Context} {brand region limit : Identity}
    (bounded : context.activation < limit) :
    RootSupport.Below ((FreshNamedFrame function context brand region).flatMap Frame.activationSupport) limit := by
  unfold FreshNamedFrame
  split <;> simp only [List.flatMap_nil,List.flatMap_cons,Frame.activationSupport,List.append_nil,
    RootSupport.below_nil,RootSupport.below_cons,and_true]
  exact bounded

theorem LocalStep.activation_frontier {program : Kernel.Program} {before after : State} {event : Option Event}
    (step : LocalStep program before event after) : before.nextActivation ≤ after.nextActivation := by
  cases step <;> first | exact Nat.le_succ _ | exact Nat.le_refl _

theorem AtomStep.activation_frontier {program : Kernel.Program} {before after : State} {event : Option Event}
    (step : AtomStep program before event after) : before.nextActivation ≤ after.nextActivation := by
  cases step <;> exact Nat.le_refl _

theorem LocalStep.activation_support {program : Kernel.Program} {before after : State} {event : Option Event}
    (taskBound : RootSupport.Below before.task.activationSupport before.nextActivation)
    (frameBound : RootSupport.Below (before.frames.flatMap Frame.activationSupport) before.nextActivation)
    (step : LocalStep program before event after) :
    RootSupport.Below after.task.activationSupport after.nextActivation ∧
      RootSupport.Below (after.frames.flatMap Frame.activationSupport) after.nextActivation := by
  have frontier := step.activation_frontier
  have taskAfter := taskBound.mono frontier
  have framesAfter := frameBound.mono frontier
  cases step
  all_goals simp_all only [Task.activationSupport,Frame.activationSupport,List.flatMap_cons,List.flatMap_append,
    List.flatMap_nil,RootSupport.below_append,RootSupport.below_cons,RootSupport.below_nil,
    true_and,and_true,CloseRegions.activation_support,Context.bind,Context.bindRegion,Context.bindBrand]
  case enter entered =>
    have owner := entered.activation_lt
    exact ⟨owner,FreshNamedFrame.activation_support owner,owner⟩
  case enterTail entered route _ _ _ =>
    have owner := entered.activation_lt
    obtain ⟨outerBound,restBound⟩ := route.activation_support framesAfter
    exact ⟨owner,FreshNamedFrame.activation_support owner,⟨outerBound,owner⟩,restBound⟩

theorem AtomStep.activation_support {program : Kernel.Program} {before after : State} {event : Option Event}
    (taskBound : RootSupport.Below before.task.activationSupport before.nextActivation)
    (frameBound : RootSupport.Below (before.frames.flatMap Frame.activationSupport) before.nextActivation)
    (step : AtomStep program before event after) :
    RootSupport.Below after.task.activationSupport after.nextActivation ∧
      RootSupport.Below (after.frames.flatMap Frame.activationSupport) after.nextActivation := by
  cases step <;> simp_all only [Task.activationSupport,RootSupport.below_cons,
    RootSupport.below_nil,and_true,RetireAddresses.activation_support]

theorem LocalStep.homes_activationsBelow {program : Kernel.Program} {before after : State} {event : Option Event}
    (bounded : before.world.ActivationsBelow before.nextActivation)
    (taskBound : RootSupport.Below before.task.activationSupport before.nextActivation)
    (frameBound : RootSupport.Below (before.frames.flatMap Frame.activationSupport) before.nextActivation)
    (step : LocalStep program before event after) : after.world.ActivationsBelow after.nextActivation := by
  cases step
  all_goals simp_all only [Task.activationSupport,Frame.activationSupport,List.flatMap_cons,
    RootSupport.below_append,RootSupport.below_cons,RootSupport.below_nil,and_true]
  all_goals try exact bounded
  case evaluate allocated | bind allocated | invoke allocated =>
    exact allocated.activationsBelow bounded (by simpa using taskBound)
  case result kept => exact kept.activationsBelow bounded taskBound
  case transfer moved | bindReturn moved => exact moved.activationsBelow bounded
  case call consumed => exact consumed.activationsBelow bounded
  case enter entered | enterTail entered _ _ _ _ => exact entered.activationsBelow bounded
  case activationReturn kept _ _ | scopeReturn kept _ _ => exact kept.activationsBelow bounded frameBound.1
  case scope region _ => exact region.activationsBelow bounded
  case patternBind bound => exact bound.activationsBelow bounded taskBound
  case patternShell deconstructed =>
    cases deconstructed
    exact World.write_activationsBelow (by assumption) bounded
  case destroyHook allocated borrowed _ =>
    exact borrowed.activationsBelow (allocated.activationsBelow bounded taskBound.1)
  case destroyReference written | shellDone written => exact World.write_activationsBelow written bounded
  case retire retired => exact retired.activationsBelow bounded
  case regionEnd ended => exact ended.activationsBelow bounded
  case loanEnd ended | releaseRoot ended | releaseChild ended => exact ended.activationsBelow bounded

theorem AtomStep.homes_activationsBelow {program : Kernel.Program} {before after : State} {event : Option Event}
    (bounded : before.world.ActivationsBelow before.nextActivation)
    (taskBound : RootSupport.Below before.task.activationSupport before.nextActivation)
    (step : AtomStep program before event after) : after.world.ActivationsBelow after.nextActivation := by
  cases step
  all_goals simp_all only [Task.activationSupport,RootSupport.below_cons,RootSupport.below_nil,and_true]
  all_goals try exact bounded
  case constant written =>
    have actual := World.write_activationsBelow written bounded
    exact actual
  case acquire acquired => exact acquired.activationsBelow bounded
  case borrow borrowed => exact borrowed.activationsBelow bounded
  case construct created => exact created.activationsBelow bounded
  case closure captured _ _ created => exact created.activationsBelow (captured.activationsBelow bounded taskBound)
  case function created | operation created | label created => exact created.activationsBelow bounded

end Glorious.Language.Execution
