import GloriousLanguage.ActivationEffectOrigin

/-! Lexical transfers and sealed proof values allocate under their actual
context owner. Reservation and pattern machinery preserve the same home and
control bounds as ordinary invocation; they do not introduce new activations. -/
namespace Glorious.Language.Execution

open Kernel

theorem LabelRoute.activation_support {frames inner outer : List Frame} {brand region : Identity}
    {context : Context} {type : Term} {limit : Identity}
    (route : LabelRoute frames brand inner context region type outer)
    (bounded : RootSupport.Below (frames.flatMap Frame.activationSupport) limit) :
    context.activation < limit ∧ RootSupport.Below (outer.flatMap Frame.activationSupport) limit := by
  rw [route.1] at bounded
  simp only [List.flatMap_append,List.flatMap_cons,Frame.activationSupport,RootSupport.below_append,
    RootSupport.below_cons,RootSupport.below_nil,and_true] at bounded
  exact bounded.2

theorem DisposesReservations.activation_support {context : Context} {places : List ResolvedPlace} {next : Task}
    {limit : Identity} (bounded : context.activation < limit)
    (continued : RootSupport.Below next.activationSupport limit) :
    RootSupport.Below (DisposesReservations context places next).activationSupport limit := by
  induction places with
  | nil => exact continued
  | cons _ _ ih => exact RootSupport.below_cons.mpr ⟨bounded,ih⟩

theorem CopiesObservations.activationsBelow {program : Kernel.Program} {context : Context}
    {before after : World} {observations : List (Local × Address × Authority)} {bindings : List (Local × Address)}
    {limit : Identity} (copied : CopiesObservations program context before observations bindings after)
    (bounded : before.ActivationsBelow limit) (owner : context.activation < limit) : after.ActivationsBelow limit := by
  induction copied with
  | nil => exact bounded
  | copy _ _ allocated copied _ ih | borrow _ _ allocated copied _ ih =>
    exact ih (copied.activationsBelow (allocated.activationsBelow bounded owner))

theorem PacksBindings.activationsBelow {program : Kernel.Program} {context : Context} {before after : World}
    {pattern resultOrigin positive bindings pack} {limit : Identity}
    (packed : PacksBindings program context before pattern resultOrigin positive bindings pack after)
    (bounded : before.ActivationsBelow limit) (owner : context.activation < limit) : after.ActivationsBelow limit := by
  obtain ⟨_,_,_,_,allocated,_,created,rfl⟩ := packed
  have actual := created.activationsBelow (allocated.activationsBelow bounded owner)
  exact actual

theorem UnitFields.activationsBelow {program : Kernel.Program} {context : Context} {before after : World}
    {types : List Term} {index : Option Nat} {pack : Address} {fields : List Address} {limit : Identity}
    (assembled : UnitFields program context before types index pack fields after)
    (bounded : before.ActivationsBelow limit) (owner : context.activation < limit) : after.ActivationsBelow limit := by
  induction assembled with
  | done => exact bounded
  | selected _ _ _ ih => exact ih bounded
  | unitBefore allocated created _ ih | unitAfter allocated created _ ih =>
    exact ih (created.2.activationsBelow (allocated.activationsBelow bounded owner))

theorem TestResult.activationsBelow {program : Kernel.Program} {context : Context} {before after : World}
    {destination type pattern positive observations} {limit : Identity}
    (tested : TestResult program context before destination type pattern positive observations after)
    (bounded : before.ActivationsBelow limit) (owner : context.activation < limit) : after.ActivationsBelow limit := by
  cases tested with
  | result _ _ copied packed fields constructed =>
    exact constructed.activationsBelow
      (fields.choose_spec.2.2.2.2.activationsBelow
        (packed.activationsBelow (copied.activationsBelow bounded owner) owner) owner)

theorem ConsumesAvailability.activationsBelow {before after : World}
    {address : Address} {id : Identity} {access : Access} {limit : Identity}
    (consumed : ConsumesAvailability before address id access after)
    (bounded : before.ActivationsBelow limit) : after.ActivationsBelow limit := by
  cases consumed with
  | lent => exact bounded
  | owned _ written =>
    have actual := World.write_activationsBelow written bounded
    exact actual

theorem ControlStep.activation_frontier {program : Kernel.Program} {before after : State} {event : Option Event}
    (step : ControlStep program before event after) : before.nextActivation ≤ after.nextActivation := by
  cases step <;> exact Nat.le_refl _

theorem ControlStep.activation_support {program : Kernel.Program} {before after : State} {event : Option Event}
    (taskBound : RootSupport.Below before.task.activationSupport before.nextActivation)
    (frameBound : RootSupport.Below (before.frames.flatMap Frame.activationSupport) before.nextActivation)
    (step : ControlStep program before event after) :
    RootSupport.Below after.task.activationSupport after.nextActivation ∧
      RootSupport.Below (after.frames.flatMap Frame.activationSupport) after.nextActivation := by
  cases step
  all_goals simp_all only [Task.activationSupport,RootSupport.below_cons,RootSupport.below_nil,
    and_true,true_and,CloseRegions.activation_support,Context.bind,Context.bindBrand]
  case leave route _ _ _ => exact route.activation_support frameBound
  case destroyAvailable => exact DisposesReservations.activation_support taskBound.1 taskBound.2

theorem ControlStep.homes_activationsBelow {program : Kernel.Program} {before after : State} {event : Option Event}
    (bounded : before.world.ActivationsBelow before.nextActivation)
    (taskBound : RootSupport.Below before.task.activationSupport before.nextActivation)
    (frameBound : RootSupport.Below (before.frames.flatMap Frame.activationSupport) before.nextActivation)
    (step : ControlStep program before event after) : after.world.ActivationsBelow after.nextActivation := by
  cases step
  all_goals simp_all only [Task.activationSupport,RootSupport.below_cons,RootSupport.below_nil,and_true]
  all_goals try exact bounded
  case leave route kept _ _ => exact kept.activationsBelow bounded (route.activation_support frameBound).1
  case reserve allocated created =>
    have actual := created.activationsBelow (allocated.activationsBelow bounded (by simpa using taskBound))
    exact actual
  case available transferred | bindings transferred => exact transferred.activationsBelow bounded
  case destroyAvailable written =>
    have actual := World.write_activationsBelow written bounded
    exact actual
  case destroySpentAvailable written => exact World.write_activationsBelow written bounded
  case contextualCall consumed closed => exact closed.activationsBelow (consumed.activationsBelow bounded)
  case positiveTest allocated tested | negativeTest allocated tested =>
    exact tested.activationsBelow (allocated.activationsBelow bounded (by simpa using taskBound)) taskBound

end Glorious.Language.Execution
