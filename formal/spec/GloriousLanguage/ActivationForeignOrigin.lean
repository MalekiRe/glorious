import GloriousLanguage.ActivationMemoryOrigin

/-! Foreign mutations allocate only under the actual session context or an
external allocation domain. Callback entry and cleanup retain their original
context identities; ordinary entry alone creates the fresh source activation. -/
namespace Glorious.Language.Foreign

open _root_.Glorious.Language.Kernel Execution Memory

theorem Mutation.activationsBelow {program : Kernel.Program} {policy : AuthorityPolicy} {before after : World}
    {action : MutationAction} {limit : Identity} (changed : Mutation program policy before action after)
    (homes : ∀ home region, policy.home home region → home.ActivationsBelow limit)
    (bounded : before.ActivationsBelow limit) : after.ActivationsBelow limit := by
  cases changed
  case allocate allowed _ allocated | allocateExterior allowed _ allocated =>
    have actual := allocated.activationsBelow bounded (homes _ _ allowed)
    exact actual
  case scalar stored => exact stored.2.2.activationsBelow bounded
  case unit stored | pointer stored => exact stored.2.activationsBelow bounded
  case aggregate constructed => exact constructed.activationsBelow bounded
  case acquire acquired => exact acquired.activationsBelow bounded
  case borrow borrowed => exact borrowed.activationsBelow bounded
  case allocateBuffer allocated => exact allocated.activationsBelow bounded
  case reallocateBuffer reallocated => exact reallocated.activationsBelow bounded
  case releaseBuffer released => exact released.activationsBelow bounded
  case rawRead read => exact read.activationsBelow bounded
  case rawWrite written => exact written.activationsBelow bounded
  case rawBorrow borrowed => exact borrowed.activationsBelow bounded
  case bulkMove moved => exact moved.activationsBelow bounded
  case retire retired => exact retired.activationsBelow bounded
  case endLoan ended => exact ended.activationsBelow bounded


theorem Mutations.activationsBelow {program : Kernel.Program} {custody : ClaimCustody}
    {policy : List ProducedResource → AuthorityPolicy} {before after : World} {produced actions}
    {limit : Identity} (changed : Mutations program custody policy before produced actions after)
    (homes : ∀ published home region, (policy published).home home region → home.ActivationsBelow limit)
    (bounded : before.ActivationsBelow limit) : after.ActivationsBelow limit := by
  induction changed with
  | refl => exact bounded
  | cons first _ ih => exact ih (first.activationsBelow (homes _) bounded)

theorem Policy.homes_activationsBelow {program : Kernel.Program} {model : Model} {contract : Contract}
    {world : World} {session : ForeignSession} {limit : Identity}
    (bounded : session.call.context.activation < limit) :
    ∀ home region, (Policy program model contract world session).home home region → home.ActivationsBelow limit := by
  rintro home region (⟨rfl,_⟩ | ⟨domain,_,_,rfl | rfl⟩)
  · exact Home.temporary_activationsBelow.mpr bounded
  · exact Home.allocation_activationsBelow _ _
  · exact Home.external_activationsBelow _ _

theorem Model.Lawful.host_activationsBelow {program : Kernel.Program} {model : Model}
    {session : ForeignSession} {imported : Import} {contract : Contract} {before after : World}
    {observation next : List Nat} {actions : List MutationAction} {action : HostAction} {limit : Identity}
    (lawful : model.Lawful program) (well : before.WellFormed)
    (selected : Selected program model session.call imported contract) (active : contract.session before session)
    (step : model.step session.call.binding.declaration before session observation actions after action next)
    (bounded : before.ActivationsBelow limit) (owner : session.call.context.activation < limit) :
    after.ActivationsBelow limit :=
  (lawful.step _ _ _ _ _ _ _ _ _ selected well active step).1.activationsBelow
    (fun _ => Policy.homes_activationsBelow owner) bounded

theorem CallbackReturnTask.activation_support {session : ForeignSession} {registration : CallbackEntry} {result : Address}
    {lease : Option ReceiverLease} {next : Code} {limit : Identity}
    (bounded : session.call.context.activation < limit) :
    RootSupport.Below (CallbackReturnTask session registration result lease next).activationSupport limit := by
  cases lease <;> simp only [CallbackReturnTask,Task.activationSupport,RootSupport.below_cons,
    RootSupport.below_nil,and_true,and_self]
  all_goals exact bounded

theorem Step.activation_frontier {program : Kernel.Program} {model : Model} {before after : State} {event : Option Event}
    (step : Step program model before event after) : before.nextActivation ≤ after.nextActivation := by
  cases step <;> exact Nat.le_refl _

theorem Step.activation_support {program : Kernel.Program} {model : Model} {before after : State} {event : Option Event}
    (taskBound : RootSupport.Below before.task.activationSupport before.nextActivation)
    (frameBound : RootSupport.Below (before.frames.flatMap Frame.activationSupport) before.nextActivation)
    (step : Step program model before event after) :
    RootSupport.Below after.task.activationSupport after.nextActivation ∧
      RootSupport.Below (after.frames.flatMap Frame.activationSupport) after.nextActivation := by
  cases step
  all_goals simp_all only [Task.activationSupport,Frame.activationSupport,List.flatMap_cons,
    RootSupport.below_append,RootSupport.below_cons,RootSupport.below_nil,and_true,
    ForeignSession.advance,ForeignSession.returned]
  case callbackResult => exact CallbackReturnTask.activation_support frameBound.1

theorem Step.homes_activationsBelow {program : Kernel.Program} {model : Model} {before after : State} {event : Option Event}
    (lawful : model.Lawful program) (well : before.world.WellFormed)
    (bounded : before.world.ActivationsBelow before.nextActivation)
    (taskBound : RootSupport.Below before.task.activationSupport before.nextActivation)
    (frameBound : RootSupport.Below (before.frames.flatMap Frame.activationSupport) before.nextActivation)
    (step : Step program model before event after) : after.world.ActivationsBelow after.nextActivation := by
  cases step
  all_goals simp_all only [Task.activationSupport,Frame.activationSupport,List.flatMap_cons,
    RootSupport.below_append,RootSupport.below_cons,RootSupport.below_nil,and_true]
  all_goals try exact bounded
  case enter kept _ _ _ => exact kept.activationsBelow bounded taskBound
  case host selected active transition | fault selected active transition =>
    exact lawful.host_activationsBelow well selected active transition bounded taskBound
  case result selected active transition _ transferred =>
    exact transferred.activationsBelow (lawful.host_activationsBelow well selected active transition bounded taskBound)
  case callback selected active transition _ _ =>
    exact lawful.host_activationsBelow well selected active transition bounded taskBound
  case callbackResult kept retired => exact retired.activationsBelow (kept.activationsBelow bounded frameBound.1)

end Glorious.Language.Foreign
