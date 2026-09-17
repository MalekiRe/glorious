import GloriousLanguage.ForeignRuntimeSupport
import GloriousLanguage.ForeignAuthorityOrigin

/-! Runtime liveness is preserved through actual source execution, nested host
calls and callback cleanup. It follows the callback frame and the host-state
evolution producer, not an assumed post-registry permission predicate. -/
namespace Glorious.Language

open _root_.Glorious.Language.Kernel

namespace Execution

theorem LocalStep.callback_control {program : Kernel.Program} {before after : State} {event : Option Event}
    (covered : before.CallbackControl) (step : LocalStep program before event after) :
    after.CallbackControl ∧ after.callbackRuntimes ⊆ before.callbackRuntimes := by
  cases step
  all_goals simp_all only [State.CallbackControl,State.callbackRuntimes,Task.CallbackCovers,
    Task.callbackRuntimes,FramesCallbackCovers,Frame.CallbackCovers,Frame.callbackRuntimes,
    Foreign.AmbientRuntimes.append,Foreign.AmbientRuntimes.cons,List.nil_append,
    CloseRegions.callback_covers,CloseRegions.callback_runtimes,ReleaseLoans.callback_covers,ReleaseLoans.callback_runtimes,
    ReleaseCustodyLoans.callback_covers,ReleaseCustodyLoans.callback_runtimes,FreshNamedFrame.callback_covers,
    FreshNamedFrame.callback_runtimes,true_and,and_true,List.Subset.refl]
  case destroyHookExhausted => exact List.subset_append_right _ _
  case enterTail _ _ tail _ _ _ =>
    exact ⟨tail.callback_covers covered,tail.callback_runtimes.symm ▸ List.Subset.refl _⟩

theorem AtomStep.callback_control {program : Kernel.Program} {before after : State} {event : Option Event}
    (covered : before.CallbackControl) (step : AtomStep program before event after) :
    after.CallbackControl ∧ after.callbackRuntimes = before.callbackRuntimes := by
  cases step <;> simp_all only [State.CallbackControl,State.callbackRuntimes,Task.CallbackCovers,
    Task.callbackRuntimes,Task.retire_fold_callback_covers,Task.retire_fold_callback_runtimes,true_and]

theorem ControlStep.callback_control {program : Kernel.Program} {before after : State} {event : Option Event}
    (covered : before.CallbackControl) (step : ControlStep program before event after) :
    after.CallbackControl ∧ after.callbackRuntimes = before.callbackRuntimes := by
  cases step
  all_goals simp_all only [State.CallbackControl,State.callbackRuntimes,Task.CallbackCovers,
    Task.callbackRuntimes,CloseRegions.callback_covers,CloseRegions.callback_runtimes,
    DisposesReservations.callback_covers,DisposesReservations.callback_runtimes,true_and,List.nil_append]
  case leave _ route _ _ _ => exact route.callback_covers covered

theorem PrimitiveStep.callback_control {program : Kernel.Program} {before after : State} {event : Option Event}
    (covered : before.CallbackControl) (step : PrimitiveStep program before event after) :
    after.CallbackControl ∧ after.callbackRuntimes = before.callbackRuntimes := by
  cases step <;> simp_all only [State.CallbackControl,State.callbackRuntimes,Task.CallbackCovers,
    Task.callbackRuntimes,true_and]

theorem EffectStep.callback_control {program : Kernel.Program} {before after : State} {event : Option Event}
    (suspensions : before.SuspensionsWellFormed) (covered : before.CallbackControl)
    (step : EffectStep program before event after) :
    after.CallbackControl ∧ after.callbackRuntimes = before.callbackRuntimes := by
  cases step
  all_goals simp_all only [State.CallbackControl,State.callbackRuntimes,Task.CallbackCovers,
    Task.callbackRuntimes,FramesCallbackCovers,Frame.CallbackCovers,Frame.callbackRuntimes,
    Foreign.AmbientRuntimes.append,Foreign.AmbientRuntimes.cons,List.nil_append,
    CloseRegions.callback_covers,CloseRegions.callback_runtimes,true_and,and_true]
  case terminal _ _ _ _ route _ _ _ _ _ => exact route.callback_covers covered
  case suspend _ _ _ _ _ _ route _ _ _ _ _ _ _ _ => exact route.callback_covers covered
  case suspendTailArm _ _ _ _ _ _ _ route _ _ _ _ _ _ _ => exact route.callback_covers covered
  case resumeLast _ found _ _ _ _ =>
    have free := (suspensions.origin _ _ found).foreignFree
    constructor
    · rw [List.append_assoc]
      exact FramesCallbackCovers.free_append free ⟨trivial,trivial,covered⟩
    · simp only [Foreign.AmbientRuntimes.free free,Foreign.AmbientRuntimes.nil,List.nil_append]
  case resumeCopy _ found _ _ _ _ =>
    have free := (suspensions.origin _ _ found).foreignFree
    constructor
    · rw [List.append_assoc]
      exact FramesCallbackCovers.map_free_append free ⟨trivial,trivial,covered⟩
    · simp only [Foreign.AmbientRuntimes.map_free free,Foreign.AmbientRuntimes.nil,List.nil_append]
  case resumeCopyExhausted copied _ =>
    simp_all only [copied.result,true_and]
  case disposeContinuation =>
    split <;> simp_all only [Task.CallbackCovers,Task.callbackRuntimes,true_and]

end Execution

namespace Foreign

open Execution

/-- The actual callback entry owns a currently live runtime and bounded ABI
entry. Lent callbacks retain their exact record; one-shot ownership is consumed
at dispatch, never inferred from a post-consumption callable permission. -/
theorem Step.callback_entry {program : Kernel.Program} {model : Model} {before after : State} {event : Option Event}
    {caller : Execution.Context} {function : Function} {source : EntrySource}
    {session : ForeignSession} {entry : CallbackEntry} {resultType : Term} {lease : Option ReceiverLease}
    {next : Code} {rest : List Frame}
    (step : Step program model before event after) (entered : after.task = .enter caller function source false)
    (frame : after.frames = .hostCallback session entry resultType lease next :: rest) :
    entry.runtime ∈ model.runtimes after.hostState ∧ entry.entryAddress < 2^program.declarations.input.target.pointerBits ∧
      ∃ registration ∈ model.registrations before.hostState,
        registration.identity = entry.registration ∧ registration.runtime = entry.runtime ∧
        registration.entryAddress = entry.entryAddress ∧ registration.active = true ∧
        (registration.access ≠ .owned → registration ∈ model.registrations after.hostState) ∧
        (registration.access = .owned → registration ∉ model.registrations after.hostState) := by
  cases step <;> simp_all
  case callback admitted _ =>
    rw [← frame.1.2.1]
    exact ⟨admitted.runtime,admitted.entry,_,admitted.registered,admitted.identity,rfl,rfl,
      admitted.active,admitted.lent,admitted.owned_unregistered⟩
  case callbackResult =>
    unfold CallbackReturnTask at entered
    split at entered <;> cases entered

theorem Step.callback_control {program : Kernel.Program} {model : Model} {before after : State} {event : Option Event}
    (covered : before.CallbackControl) (step : Step program model before event after) : after.CallbackControl := by
  cases step
  all_goals simp_all only [State.CallbackControl,Task.CallbackCovers,FramesCallbackCovers,Frame.CallbackCovers,
    AmbientRuntimes.cons,Frame.callbackRuntimes,ForeignSession.advance,ForeignSession.returned,
    CallbackReturnTask.callback_covers,true_and,and_true]
  case enter => exact List.Subset.refl _
  case callbackResult =>
    intro runtime member
    rcases List.mem_append.mp member with current | outer
    · exact current
    · exact List.mem_cons_of_mem _ (covered.1 outer)

theorem HostStateEvolution.live_runtimes {program : Kernel.Program} {contract : Contract} {model : Model}
    {initial current : World} {session : ForeignSession} {before after : List Nat}
    (evolution : HostStateEvolution program contract model initial current session before after)
    (live : ∀ runtime ∈ session.heldRuntimes, runtime ∈ model.runtimes before) :
    ∀ runtime ∈ session.heldRuntimes, runtime ∈ model.runtimes after :=
  fun runtime member => evolution.runtimes runtime member (live runtime member)

theorem Step.callbacks {program : Kernel.Program} {model : Model} {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (lawful : model.Lawful program) (typed : Typing.WorldTyped program before.world)
    (callbacks : model.CallbacksWellFormed before) (step : Step program model before event after) :
    model.CallbacksWellFormed after := by
  refine ⟨step.callback_control callbacks.control,?_⟩
  have taskLive := callbacks.task
  have frameLive := callbacks.frames
  have taskCovers := callbacks.control.1
  have frameCovers := callbacks.control.2
  cases step
  all_goals simp_all only [State.callbackRuntimes,Task.callbackRuntimes,Task.CallbackCovers,
    FramesCallbackCovers,Frame.CallbackCovers,AmbientRuntimes.cons,Frame.callbackRuntimes,
    ForeignSession.advance,ForeignSession.returned,CallbackReturnTask.callback_runtimes,
    List.nil_append,List.forall_mem_append,List.forall_mem_cons,and_self,true_and,implies_true]
  case enter _ selected kept callTyped precondition started =>
    exact (lawful.start _ _ _ _ _ selected (kept.worldTyped valid inventory typed).1
      callTyped precondition started).2.2.live_runtimes frameLive
  case host _ _ selected active changed =>
    have held := (lawful.step _ _ _ _ _ _ _ _ _ selected typed.1 active changed).2.2.2.2.2.2.2.2.live_runtimes taskLive
    exact ⟨held,fun runtime member => held runtime (taskCovers member)⟩
  case result _ _ selected active changed _ _ =>
    have held := (lawful.step _ _ _ _ _ _ _ _ _ selected typed.1 active changed).2.2.2.2.2.2.2.2.live_runtimes taskLive
    exact fun runtime member => held runtime (taskCovers member)
  case callback _ _ selected active changed admitted _ =>
    have held := (lawful.step _ _ _ _ _ _ _ _ _ selected typed.1 active changed).2.2.2.2.2.2.2.2.live_runtimes taskLive
    exact ⟨⟨admitted.runtime,held⟩,fun runtime member => held runtime (taskCovers member)⟩
  case callbackReturned _ _ selected postcondition returned =>
    have held := (lawful.callbackReturned _ _ _ _ _ _ _ _ selected typed.1 postcondition returned).2.2.live_runtimes taskLive.2
    exact ⟨held,fun runtime member => held runtime (frameCovers.1 member)⟩
  case fault _ _ selected active changed =>
    have held := (lawful.step _ _ _ _ _ _ _ _ _ selected typed.1 active changed).2.2.2.2.2.2.2.2.live_runtimes taskLive
    exact fun runtime member => held runtime (taskCovers member)

end Foreign

namespace Execution

/-- Source transitions retain live runtime support; fatal termination may
discard a task continuation but cannot invent a runtime dependency. Foreign
transitions use actual HostStateEvolution and callback-entry acquisition. -/
theorem Step.callbacks {program : Kernel.Program} {host : Foreign.Model} {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (suspensions : before.SuspensionsWellFormed) (callbacks : host.CallbacksWellFormed before)
    (step : Step program host before event after) : host.CallbacksWellFormed after := by
  rcases step.host_state with unchanged | foreign
  · have source (preserved : after.CallbackControl ∧ after.callbackRuntimes = before.callbackRuntimes) :
        host.CallbacksWellFormed after :=
      ⟨preserved.1,by simpa only [preserved.2,unchanged] using callbacks.live⟩
    rcases step with localStep | atom | effect | branch | primitive | foreign
    · obtain ⟨control,retained⟩ := localStep.callback_control callbacks.control
      exact ⟨control,fun runtime member => unchanged ▸ callbacks.live runtime (retained member)⟩
    · exact source (atom.callback_control callbacks.control)
    · exact source (effect.callback_control suspensions callbacks.control)
    · exact source (branch.callback_control callbacks.control)
    · exact source (primitive.callback_control callbacks.control)
    · exact foreign.callbacks valid inventory lawful typed callbacks
  · exact foreign.callbacks valid inventory lawful typed callbacks

/-- Callback code/runtime ownership survives arbitrary source execution,
nested host actions and ordinary destructor cleanup. Only actual host return
releases the callback frame; registry deletion alone cannot release its runtime. -/
theorem Run.callbacks {program : Kernel.Program} {host : Foreign.Model} {before after : State} {trace : List Event}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (suspensions : before.SuspensionsWellFormed) (callbacks : host.CallbacksWellFormed before)
    (run : Run program host before trace after) : host.CallbacksWellFormed after := by
  induction run with
  | refl => exact callbacks
  | silent step tail ih =>
    exact ih (step.worldTyped valid inventory lawful typed)
      (step.suspensions valid inventory lawful typed suspensions (by intro impossible; cases impossible))
      (step.callbacks valid inventory lawful typed suspensions callbacks)
  | @visible before middle after event trace step tail ih =>
    have retained := step.callbacks valid inventory lawful typed suspensions callbacks
    by_cases fatal : event = Event.fatal .resource
    · subst fatal
      rw [tail.after_eq_of_fatal step.fatal_task]
      exact retained
    · exact ih (step.worldTyped valid inventory lawful typed)
        (step.suspensions valid inventory lawful typed suspensions (fun equal => fatal (Option.some.inj equal))) retained


/-- An executing callback's runtime remains live after arbitrary intervening
source and nested host execution, including its retained destruction phase. -/
theorem Run.active_callback_runtime {program : Kernel.Program} {host : Foreign.Model} {before after : State}
    {trace : List Event} {session : ForeignSession} {entry : CallbackEntry} {resultType : Term}
    {lease : Option ReceiverLease} {next : Code}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (suspensions : before.SuspensionsWellFormed) (callbacks : host.CallbacksWellFormed before)
    (run : Run program host before trace after)
    (frame : Frame.hostCallback session entry resultType lease next ∈ after.frames) :
    entry.runtime ∈ host.runtimes after.hostState :=
  (run.callbacks valid inventory lawful typed suspensions callbacks).frame_runtime frame

end Execution

namespace Contracts

theorem InvocationStart.callbacks {program : Kernel.Program} {host : Foreign.Model} {function : Function}
    {inputs : List InvocationInput} {state : Execution.State}
    {boundary : InvocationBoundary} (initial : InvocationStart program host function inputs boundary state) : host.CallbacksWellFormed state :=
  initial.2.2.2.2.1

theorem InvocationStart.run_callbacks {program : Kernel.Program} {host : Foreign.Model} {function : Function}
    {inputs : List InvocationInput} {start finish : Execution.State} {trace : List Execution.Event}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (lawful : host.Lawful program) {boundary : InvocationBoundary} (initial : InvocationStart program host function inputs boundary start)
    (run : Execution.Run program host start trace finish) : host.CallbacksWellFormed finish :=
  run.callbacks valid inventory lawful initial.1.1 initial.suspensions initial.callbacks

theorem Observes.callbacks {program : Kernel.Program} {host : Foreign.Model} {function : Function} {observation : Observation}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (lawful : host.Lawful program) (observed : Observes program host function observation) :
    ∃ boundary start finish, InvocationStart program host function observation.input boundary start ∧
      start.world = observation.before ∧ Execution.Run program host start observation.events finish ∧
      finish.world = observation.after ∧ AtOutcome program boundary finish observation.outcome ∧ host.CallbacksWellFormed finish := by
  obtain ⟨boundary,start,finish,initial,before,run,after,outcome⟩ := observed
  exact ⟨boundary,start,finish,initial,before,run.execution,after,outcome,initial.run_callbacks valid inventory lawful run.execution⟩

theorem Diverges.callbacks {program : Kernel.Program} {host : Foreign.Model} {function : Function}
    {inputs : List InvocationInput} {states : Nat → Execution.State} {events : Nat → Option Execution.Event}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (lawful : host.Lawful program) (infinite : Diverges program host function inputs states events) :
    ∀ n, host.CallbacksWellFormed (states n) := by
  obtain ⟨boundary,initial,steps⟩ := infinite
  exact fun n => initial.run_callbacks valid inventory lawful (InvocationRun.prefix steps n).execution

end Contracts

namespace Specification

theorem reachable_callbacks {program : Kernel.Program} {host : Foreign.Model} {function : Function}
    {inputs : List InvocationInput} {state : Execution.State}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (lawful : host.Lawful program) (reachable : (Semantics program host function inputs).Reachable state) :
    host.CallbacksWellFormed state := by
  obtain ⟨start,trace,initial,run⟩ := reachable_execution_iff.mp reachable
  exact initial.run_callbacks valid inventory lawful run

theorem reachable_callback_runtime {program : Kernel.Program} {host : Foreign.Model} {function : Function}
    {inputs : List InvocationInput} {state : Execution.State} {session : Execution.ForeignSession}
    {entry : Execution.CallbackEntry} {resultType : Term} {lease : Option Execution.ReceiverLease} {next : Code}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (lawful : host.Lawful program) (reachable : (Semantics program host function inputs).Reachable state)
    (frame : Execution.Frame.hostCallback session entry resultType lease next ∈ state.frames) :
    entry.runtime ∈ host.runtimes state.hostState :=
  (reachable_callbacks valid inventory lawful reachable).frame_runtime frame

end Specification
end Glorious.Language
