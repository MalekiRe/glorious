import GloriousLanguage.Contracts

/-! Escaped continuation observations are tied to the actual outward
invocation request and its caller-side capture. Internal lifecycle events
remain in the invocation trace. The combined execution below is the original
machine run, while its caller events retain their separate attribution. -/
namespace Glorious.Language.Contracts

open Kernel Execution

/-- The real capture of this exact request constructs its suspended lifecycle.
This constructor is used by handler progress; it cannot be supplied by an
unrelated same-key suspension table entry. -/
theorem ObservationAt.capture_lifecycle {program : Kernel.Program} {host : Foreign.Model}
    {function : Function} {boundary : InvocationBoundary} {start pending captured : State}
    {request : Observation} {id : DeclId} {arguments : List Term} {payload : List ResolvedPlace}
    {continuation : Identity}
    (observed : ObservationAt program host function boundary start pending request)
    (outcome : request.outcome = .operation id arguments payload)
    (capture : EffectStep program pending (some (.suspend continuation)) captured) :
    LifecycleObserves program host function ⟨request,continuation,[.suspend continuation],captured.world,.suspended⟩ :=
  ⟨captured,⟨boundary,start,pending,id,arguments,payload,observed,outcome,capture⟩,rfl,rfl⟩

theorem EscapedCapture.request_observed {program : Kernel.Program} {host : Foreign.Model}
    {function : Function} {request : Observation} {continuation : Identity} {captured : State}
    (escaped : EscapedCapture program host function request continuation captured) :
    Observes program host function request := by
  obtain ⟨boundary,start,pending,_,_,_,observed,_,_⟩ := escaped
  exact ⟨boundary,start,pending,observed⟩

/-- The capture event is after the invocation's outward request, not an
unrelated event selected from a table or from the caller's earlier execution. -/
theorem EscapedCapture.execution {program : Kernel.Program} {host : Foreign.Model}
    {function : Function} {request : Observation} {continuation : Identity} {captured : State}
    (escaped : EscapedCapture program host function request continuation captured) :
    ∃ boundary start, InvocationStart program host function request.input boundary start ∧
      start.world = request.before ∧
      Run program host start (request.events ++ [.suspend continuation]) captured := by
  obtain ⟨boundary,start,pending,_,_,_,observed,_,capture⟩ := escaped
  obtain ⟨initial,before,run,_,_⟩ := observed
  exact ⟨boundary,start,initial,before,run.execution.append
    (.visible (Or.inr (Or.inr (Or.inl capture))) .refl)⟩

theorem LifecycleObserves.request_observed {program : Kernel.Program} {host : Foreign.Model}
    {function : Function} {observation : LifecycleObservation}
    (observed : LifecycleObserves program host function observation) :
    Observes program host function observation.request := by
  obtain ⟨_,escaped,_⟩ := observed
  exact escaped.request_observed

/-- The separate invocation/caller trace fields compose to one actual run.
Cancellation initiation includes the real same-key cancel transition; physical
destructor completion is not inferred from its inactive resumption-table bit. -/
theorem LifecycleObserves.execution {program : Kernel.Program} {host : Foreign.Model}
    {function : Function} {observation : LifecycleObservation}
    (observed : LifecycleObserves program host function observation) :
    ∃ boundary start finish,
      InvocationStart program host function observation.request.input boundary start ∧
      start.world = observation.request.before ∧
      Run program host start (observation.request.events ++ observation.callerEvents) finish ∧
      finish.world = observation.after := by
  obtain ⟨captured,escaped,lifecycle⟩ := observed
  obtain ⟨boundary,start,initial,before,run⟩ := escaped.execution
  cases outcome : observation.outcome with
  | suspended =>
    simp only [LifecycleAt,outcome] at lifecycle
    obtain ⟨events,after⟩ := lifecycle
    exact ⟨boundary,start,captured,initial,before,by simpa only [events] using run,after.symm⟩
  | cancellationStarted =>
    simp only [LifecycleAt,outcome] at lifecycle
    obtain ⟨events,canceling,finish,callerEvents,later,cancel,after⟩ := lifecycle
    have suffix : Run program host captured (events ++ [.cancel observation.continuation]) finish :=
      later.append (.visible (Or.inr (Or.inr (Or.inl cancel))) .refl)
    refine ⟨boundary,start,finish,initial,before,?_,after.symm⟩
    simpa only [callerEvents,List.append_assoc,List.cons_append,List.nil_append] using run.append suffix

end Glorious.Language.Contracts
