import GloriousLanguage.InvocationLifecycle
import GloriousLanguage.ResumptionPreservation

/-! Escaped lifecycle identity is authenticated by actual capture and the
existing quantitative/metadata preservation theorem. A same-number table
entry cannot replace the original invocation's context, frames or homes. -/
namespace Glorious.Language.Contracts

open Kernel Execution

theorem EscapedCapture.created {program : Kernel.Program} {host : Foreign.Model}
    {function : Function} {request : Observation} {continuation : Identity} {captured : State}
    (escaped : EscapedCapture program host function request continuation captured) :
    captured.ResumptionsAccounted ∧ ∃ suspension,
      captured.resumptions.get continuation = some suspension ∧ suspension.identity = continuation ∧
      suspension.original = true ∧ suspension.active = true ∧ suspension.used = 0 := by
  obtain ⟨boundary,start,pending,_,_,_,observed,_,capture⟩ := escaped
  obtain ⟨initial,_,run,_,_⟩ := observed
  have accounted := run.execution.resumptions_accounted initial.resumptions_accounted
  exact ⟨capture.resumption_change.accounted accounted,capture.resumption_change.suspend_created.2⟩

/-- A cancellation observation cancels the continuation created by this
invocation's actual outward request. Its saved origin is unchanged through
arbitrary intervening caller execution and any permitted copied replays. -/
theorem LifecycleObserves.cancellation_origin {program : Kernel.Program} {host : Foreign.Model}
    {function : Function} {observation : LifecycleObservation}
    (observed : LifecycleObserves program host function observation)
    (canceled : observation.outcome = .cancellationStarted) :
    ∃ captured original canceling current finish events,
      EscapedCapture program host function observation.request observation.continuation captured ∧
      captured.resumptions.get observation.continuation = some original ∧
      original.active = true ∧ original.used = 0 ∧
      observation.callerEvents = .suspend observation.continuation :: events ++ [.cancel observation.continuation] ∧
      Run program host captured events canceling ∧
      canceling.resumptions.get observation.continuation = some current ∧
      current = { original with remaining := current.remaining, used := current.used, active := current.active } ∧
      current.active = true ∧ original.quantity.lower = 0 ∧
      EffectStep program canceling (some (.cancel observation.continuation)) finish ∧
      finish.resumptions.get observation.continuation = some { current with remaining := 0, active := false } ∧
      observation.after = finish.world := by
  obtain ⟨captured,escaped,lifecycle⟩ := observed
  simp only [LifecycleAt,canceled] at lifecycle
  obtain ⟨events,canceling,finish,trace,later,cancel,after⟩ := lifecycle
  obtain ⟨accounted,original,created,_,_,active,used⟩ := escaped.created
  obtain ⟨current,present,origin⟩ := later.retains_origin accounted created
  obtain ⟨actual,actualAt,currentActive,optional,settled⟩ := cancel.resumption_change.cancel_started
  have same := Option.some.inj (present.symm.trans actualAt)
  subst actual
  have quantity : current.quantity = original.quantity := by
    have projected := congrArg (fun (suspension : Suspension) => suspension.quantity) origin
    exact projected
  exact ⟨captured,original,canceling,current,finish,events,escaped,created,active,used,trace,later,present,
    origin,currentActive,quantity ▸ optional,cancel,settled,after⟩

end Glorious.Language.Contracts
