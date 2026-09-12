import GloriousLanguage.SuspensionContent
import GloriousLanguage.ResumptionPreservation
import GloriousLanguage.ControlOrigin

/-! Capture product retention. The actual resumption-table change of every step
retains the whole captured product of a suspension stored before it: its roots,
saved homes, frames, handler, context, control authorities and budgets. This
consumes the authoritative `ResumptionChange.retains_metadata` producer rather
than restating it, and adds the control-authority projection the replay
admission consumes. -/
namespace Glorious.Language

open Kernel

namespace Execution

/-- The stored row of a suspension retains its complete captured product along
an actual resumption change. -/
theorem ResumptionChange.stored_product {before after : State} {event : Option Event}
    {id : Identity} {suspension : Suspension}
    (change : ResumptionChange before event after) (valid : before.ResumptionsAccounted)
    (found : before.resumptions.get id = some suspension) :
    ∃ current, after.resumptions.get id = some current ∧ current.roots = suspension.roots ∧
      current.homes = suspension.homes ∧ current.frames = suspension.frames ∧
      current.handler = suspension.handler ∧ current.context = suspension.context ∧
      current.controlAuthoritySupport = suspension.controlAuthoritySupport ∧
      current.quantity = suspension.quantity ∧ current.captureRootLimit = suspension.captureRootLimit ∧
      (current.frames = suspension.frames) := by
  obtain ⟨current,present,quantity,roots,homes,limit,context,handler,frames,inactive⟩ :=
    change.retains_metadata valid found
  refine ⟨current,present,roots,homes,frames,handler,context,?_⟩
  exact ⟨by simp only [Suspension.controlAuthoritySupport,context,handler,frames],quantity,limit,frames⟩

/-- The stored capture product, including the control authorities the replay
admission consumes, survives an arbitrary actual step. -/
theorem Step.stored_product {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {event : Option Event} {id : Identity} {suspension : Suspension}
    (step : Step program host before event after) (valid : before.ResumptionsAccounted)
    (found : before.resumptions.get id = some suspension) :
    ∃ current, after.resumptions.get id = some current ∧ current.roots = suspension.roots ∧
      current.homes = suspension.homes ∧ current.frames = suspension.frames ∧
      current.handler = suspension.handler ∧ current.context = suspension.context ∧
      current.controlAuthoritySupport = suspension.controlAuthoritySupport ∧
      current.quantity = suspension.quantity ∧ current.captureRootLimit = suspension.captureRootLimit := by
  obtain ⟨current,present,roots,homes,frames,handler,context,authorities,quantity,limit,_⟩ :=
    step.resumption_change.stored_product valid found
  exact ⟨current,present,roots,homes,frames,handler,context,authorities,quantity,limit⟩

/-- The same retention along an actual run: the suspension created by the real
capture is still the stored row at replay, with the same captured product. -/
theorem Run.stored_product {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event} {id : Identity} {suspension : Suspension}
    (run : Run program host before trace after) (valid : before.ResumptionsAccounted)
    (found : before.resumptions.get id = some suspension) :
    ∃ current, after.resumptions.get id = some current ∧ current.roots = suspension.roots ∧
      current.homes = suspension.homes ∧ current.frames = suspension.frames ∧
      current.handler = suspension.handler ∧ current.context = suspension.context ∧
      current.controlAuthoritySupport = suspension.controlAuthoritySupport ∧
      current.quantity = suspension.quantity ∧ current.captureRootLimit = suspension.captureRootLimit := by
  obtain ⟨current,present,quantity,roots,homes,limit,context,handler,frames,inactive⟩ :=
    run.retains_metadata valid found
  exact ⟨current,present,roots,homes,frames,handler,context,
    by simp only [Suspension.controlAuthoritySupport,context,handler,frames],quantity,limit⟩

/-- Snapshot frames are a property of the stored frames themselves, so they are
retained whenever the frames are. -/
theorem Run.stored_snapshotFrames {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event} {id : Identity} {suspension : Suspension}
    (run : Run program host before trace after) (valid : before.ResumptionsAccounted)
    (found : before.resumptions.get id = some suspension)
    (snapshot : ∀ frame ∈ suspension.frames, SnapshotFrame frame) :
    ∃ current, after.resumptions.get id = some current ∧ ∀ frame ∈ current.frames, SnapshotFrame frame := by
  obtain ⟨current,present,_,_,frames,_,_,_,_,_⟩ := run.stored_product valid found
  exact ⟨current,present,by rwa [frames]⟩

/-- The control authorities of a stored suspension are recorded in the current
loan table: the real `ControlWellFormed` invariant of the actual state. -/
theorem Suspension.controlAuthorities_recorded {state : State} (control : state.ControlWellFormed)
    {id : Identity} {suspension : Suspension} (found : state.resumptions.get id = some suspension) :
    AuthoritySupport.Recorded suspension.controlAuthoritySupport state.world.loans :=
  control.savedAuthorities id suspension found

/-- No root allocated at or after the capture can be a captured root: the real
capture bound precedes the current frontier of the actual world. This is the
producer that keeps freshly allocated storage (in particular the continuation
handle) outside every active suspension's inventory. -/
theorem Suspension.captured_below {state : State} {id : Identity} {suspension : Suspension}
    (formed : state.SuspensionsWellFormed) (found : state.resumptions.get id = some suspension)
    {root : Identity} (member : root ∈ suspension.roots) : root < suspension.captureRootLimit :=
  (formed.origin id suspension found).bounded root member

theorem Suspension.captured_below_frontier {state : State} {id : Identity} {suspension : Suspension}
    (formed : state.SuspensionsWellFormed) (found : state.resumptions.get id = some suspension)
    {root : Identity} (member : root ∈ suspension.roots) : root < state.world.nextRoot :=
  Nat.lt_of_lt_of_le (Suspension.captured_below formed found member)
    (formed.frontier id suspension found)

/-- A captured root's storage region is live in the current world: the actual
world well-formedness law of live roots, consumed for the roots an active
suspension owns. -/
theorem Suspension.capturedRegion_live {before : State} {id : Identity} {suspension : Suspension}
    (well : before.world.WellFormed) (formed : before.SuspensionsWellFormed)
    (found : before.resumptions.get id = some suspension) (active : suspension.active = true)
    {rootId region : Identity} {root : Root}
    (member : rootId ∈ suspension.roots) (rootAt : before.world.roots.get rootId = some root)
    (regionAt : root.region = region) : region ∈ before.world.liveRegions := by
  have ownership := (formed.active id suspension found active rootId).mp member
  obtain ⟨actual,actualAt,live,_⟩ := ownership
  have same : root = actual := Option.some.inj (rootAt.symm.trans actualAt)
  subst same
  rw [← regionAt]
  exact (well.2.2.2.2.2.2.2.2.1 rootId root rootAt).2.1 live

end Execution
end Glorious.Language
