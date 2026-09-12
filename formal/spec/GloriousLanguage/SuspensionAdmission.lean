import GloriousLanguage.SnapshotReplayProgress

/-! Capture-to-replay admission accounting. The suspend rules' own admission
(`SuspendPermission`) supplies the replayable roots and the snapshot frames of
the suspension they create, and the actual resumption table change of every
step retains the created suspension's captured product (roots, saved homes,
frames, handler, context, inner frames, control authorities, quantity and
capture limit). This module derives those parts from the real producers and
retains them along an actual `Run`; it does not restate them at replay. -/
namespace Glorious.Language.Execution

open Kernel

/-- The suspend rules' own admission supplies the two suspension-building
components of the physical admission: the captured roots are replayable and
every frame of the suspension is a snapshot frame, as soon as the accepted
quantity really is multi-shot. -/
theorem SuspendPermission.replayable_frames {program : Kernel.Program} {world : World}
    {roots : List Identity} {quantity : Quantity} {frames : List Frame} {bound : Nat}
    (permission : SuspendPermission program world roots quantity frames)
    (upper : quantity.upper = some bound) (multi : 1 < bound) :
    Replayable program world roots ∧ ∀ frame ∈ frames, SnapshotFrame frame :=
  permission.2.2.2 bound upper multi

end Glorious.Language.Execution
