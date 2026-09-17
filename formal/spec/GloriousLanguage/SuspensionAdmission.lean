import GloriousLanguage.Effects

/-! Capture-to-replay admission accounting. The suspend rules' own admission
(`SuspendPermission`) supplies the replayable roots, the snapshot frames and
the control replayability of the frames it captures. This module projects those
products out of the disposition admission; carrying them to the replay site
along an actual `Run` is `SnapshotReplayProgress`, which also owns the
replay/cancel boundary that consumes them, so this module stays upstream of the
suspension retention chain that performs the carrying. -/
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
  permission.2.2.2.1 bound upper multi

/-- The suspend rules' own admission also supplies the control-replayability of
the frames this share captures: the disposition contract requires every authority
those frames name to be a replayed authority, so the captured control can be
copied. -/
theorem SuspendPermission.controlReplayable {program : Kernel.Program} {world : World}
    {roots : List Identity} {quantity : Quantity} {frames : List Frame}
    (permission : SuspendPermission program world roots quantity frames) :
    ∀ authority ∈ frames.flatMap Frame.authoritySupport, authority.Replayable world :=
  permission.2.2.2.2

end Glorious.Language.Execution
