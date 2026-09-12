import GloriousLanguage.SnapshotReplayConstruction
import GloriousLanguage.Effects
import GloriousLanguage.HandoffProgress

/-! Actual replay and cancellation execution. A positive replay request reaches
the real replay step, the real argument handoff, or the honest physical
outcome of the resource it needs: an unplaceable snapshot copy, a copy whose
argument handoff finds no extent, or a final replay whose restored argument
finds no extent. Cancellation executes through its own source admission; this
module grants no replay, copy, extent or cancellation permission. -/
namespace Glorious.Language.Execution

open Kernel

/-- The final replay of one live suspension reaches the actual replay step or
the real exhaustion of the restored argument's temporary home. -/
theorem resumeLast_or_exhausted {program : Kernel.Program} {before : State}
    {caller : Context} {id : Identity} {argument : ResolvedPlace} {suspension : Suspension}
    {value : Value} {layout : Layout}
    (task : before.task = .resume caller id argument false)
    (found : before.resumptions.get id = some suspension)
    (active : ActiveObligation suspension) (last : suspension.remaining = 1)
    (valid : (restoreRoots before.world suspension.homes).WellFormed)
    (stored : (restoreRoots before.world suspension.homes).Stores argument.address value)
    (initialized : value.Initialized)
    (ready : value.MoveReady program (restoreRoots before.world suspension.homes) [argument.address])
    (permission : Permitted (restoreRoots before.world suspension.homes) argument.authority .owned argument.address)
    (request : AllocationRequest program.declarations (restoreRoots before.world suspension.homes)
      suspension.context.region value.type layout) :
    (∃ (destination : Address) (transferred : World), EffectStep program before (some (.replay id true))
      { before with
        world := transferred
        task := .yield suspension.context destination
        frames := suspension.frames ++ [.handler suspension.handler false,.resumed caller] ++ before.frames
        resumptions := before.resumptions.set id
          { suspension with remaining := 0, used := suspension.used+1, active := false } }) ∨
    EffectStep program before (some (.fatal .resource))
      { before with world := restoreRoots before.world suspension.homes, task := .fatal .resource } := by
  rcases Protect.success_or_exhausted valid stored initialized ready permission request with
    ⟨destination,transferred,kept⟩ | exhausted
  · exact Or.inl ⟨destination,transferred,.resumeLast task found active last rfl kept⟩
  · exact Or.inr (.resumeLastExhausted task found active last rfl exhausted)

/-- The copy replay of one live suspension reaches the actual copied replay
step, the real exhaustion of the copied argument's temporary home, or the real
physical exhaustion of the snapshot placement itself. The copied state is the
actual `CopiesSnapshot` of the suspension inventory; no extent, copy or handoff
is assumed. -/
theorem resumeCopy_or_blocked {program : Kernel.Program} {before : State}
    {caller : Context} {id : Identity} {argument : ResolvedPlace} {suspension : Suspension}
    (task : before.task = .resume caller id argument false)
    (well : before.world.WellFormed) (formed : before.SuspensionsWellFormed)
    (found : before.resumptions.get id = some suspension) (active : suspension.active = true)
    (obligation : ActiveObligation suspension) (positive : 1 < suspension.remaining)
    (admission : suspension.PhysicalAdmission program before)
    (copiedWellFormed : ∀ (copied : State) (map : Relocation),
      CopiesSnapshot program before suspension map copied → copied.world.WellFormed)
    (argumentReady : ∀ (copied : State) (map : Relocation),
      CopiesSnapshot program before suspension map copied →
      ∃ (value : Value) (layout : Layout),
        copied.world.Stores argument.address value ∧ value.Initialized ∧
        value.MoveReady program copied.world [argument.address] ∧
        Permitted copied.world argument.authority .owned argument.address ∧
        AllocationRequest program.declarations copied.world (map.context suspension.context).region
          value.type layout) :
    (∃ (map : Relocation) (copied : State) (destination : Address) (transferred : World),
      CopiesSnapshot program before suspension map copied ∧
      EffectStep program before (some (.replay id false))
        { copied with
          world := transferred
          task := .yield (map.context suspension.context) destination
          frames := suspension.frames.map map.frame ++
            [.handler (map.installed suspension.handler) false,.resumed caller] ++ before.frames
          resumptions := before.resumptions.set id
            { suspension with remaining := suspension.remaining-1, used := suspension.used+1 } }) ∨
    (∃ (map : Relocation) (copied : State), CopiesSnapshot program before suspension map copied ∧
      EffectStep program before (some (.fatal .resource)) { copied with task := .fatal .resource }) ∨
    EffectStep program before (some (.fatal .resource)) { before with task := .fatal .resource } := by
  rcases suspension.copiesSnapshot_or_blocked well formed found active admission with
    ⟨table,copied,copiedEq,copying⟩ | blocked
  · subst copiedEq
    obtain ⟨value,layout,stored,initialized,ready,permission,request⟩ :=
      argumentReady _ (suspension.inventory program before table) copying
    rcases Protect.success_or_exhausted (copiedWellFormed _ _ copying) stored initialized ready
      permission request with ⟨destination,transferred,kept⟩ | exhausted
    · exact Or.inl ⟨_,_,destination,transferred,copying,
        .resumeCopy task found obligation positive copying kept⟩
    · exact Or.inr (Or.inl ⟨_,_,copying,
        .resumeCopyExhausted task found obligation positive copying exhausted⟩)
  · exact Or.inr (Or.inr (.resumeCopyBlocked task found obligation positive blocked))

/-- An active resumption with a spent lower budget quantity and its actual
source cancellation admission executes the real cancellation step. -/
theorem cancel_progress {program : Kernel.Program} {before : State}
    {context : Context} {id : Identity} {next : Task} {suspension : Suspension}
    (task : before.task = .cancel context id next)
    (found : before.resumptions.get id = some suspension)
    (active : ActiveObligation suspension) (lower : suspension.quantity.lower = 0)
    (admitted : Cancelable program before.world suspension.roots) :
    EffectStep program before (some (.cancel id))
      { before with
        world := restoreRoots before.world suspension.homes
        task := .cleanup context suspension.roots (CloseRegions (SuspensionRegions suspension) next)
        resumptions := before.resumptions.set id { suspension with active := false, remaining := 0 } } :=
  .cancel task found active lower admitted

end Glorious.Language.Execution
