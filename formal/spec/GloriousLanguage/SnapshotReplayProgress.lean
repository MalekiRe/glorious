import GloriousLanguage.SnapshotReplayConstruction
import GloriousLanguage.Effects
import GloriousLanguage.HandoffProgress
import GloriousLanguage.RehomePreservation

/-! Actual replay and cancellation execution. A positive replay request reaches
the real replay step, the real argument handoff, or the honest physical
outcome of the resource it needs: an unplaceable snapshot copy, a copy whose
argument handoff finds no extent, or a final replay whose restored argument
finds no extent. Cancellation executes through its own source admission; this
module grants no replay, copy, extent or cancellation permission. -/
namespace Glorious.Language.Execution

open _root_.Glorious.Language.Kernel

/-- The actual saved inventory changes only internal suspended homes. Its
original argument therefore keeps every permission, invariant and handoff
support through final restoration. -/
theorem restoreRoots.handoffReady {program : RuntimeProgram} {before : State}
    {id : Identity} {suspension : Suspension} {value : Value} {access : Access} {footprint : List Address}
    (formed : before.SuspensionsWellFormed) (found : before.resumptions.get id = some suspension)
    (active : suspension.active = true) (ready : value.HandoffReady program before.world access footprint) :
    value.HandoffReady program (restoreRoots before.world suspension.homes) access footprint := by
  rw [restoreRoots.eq_rehome]
  apply ready.rehome (roots := suspension.roots)
  · intro key outside root
    rw [(formed.origin id suspension found).home_none outside]
    rfl
  · intro key member root rootAt
    obtain ⟨actual,actualAt,_,suspended⟩ := (formed.active id suspension found active key).mp member
    have same : root = actual := Option.some.inj (rootAt.symm.trans actualAt)
    rw [same,suspended]
    constructor <;> (intro domain equal; cases equal)


/-- The final replay of one live suspension reaches the actual replay step or
the real exhaustion of the restored argument's temporary home, entirely from
the original world and its active capture inventory. -/
theorem resumeLast_or_exhausted {program : Kernel.Program} {before : State}
    {caller : Context} {id : Identity} {argument : ResolvedPlace} {suspension : Suspension}
    {value : Value} {layout : Layout}
    (task : before.task = .resume caller id argument false)
    (found : before.resumptions.get id = some suspension)
    (active : ActiveObligation suspension) (last : suspension.remaining = 1)
    (valid : before.world.WellFormed) (formed : before.SuspensionsWellFormed)
    (stored : before.world.Stores argument.address value) (initialized : value.Initialized)
    (ready : value.MoveReady program before.world [argument.address])
    (permission : Permitted before.world argument.authority .owned argument.address)
    (request : AllocationRequest program.declarations before.world suspension.context.region value.type layout) :
    (∃ (destination : Address) (transferred : World), EffectStep program before (some (.replay id true))
      { before with
        world := transferred
        task := .yield suspension.context destination
        frames := suspension.frames ++ [.handler suspension.handler false,.resumed caller] ++ before.frames
        resumptions := before.resumptions.set id
          { suspension with remaining := 0, used := suspension.used+1, active := false } }) ∨
    EffectStep program before (some (.fatal .resource))
      { before with world := restoreRoots before.world suspension.homes, task := .fatal .resource } := by
  have storedAfter : (restoreRoots before.world suspension.homes).Stores argument.address value := by
    rw [restoreRoots.eq_rehome]
    exact World.rehome_stores.mpr stored
  have readyAfter := restoreRoots.handoffReady formed found active.1 ready
  have permissionAfter : Permitted (restoreRoots before.world suspension.homes) argument.authority .owned argument.address := by
    rw [restoreRoots.eq_rehome]
    exact permission.rehome
  have requestAfter := request.same_regions (after := restoreRoots before.world suspension.homes) rfl rfl
  rcases Protect.success_or_exhausted (context := suspension.context) (restoreRoots.wellFormed valid)
    storedAfter initialized readyAfter permissionAfter requestAfter with ⟨destination,transferred,kept⟩ | exhausted
  · exact Or.inl ⟨destination,transferred,.resumeLast task found active last rfl kept⟩
  · exact Or.inr (.resumeLastExhausted task found active last rfl exhausted)

/-- The copy replay of one live suspension reaches the actual copied replay
step, the real exhaustion of the copied argument's temporary home, or the real
physical exhaustion of the snapshot placement itself. The original argument
supplies storage, readiness, permission and a positive layout request. Actual
shared-loan copying derives its handoff frame and the copied world invariant. -/
theorem resumeCopy_or_blocked {program : Kernel.Program} {before : State}
    {caller : Context} {id : Identity} {argument : ResolvedPlace} {suspension : Suspension}
    {value : Value} {layout : Layout}
    (task : before.task = .resume caller id argument false)
    (well : before.world.WellFormed) (formed : before.SuspensionsWellFormed)
    (found : before.resumptions.get id = some suspension) (active : suspension.active = true)
    (obligation : ActiveObligation suspension) (positive : 1 < suspension.remaining)
    (admission : suspension.PhysicalAdmission program before)
    (stored : before.world.Stores argument.address value) (initialized : value.Initialized)
    (ready : value.MoveReady program before.world [argument.address])
    (permission : Permitted before.world argument.authority .owned argument.address)
    (request : AllocationRequest program.declarations before.world suspension.context.region value.type layout) :
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
    have storedAfter : _ := World.resident_iff_stores.mp
      (Relocation.old_resident (map := suspension.inventory program before table) (homes := suspension.homes)
        (World.resident_iff_stores.mpr stored))
    have readyAfter := copying.old_handoffReady well ready
    have permissionAfter := copying.relocation.old_permitted (homes := suspension.homes) well permission
    have targetLive := Relocation.region_live (map := suspension.inventory program before table)
      (homes := suspension.homes) request.region_live
    have requestAfter := request.retarget targetLive (Nat.le_add_left _ _)
    rcases Protect.success_or_exhausted
      (context := (suspension.inventory program before table).context suspension.context)
      (copying.wellFormed well) storedAfter initialized readyAfter permissionAfter requestAfter with
      ⟨destination,transferred,kept⟩ | exhausted
    · exact Or.inl ⟨_,_,destination,transferred,copying,
        .resumeCopy task found obligation positive copying kept⟩
    · exact Or.inr (Or.inl ⟨_,_,copying,
        .resumeCopyExhausted task found obligation positive copying exhausted⟩)
  · exact Or.inr (Or.inr (.resumeCopyBlocked task found obligation positive blocked))

/-- Every active, accounted ordinary replay with an originally ready argument
has an actual machine step. The budget chooses restoration versus copying;
only the latter asks for the original physical snapshot admission. Failure
retains the exact real allocation prefix provided by the branch theorem. -/
theorem resume_progress {program : Kernel.Program} {before : State}
    {caller : Context} {id : Identity} {argument : ResolvedPlace} {suspension : Suspension}
    {value : Value} {layout : Layout}
    (task : before.task = .resume caller id argument false)
    (well : before.world.WellFormed) (formed : before.SuspensionsWellFormed)
    (found : before.resumptions.get id = some suspension) (active : suspension.active = true)
    (admission : 1 < suspension.remaining → suspension.PhysicalAdmission program before)
    (stored : before.world.Stores argument.address value) (initialized : value.Initialized)
    (ready : value.MoveReady program before.world [argument.address])
    (permission : Permitted before.world argument.authority .owned argument.address)
    (request : AllocationRequest program.declarations before.world suspension.context.region value.type layout) :
    ∃ event after, EffectStep program before (some event) after ∧
      (event = .replay id true ∨ event = .replay id false ∨ event = .fatal .resource) := by
  have accounted := formed.budgets.accounted id suspension found
  have obligation : ActiveObligation suspension :=
    ⟨active,accounted.original,accounted.quantity,(accounted.active active).2⟩
  by_cases last : suspension.remaining = 1
  · rcases resumeLast_or_exhausted task found obligation last well formed stored initialized ready permission request with
      ⟨destination,transferred,step⟩ | exhausted
    · exact ⟨_,_,step,Or.inl rfl⟩
    · exact ⟨_,_,exhausted,Or.inr (Or.inr rfl)⟩
  · have positive : 1 < suspension.remaining := by
      have remaining := (accounted.active active).1
      omega
    rcases resumeCopy_or_blocked task well formed found active obligation positive (admission positive)
      stored initialized ready permission request with
      ⟨map,copied,destination,transferred,copying,step⟩ | ⟨map,copied,copying,exhausted⟩ | blocked
    · exact ⟨_,_,step,Or.inr (Or.inl rfl)⟩
    · exact ⟨_,_,exhausted,Or.inr (Or.inr rfl)⟩
    · exact ⟨_,_,blocked,Or.inr (Or.inr rfl)⟩


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
