import GloriousLanguage.SuspensionOrigins
import GloriousLanguage.SuspensionStorage

/-! Primitive execution preserves captured storage ownership through its real
allocation and memory producers. Raw mutation may change values, but cannot
invent suspended homes or retire storage still owned by a suspension. -/
namespace Glorious.Language

open Kernel Execution Memory

/-- A region end only trims `liveRegions`, so it retains every location. -/
theorem RegionEnds.suspensionExtension {before after : World} {region : Identity}
    (ended : RegionEnds before region after) : before.SuspensionExtension after := by
  obtain ⟨_,same⟩ := ended
  subst same
  exact World.SuspensionExtension.of_locations (Nat.le_refl _) (fun id => rfl)
    (fun _ recorded => recorded)

theorem Memory.AllocatesBuffer.suspensionExtension {program : Program} {custody : ClaimCustody}
    {before after : World} {domain : Identity} {element : Term} {count base : Nat} {pointer : RawPointer}
    {place : ResolvedPlace}
    (allocated : AllocatesBuffer program custody before domain element count base pointer place after) :
    before.SuspensionExtension after := by
  cases allocated with
  | fresh request extent =>
    refine ⟨⟨Nat.le_succ _,?_⟩,?_,?_,?_⟩
    · intro id bound
      simp only [Table.get_set_other _ _ _ _ (Nat.ne_of_lt bound)]
    · intro id root suspension bound found home
      rw [Table.get_set_other _ _ _ _ (Nat.ne_of_lt bound),found]
      rfl
    · intro id root suspension found home
      by_cases same : id = before.nextRoot
      · subst same
        rw [Table.get_set] at found
        have equal := Option.some.inj found
        rw [← equal] at home
        cases home
      · exact ⟨root,by simpa only [Table.get_set_other _ _ _ _ same] using found,rfl⟩
    · intro authority recorded
      exact Authority.Recorded.set recorded _ _

theorem Memory.BulkMove.suspensionExtension {program : RuntimeProgram} {before after : World} {sources destinations}
    (moved : BulkMove program before sources destinations after) : before.SuspensionExtension after := by
  have counter := moved.authorityStable.homes.counter
  have recorded := moved.authorityStable.recorded
  obtain ⟨_,_,_,_,_,_,_,_,cleared,installed⟩ := moved
  exact .of_locations counter (fun id => (installed.locations id).trans (cleared.locations id)) recorded

/-- Releasing storage claims only rewrites the loan table. -/
theorem ReleasesStorageClaims.suspensionExtension {before after : World} {place : ResolvedPlace}
    (released : ReleasesStorageClaims before place after) : before.SuspensionExtension after := by
  refine ⟨released.homeExtension,?_,?_,released.recorded⟩
  · intro id root suspension bound found home
    cases released
    exact congrArg (Option.map Root.location) found
  · intro id root suspension found home
    cases released
    exact ⟨root,found,rfl⟩

theorem Memory.ReleasesBuffer.suspensionExtension {program : Program} {before after : World}
    {place : ResolvedPlace} {pointer : RawPointer} {domain : Identity}
    (released : ReleasesBuffer program before place pointer domain after) : before.SuspensionExtension after := by
  cases released with
  | release =>
    rename_i value rootv unclaimed cleared retired bufferAt rootAt shellLive resourcesEmpty fieldsNone claims safe written retires ended
    exact (claims.suspensionExtension.trans (World.write_suspensionExtension written)).trans
      (retires.suspensionExtension.trans (RegionEnds.suspensionExtension ended))

theorem Memory.ReallocatesBuffer.suspensionExtension {program : RuntimeProgram} {custody : ClaimCustody}
    {before after : World} {oldAllocation allocation : ResolvedPlace} {old : RawPointer}
    {domain : Identity} {element : Term} {count base : Nat} {result : RawPointer}
    (reallocated : ReallocatesBuffer program custody before oldAllocation old domain element count base result allocation after) :
    before.SuspensionExtension after := by
  cases reallocated with
  | grow =>
    rename_i oldCount allocated moved ready bulkMove allocatedRun released
    exact (Memory.AllocatesBuffer.suspensionExtension allocatedRun).trans
      ((bulkMove.suspensionExtension).trans (released.suspensionExtension))

theorem Memory.RawRead.suspensionExtension {program : RuntimeProgram} {before after : World}
    {source : ResolvedPlace} {pointer : RawPointer} {type : Term} {copy : Bool} {destination : Address}
    (read : RawRead program before source pointer type copy destination after) : before.SuspensionExtension after := by
  cases read with
  | read =>
    rename_i points layout range action
    rcases action with ⟨_,copied⟩ | ⟨_,moved⟩
    · exact copied.suspensionExtension
    · exact moved.suspensionExtension

theorem Memory.RawWrite.suspensionExtension {program : RuntimeProgram} {before after : World}
    {source destination : ResolvedPlace} {pointer : RawPointer} {type : Term}
    (written : RawWrite program before source destination pointer type after) : before.SuspensionExtension after := by
  cases written with
  | write =>
    rename_i stored typeEq points layoutOf range permitted moved
    exact moved.suspensionExtension

theorem Memory.RawBorrow.suspensionExtension {program : RuntimeProgram} {before after : World}
    {source : ResolvedPlace} {pointer : RawPointer} {type : Term} {mode : Mutability} {region : Identity}
    {destination : Address}
    (borrowed : RawBorrow program before source pointer type mode region destination after) : before.SuspensionExtension after := by
  cases borrowed with
  | borrow =>
    rename_i points range admitted occupied formed
    exact formed.suspensionExtension

namespace Execution

/-- All successful and fatal primitive branches preserve the same captured
root relation; no primitive-specific post-state certificate is introduced. -/
theorem PrimitiveStep.suspensionExtension {program : Kernel.Program} {before after : State} {event : Option Event}
    (step : PrimitiveStep program before event after) : before.world.SuspensionExtension after.world := by
  cases step with
  | scalar _ _ _ _ stored => exact stored.2.2.suspensionExtension
  | scalarFault => exact .refl _
  | allocate _ _ _ _ _ allocated stored => exact allocated.suspensionExtension.trans stored.2.suspensionExtension
  | release _ _ _ _ _ released stored => exact released.suspensionExtension.trans stored.2.suspensionExtension
  | reallocate _ _ _ _ _ _ _ reallocated stored =>
    exact reallocated.suspensionExtension.trans stored.2.suspensionExtension
  | reallocateExhausted _ _ _ _ _ _ _ => exact .refl _
  | allocateExhausted _ _ _ _ _ => exact .refl _
  | rawRead _ _ _ _ read => exact read.suspensionExtension
  | rawCopy _ _ _ _ read => exact read.suspensionExtension
  | rawWrite _ _ _ _ written stored => exact written.suspensionExtension.trans stored.2.suspensionExtension
  | rawMove _ _ _ _ _ _ _ _ _ moved stored => exact moved.suspensionExtension.trans stored.2.suspensionExtension
  | rawBorrow _ _ _ _ borrowed => exact borrowed.suspensionExtension
  | pointerOffset _ _ _ _ _ stored => exact stored.2.suspensionExtension
  | pointerAddress _ _ _ stored => exact stored.2.2.suspensionExtension
  | pointerWithAddress _ _ _ _ _ _ stored => exact stored.2.suspensionExtension
  | layout _ _ _ _ _ written _ =>
    have changed := World.write_suspensionExtension written
    exact ⟨⟨changed.counter,changed.homes⟩,changed.retained,changed.origin,changed.recorded⟩
  | literalText _ _ _ _ _ _ written | literalBytes _ _ _ _ _ _ written =>
    have changed := World.write_suspensionExtension written
    exact ⟨⟨changed.counter,changed.homes⟩,changed.retained,changed.origin,changed.recorded⟩
  | abort => exact .refl _

theorem PrimitiveStep.suspensions {program : Kernel.Program} {before after : State} {event : Option Event}
    (well : before.world.WellFormed) (suspensions : before.SuspensionsWellFormed)
    (step : PrimitiveStep program before event after) : after.SuspensionsWellFormed := by
  apply suspensions.transport well step.suspensionExtension
  · cases step <;> rfl
  · cases step <;> exact Nat.le_refl _

end Execution
end Glorious.Language
