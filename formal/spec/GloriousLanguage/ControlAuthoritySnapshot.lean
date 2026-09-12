import GloriousLanguage.ControlAuthorityBranch

/-! Saved control authorities come from the actual routed frames. Replay
uses the same finite relocation that produces the copied loan table; old
unrelocated controls retain their historical records as well. -/
namespace Glorious.Language.Execution

open Kernel

theorem Routes.authority_support {program : Kernel.Program} {before : State}
    {operation : DeclId} {arguments : List Term} {payload : List ResolvedPlace}
    {inner outer : List Frame} {handler : InstalledHandler} {owns : Bool} {arm : OperationArm}
    {loans : Table Loan} (routes : Routes program before operation arguments payload inner handler owns arm outer)
    (recorded : AuthoritySupport.Recorded (before.frames.flatMap Frame.authoritySupport) loans) :
    AuthoritySupport.Recorded (inner.flatMap Frame.authoritySupport) loans ∧
      AuthoritySupport.Recorded handler.authoritySupport loans ∧
      AuthoritySupport.Recorded (outer.flatMap Frame.authoritySupport) loans := by
  rw [routes.1] at recorded
  simpa only [List.flatMap_append,List.flatMap_cons,Frame.authoritySupport,AuthoritySupport.recorded_append] using recorded

theorem EffectStep.created_authority_origin {program : Kernel.Program} {before after : State} {id : Identity}
    (taskRecorded : AuthoritySupport.Recorded before.task.authoritySupport before.world.loans)
    (frameRecorded : AuthoritySupport.Recorded (before.frames.flatMap Frame.authoritySupport) before.world.loans)
    (step : EffectStep program before (some (.suspend id)) after) :
    ∃ suspension, after.resumptions.get id = some suspension ∧
      AuthoritySupport.Recorded suspension.controlAuthoritySupport after.world.loans := by
  cases step with
  | suspend task selected terminal quantity bound continuation routes started keptTransfer roots permission homes created plan suspension =>
    subst suspension
    rw [task] at taskRecorded
    have contextRecorded := (AuthoritySupport.recorded_append.mp taskRecorded).1
    obtain ⟨innerRecorded,handlerRecorded,_⟩ := routes.authority_support frameRecorded
    have transferred := (started.suspensionExtension.trans keptTransfer.suspensionExtension).recorded
    have retained : ∀ (authority : Authority), authority.Recorded before.world.loans → authority.Recorded _ :=
      fun authority recorded => created.suspensionExtension.recorded authority (transferred authority recorded)
    refine ⟨_,Table.get_set _ _ _,?_⟩
    simp only [Suspension.controlAuthoritySupport,AuthoritySupport.recorded_append]
    exact ⟨⟨contextRecorded.mono retained,handlerRecorded.mono retained⟩,innerRecorded.mono retained⟩
  | suspendTailArm task selected terminal quantity bound contains continuation routes started keptTransfer roots permission homes plan suspension =>
    subst suspension
    rw [task] at taskRecorded
    have contextRecorded := (AuthoritySupport.recorded_append.mp taskRecorded).1
    obtain ⟨innerRecorded,handlerRecorded,_⟩ := routes.authority_support frameRecorded
    have retained := (started.suspensionExtension.trans keptTransfer.suspensionExtension).recorded
    refine ⟨_,Table.get_set _ _ _,?_⟩
    simp only [Suspension.controlAuthoritySupport,AuthoritySupport.recorded_append]
    exact ⟨⟨contextRecorded.mono retained,handlerRecorded.mono retained⟩,innerRecorded.mono retained⟩

theorem SnapshotMap.authority_recorded {program : Kernel.Program} {before : State}
    {suspension : Suspension} {map : Relocation} {homes : Table Home} {authority : Authority}
    (well : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (recorded : authority.Recorded before.world.loans) :
    (map.authority authority).Recorded (map.copyWorld before.world homes).loans := by
  induction authority with
  | owner => trivial
  | loan id =>
    obtain ⟨loan,found⟩ := recorded
    by_cases included : id ∈ map.loans
    · exact ⟨_,selected.copied_loan well found included⟩
    · simpa only [Relocation.authority,Authority.Recorded,Relocation.loan,relocateId,included,↓reduceIte]
        using (show ∃ loan, (map.copyWorld before.world homes).loans.get id = some loan from ⟨loan,Relocation.old_loan found⟩)
  | shared backing ih => exact ih recorded

theorem Relocation.context_authority_support {map : Relocation} {context : Context} {before after : Table Loan}
    (mapped : ∀ (authority : Authority), authority.Recorded before → (map.authority authority).Recorded after)
    (recorded : AuthoritySupport.Recorded context.authoritySupport before) :
    AuthoritySupport.Recorded (map.context context).authoritySupport after := by
  simp only [Context.authoritySupport,Relocation.context,List.map_map,Function.comp_def,
    AuthoritySupport.recorded_map] at recorded ⊢
  intro binding member
  exact mapped _ (recorded binding member)

theorem Relocation.installed_authority_support {map : Relocation} {handler : InstalledHandler} {before after : Table Loan}
    (mapped : ∀ (authority : Authority), authority.Recorded before → (map.authority authority).Recorded after)
    (recorded : AuthoritySupport.Recorded handler.authoritySupport before) :
    AuthoritySupport.Recorded (map.installed handler).authoritySupport after := by
  simp only [InstalledHandler.authoritySupport,AuthoritySupport.recorded_append] at recorded
  simp only [Relocation.installed,InstalledHandler.authoritySupport,AuthoritySupport.recorded_append]
  exact ⟨⟨map.context_authority_support mapped recorded.1.1,map.context_authority_support mapped recorded.1.2⟩,
    map.context_authority_support mapped recorded.2⟩

theorem Relocation.frame_authority_support {map : Relocation} {frame : Frame} {before after : Table Loan}
    (retained : ∀ (authority : Authority), authority.Recorded before → authority.Recorded after)
    (mapped : ∀ (authority : Authority), authority.Recorded before → (map.authority authority).Recorded after)
    (recorded : AuthoritySupport.Recorded frame.authoritySupport before) :
    AuthoritySupport.Recorded (map.frame frame).authoritySupport after := by
  cases frame
  all_goals simp only [Relocation.frame,Frame.authoritySupport,AuthoritySupport.recorded_append,
    AuthoritySupport.recorded_cons,AuthoritySupport.recorded_nil] at recorded ⊢
  all_goals first
    | exact map.context_authority_support mapped recorded
    | exact map.installed_authority_support mapped recorded
    | exact ⟨map.installed_authority_support mapped recorded.1,map.context_authority_support mapped recorded.2⟩
    | exact recorded.mono retained
    | trivial
    | skip
  case hook => exact ⟨recorded.1.mono retained,retained _ recorded.2.1,
    retained _ recorded.2.2.1,recorded.2.2.2.mono retained⟩
  case hostCallback => exact ⟨recorded.1.mono retained,recorded.2.mono retained⟩

theorem CopiesSnapshot.authority_support {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation} (well : before.world.WellFormed)
    (copied : CopiesSnapshot program before suspension map after)
    (recorded : AuthoritySupport.Recorded suspension.controlAuthoritySupport before.world.loans) :
    AuthoritySupport.Recorded (map.context suspension.context).authoritySupport after.world.loans ∧
      AuthoritySupport.Recorded (map.installed suspension.handler).authoritySupport after.world.loans ∧
      AuthoritySupport.Recorded ((suspension.frames.map map.frame).flatMap Frame.authoritySupport) after.world.loans := by
  simp only [Suspension.controlAuthoritySupport,AuthoritySupport.recorded_append] at recorded
  rw [copied.result]
  have mapped := fun authority recorded => copied.relocation.authority_recorded
    (authority := authority) (homes := suspension.homes) well recorded
  have retained : ∀ (authority : Authority), authority.Recorded before.world.loans →
      authority.Recorded (map.copyWorld before.world suspension.homes).loans :=
    fun _ recorded => recorded.transport (fun _ loan found => ⟨loan,Relocation.old_loan found⟩)
  refine ⟨map.context_authority_support mapped recorded.1.1,map.installed_authority_support mapped recorded.1.2,?_⟩
  rw [AuthoritySupport.recorded_flatMap]
  intro frame member
  obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
  exact map.frame_authority_support retained mapped (AuthoritySupport.recorded_flatMap.mp recorded.2 original originalMember)

theorem Step.saved_authority_origin {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (suspensions : before.SuspensionsWellFormed)
    (taskRecorded : AuthoritySupport.Recorded before.task.authoritySupport before.world.loans)
    (frameRecorded : AuthoritySupport.Recorded (before.frames.flatMap Frame.authoritySupport) before.world.loans)
    (saved : ∀ id suspension, before.resumptions.get id = some suspension →
      AuthoritySupport.Recorded suspension.controlAuthoritySupport before.world.loans)
    (step : Step program host before event after) :
    ∀ id suspension, after.resumptions.get id = some suspension →
      AuthoritySupport.Recorded suspension.controlAuthoritySupport after.world.loans := by
  have retained := (step.suspension_storage valid inventory lawful typed suspensions).2
  apply step.resumption_change.saved_property (fun _ _ _ _ recorded => recorded)
    (fun id suspension found => (saved id suspension found).mono retained)
  intro id equal
  rcases step with localStep | atom | effect | controlStep | primitive | foreign
  · cases localStep <;> cases equal
  · cases atom <;> simp_all <;> split at equal <;> (try split at equal) <;> contradiction
  · rw [equal] at effect
    exact effect.created_authority_origin taskRecorded frameRecorded
  · cases controlStep <;> cases equal
  · cases primitive <;> cases equal
  · cases foreign <;> cases equal

end Glorious.Language.Execution
