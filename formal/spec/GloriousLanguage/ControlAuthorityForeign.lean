import GloriousLanguage.ControlAuthorityEffect

/-! Primitive and foreign control retains actual recorded authorities.
Fresh host exposure is owner authority; callback inputs and hidden leases
are supplied by the ordinary permission and lending producers. -/
namespace Glorious.Language.Execution

open Kernel

theorem PrimitiveStep.authority_support {program : Kernel.Program} {before after : State} {event : Option Event}
    (taskRecorded : AuthoritySupport.Recorded before.task.authoritySupport before.world.loans)
    (frameRecorded : AuthoritySupport.Recorded (before.frames.flatMap Frame.authoritySupport) before.world.loans)
    (step : PrimitiveStep program before event after) :
    AuthoritySupport.Recorded after.task.authoritySupport after.world.loans ∧
      AuthoritySupport.Recorded (after.frames.flatMap Frame.authoritySupport) after.world.loans := by
  have retained := step.suspensionExtension.recorded
  have taskAfter := taskRecorded.mono retained
  have framesAfter := frameRecorded.mono retained
  cases step <;> simp_all only [Task.authoritySupport,AuthoritySupport.recorded_append,AuthoritySupport.recorded_nil,true_and]

theorem CaptureInputs.authority_support {world : World} {receiver : Address} {authority : Authority} {access : Access}
    {formals : List Local} {inputs : List InvocationInput}
    (prepared : CaptureInputs world receiver authority access formals inputs) :
    AuthoritySupport.Recorded (inputs.map InvocationInput.authority) world.loans := by
  rw [AuthoritySupport.recorded_map]
  intro input member
  exact (prepared.2 input member).2.recorded

theorem ForeignSession.known_authority_support {session : ForeignSession} {loans : Table Loan}
    (recorded : AuthoritySupport.Recorded session.authoritySupport loans) :
    AuthoritySupport.Recorded (session.known.map ResolvedPlace.authority) loans := by
  simp only [ForeignSession.authoritySupport,AuthoritySupport.recorded_append] at recorded
  simp only [ForeignSession.known,List.map_append,List.map_map,Function.comp_def,
    AuthoritySupport.recorded_append,AuthoritySupport.recorded_map,Authority.Recorded]
  exact ⟨by simp,AuthoritySupport.recorded_map.mp recorded.2⟩

theorem ForeignSession.returned_authority_support {session : ForeignSession} {result : Address} {state : List Nat}
    {loans : Table Loan} (recorded : AuthoritySupport.Recorded session.authoritySupport loans) :
    AuthoritySupport.Recorded (session.returned result state).authoritySupport loans := by
  simp only [ForeignSession.authoritySupport,AuthoritySupport.recorded_append] at recorded
  simp only [ForeignSession.returned,ForeignSession.authoritySupport,List.map_cons,
    AuthoritySupport.recorded_append,AuthoritySupport.recorded_cons,Authority.Recorded,true_and]
  exact recorded

end Glorious.Language.Execution

namespace Glorious.Language.Foreign

open Kernel Execution

theorem CallbackInputs.authority_support {world : World} {formals : List Local}
    {arguments : List ResolvedPlace} {inputs : List InvocationInput}
    (prepared : CallbackInputs world formals arguments inputs) :
    AuthoritySupport.Recorded (inputs.map InvocationInput.authority) world.loans := by
  rw [AuthoritySupport.recorded_map]
  intro input member
  rw [prepared.1] at member
  obtain ⟨⟨⟨formal,argument⟩,index⟩,pairMember,rfl⟩ := List.mem_map.mp member
  have argumentAt := (List.getElem?_zip_eq_some.mp (List.mem_zipIdx_iff_getElem?.mp pairMember)).2
  obtain ⟨_,_,_,_,_,_,permission⟩ := prepared.2.get_right argumentAt
  exact permission.recorded

theorem AmbientExposed.authority_support {frames : List Frame} {loans : Table Loan}
    (recorded : AuthoritySupport.Recorded (frames.flatMap Frame.authoritySupport) loans) :
    AuthoritySupport.Recorded ((AmbientExposed frames).map ResolvedPlace.authority) loans := by
  induction frames with
  | nil => simp [AmbientExposed]
  | cons frame rest ih =>
    simp only [List.flatMap_cons,AuthoritySupport.recorded_append] at recorded
    cases frame <;> simp only [AmbientExposed,List.flatMap_cons,List.nil_append,List.map_append]
    all_goals try exact ih recorded.2
    exact AuthoritySupport.recorded_append.mpr
      ⟨ForeignSession.known_authority_support (AuthoritySupport.recorded_append.mp recorded.1).1,ih recorded.2⟩

theorem FreshExposed.authority_support {before after : World} {loans : Table Loan} :
    AuthoritySupport.Recorded ((FreshExposed before after).map ResolvedPlace.authority) loans := by
  rw [AuthoritySupport.recorded_map]
  intro place exposed
  obtain ⟨⟨id,root⟩,member,selected⟩ := List.mem_filterMap.mp exposed
  dsimp only at selected
  split at selected
  · cases selected
    trivial
  · cases selected

theorem _root_.Glorious.Language.Execution.ForeignSession.advance_authority_support
    {session : ForeignSession} {before after : World} {state : List Nat} {loans : Table Loan}
    (recorded : AuthoritySupport.Recorded session.authoritySupport loans) :
    AuthoritySupport.Recorded (session.advance before after state).authoritySupport loans := by
  simp only [ForeignSession.authoritySupport,AuthoritySupport.recorded_append] at recorded
  simp only [ForeignSession.advance,ForeignSession.authoritySupport,List.map_append,AuthoritySupport.recorded_append]
  exact ⟨recorded.1,recorded.2,FreshExposed.authority_support⟩

theorem CallbackReturnTask.authority_support {session : ForeignSession} {registration : Identity} {result : Address}
    {lease : Option ReceiverLease} {next : Code} {loans : Table Loan}
    (recorded : AuthoritySupport.Recorded session.authoritySupport loans) :
    AuthoritySupport.Recorded (CallbackReturnTask session registration result lease next).authoritySupport loans := by
  cases lease with
  | none => exact recorded
  | some lease =>
    have contextRecorded := (AuthoritySupport.recorded_append.mp recorded).1
    simp only [CallbackReturnTask,Task.authoritySupport,AuthoritySupport.recorded_append,
      AuthoritySupport.recorded_cons,Authority.Recorded,true_and]
    exact ⟨contextRecorded,recorded⟩

theorem Step.authority_support {program : Kernel.Program} {model : Model} {before after : State} {event : Option Event}
    (lawful : model.Lawful program) (well : before.world.WellFormed)
    (taskRecorded : AuthoritySupport.Recorded before.task.authoritySupport before.world.loans)
    (frameRecorded : AuthoritySupport.Recorded (before.frames.flatMap Frame.authoritySupport) before.world.loans)
    (step : Step program model before event after) :
    AuthoritySupport.Recorded after.task.authoritySupport after.world.loans ∧
      AuthoritySupport.Recorded (after.frames.flatMap Frame.authoritySupport) after.world.loans := by
  have retained := (step.suspensionExtension lawful well).recorded
  have taskAfter := taskRecorded.mono retained
  have framesAfter := frameRecorded.mono retained
  cases step
  all_goals simp_all only [Task.authoritySupport,Frame.authoritySupport,EntrySource.authoritySupport,
    List.flatMap_cons,List.map_append,AuthoritySupport.recorded_append,
    AuthoritySupport.recorded_nil,and_true]
  case enter kept _ _ _ => exact AuthoritySupport.recorded_append.mpr ⟨taskAfter.1,AmbientExposed.authority_support framesAfter⟩
  case host => exact ForeignSession.advance_authority_support taskAfter
  case result => exact (AuthoritySupport.recorded_append.mp taskAfter).1
  case callback selected active transition _ _ _ _ _ _ _ _ _ lent captures inputs consumed =>
    have hostRetained := (lawful.host_suspensionExtension well selected active transition).recorded
    have hostToFinal := (lent.suspensionExtension.trans consumed.suspensionExtension).recorded
    have contextRecorded := (AuthoritySupport.recorded_append.mp taskAfter).1
    refine ⟨⟨contextRecorded,captures.authority_support.mono consumed.suspensionExtension.recorded,
      inputs.authority_support.mono consumed.suspensionExtension.recorded⟩,?_,
      lent.lease_authority_recorded.mono consumed.suspensionExtension.recorded⟩
    exact (ForeignSession.advance_authority_support (taskRecorded.mono hostRetained)).mono hostToFinal
  case callbackResult => exact CallbackReturnTask.authority_support framesAfter.1.1
  case callbackReturned => exact ForeignSession.returned_authority_support taskRecorded

end Glorious.Language.Foreign
