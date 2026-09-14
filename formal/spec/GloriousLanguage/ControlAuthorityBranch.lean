import GloriousLanguage.ControlAuthorityLocal

/-! Dynamic labels and reservation disposal consume the same recorded
authority provenance as ordinary invocation. Even vacant reserved storage
must not introduce an unrecorded loan into a scheduled cleanup task. -/
namespace Glorious.Language.Execution

open _root_.Glorious.Language.Kernel

theorem LabelRoute.authority_support {frames inner outer : List Frame} {brand region : Identity}
    {context : Context} {type : Term} {loans : Table Loan}
    (route : LabelRoute frames brand inner context region type outer)
    (recorded : AuthoritySupport.Recorded (frames.flatMap Frame.authoritySupport) loans) :
    AuthoritySupport.Recorded context.authoritySupport loans ∧
      AuthoritySupport.Recorded (outer.flatMap Frame.authoritySupport) loans := by
  rw [route.1] at recorded
  simp only [List.flatMap_append,List.flatMap_cons,Frame.authoritySupport,AuthoritySupport.recorded_append] at recorded
  exact recorded.2

theorem ReservationInputs.authority_support {world : World} {available : Availability} {access : Access}
    {formals : List Local} {inputs : List InvocationInput}
    (prepared : ReservationInputs world available access formals inputs) :
    AuthoritySupport.Recorded (inputs.map InvocationInput.authority) world.loans := by
  rw [AuthoritySupport.recorded_map]
  intro input member
  exact (prepared.2.2.2 input member).1.recorded

theorem DisposesReservations.authority_support {context : Context} {places : List ResolvedPlace} {next : Task}
    {loans : Table Loan} (contextRecorded : AuthoritySupport.Recorded context.authoritySupport loans)
    (placesRecorded : AuthoritySupport.Recorded (places.map ResolvedPlace.authority) loans)
    (continued : AuthoritySupport.Recorded next.authoritySupport loans) :
    AuthoritySupport.Recorded (DisposesReservations context places next).authoritySupport loans := by
  induction places with
  | nil => exact continued
  | cons _ _ ih =>
    simp only [List.map_cons,AuthoritySupport.recorded_cons] at placesRecorded
    exact AuthoritySupport.recorded_append.mpr ⟨contextRecorded,
      AuthoritySupport.recorded_cons.mpr ⟨placesRecorded.1,ih placesRecorded.2⟩⟩

theorem ControlStep.authority_support {program : Kernel.Program} {before after : State} {event : Option Event}
    (well : before.world.WellFormed)
    (taskRecorded : AuthoritySupport.Recorded before.task.authoritySupport before.world.loans)
    (frameRecorded : AuthoritySupport.Recorded (before.frames.flatMap Frame.authoritySupport) before.world.loans)
    (step : ControlStep program before event after) :
    AuthoritySupport.Recorded after.task.authoritySupport after.world.loans ∧
      AuthoritySupport.Recorded (after.frames.flatMap Frame.authoritySupport) after.world.loans := by
  have retained := step.suspensionExtension.recorded
  have taskAfter := taskRecorded.mono retained
  have framesAfter := frameRecorded.mono retained
  cases step
  all_goals simp_all only [Task.authoritySupport,EntrySource.authoritySupport,List.map_append,
    List.map_cons,List.map_nil,AuthoritySupport.recorded_append,AuthoritySupport.recorded_cons,
    AuthoritySupport.recorded_nil,true_and,and_true,CloseRegions.authority_support]
  case labelCall argument =>
    obtain ⟨_,_,resolved⟩ := argument
    exact Context.resolves_recorded taskRecorded resolved
  case leave route _ _ _ =>
    obtain ⟨outer,rest⟩ := route.authority_support framesAfter
    exact ⟨outer,rest⟩
  case reserve allocated created => exact Context.bind_authority_support taskAfter trivial
  case closeAvailable resolved _ _ => exact Context.resolves_recorded taskRecorded resolved
  case destroyAvailable found permission _ _ =>
    apply DisposesReservations.authority_support taskAfter.1 ?_ taskAfter.2
    apply AuthoritySupport.Recorded.mono (before := before.world.loans) ?_ retained
    rw [AuthoritySupport.recorded_map]
    intro place member
    exact World.reserved_authority_recorded well found (List.mem_reverse.mp member)
  case contextualCall receiver _ _ _ _ _ _ _ witness _ _ captures inputs resources =>
    exact ⟨Context.resolves_recorded taskRecorded receiver,Context.resolves_recorded taskRecorded witness,
      ⟨captures.authority_support,inputs.authority_support taskRecorded⟩,
      resources.authority_support (AuthoritySupport.recorded_map.mp
        (AuthoritySupport.recorded_append.mp taskRecorded).1)⟩
  case positiveTest allocated tested => exact Context.bind_authority_support taskAfter trivial
  case negativeTest allocated tested => exact Context.bind_authority_support taskAfter trivial

end Glorious.Language.Execution
