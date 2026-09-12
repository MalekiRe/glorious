import GloriousLanguage.ControlAuthoritySnapshot

/-! Every effect producer preserves current authority provenance, including
clause environments, last replay, copied replay, completion and cancellation.
Saved authorities are consumed from actual historical control, not assumed
valid only after replay has already executed. -/
namespace Glorious.Language.Execution

open Kernel

theorem StartsClause.authority_support {before : State} {handler : InstalledHandler} {context : Context}
    {after : World} {loans : Table Loan} (started : StartsClause before handler context after)
    (recorded : AuthoritySupport.Recorded handler.authoritySupport loans) :
    AuthoritySupport.Recorded context.authoritySupport loans := by
  rw [started.2]
  exact (AuthoritySupport.recorded_append.mp (AuthoritySupport.recorded_append.mp recorded).1).1

theorem StartsResumptionClause.authority_support {before : State} {handler : InstalledHandler} {lexical localSlot : Local}
    {context : Context} {after : World} {loans : Table Loan}
    (started : StartsResumptionClause before handler lexical context localSlot after)
    (recorded : AuthoritySupport.Recorded handler.authoritySupport loans) :
    AuthoritySupport.Recorded context.authoritySupport loans := by
  obtain ⟨_,_,started,_,rfl,_⟩ := started
  exact started.authority_support recorded

theorem PayloadPlan.authority_support {program : Language.Program} {world : World}
    {addresses : List Address} {patterns : List Pattern} {actions : PatternActions}
    (planned : PayloadPlan program world addresses patterns actions) :
    AuthoritySupport.Recorded ((ScheduledPattern actions).flatMap PatternAction.authoritySupport) world.loans := by
  induction planned with
  | nil => simp [ScheduledPattern]
  | cons first _ ih =>
    have one := first.authority_support trivial
    simp_all only [ScheduledPattern,List.flatMap_append,AuthoritySupport.recorded_append,true_and]

theorem Installs.authority_support {program : Kernel.Program} {before : State} {outer : Context}
    {syntaxNode : Handler} {handler : InstalledHandler} {after : World}
    (recorded : AuthoritySupport.Recorded outer.authoritySupport before.world.loans)
    (installed : Installs program before outer syntaxNode handler after) :
    AuthoritySupport.Recorded handler.authoritySupport after.loans := by
  have outerRecorded := recorded.mono installed.suspensionExtension.recorded
  obtain ⟨first,second,sources,captures,captured,bindings,bound,disposed,one,two,_,capturedValues,boundValues,retired,rfl,rfl⟩ := installed
  have environmentRecorded := AuthoritySupport.recorded_map.mpr boundValues.authority_recorded
  simp only [InstalledHandler.authoritySupport,AuthoritySupport.recorded_append]
  exact ⟨⟨environmentRecorded.mono retired.suspensionExtension.recorded,outerRecorded⟩,outerRecorded⟩

theorem EffectStep.authority_support {program : Kernel.Program} {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world) (suspensions : before.SuspensionsWellFormed)
    (taskRecorded : AuthoritySupport.Recorded before.task.authoritySupport before.world.loans)
    (frameRecorded : AuthoritySupport.Recorded (before.frames.flatMap Frame.authoritySupport) before.world.loans)
    (saved : ∀ id suspension, before.resumptions.get id = some suspension →
      AuthoritySupport.Recorded suspension.controlAuthoritySupport before.world.loans)
    (step : EffectStep program before event after) :
    AuthoritySupport.Recorded after.task.authoritySupport after.world.loans ∧
      AuthoritySupport.Recorded (after.frames.flatMap Frame.authoritySupport) after.world.loans := by
  have retained := (step.suspension_storage valid inventory suspensions typed).2
  have taskAfter := taskRecorded.mono retained
  have framesAfter := frameRecorded.mono retained
  cases step
  all_goals simp_all only [Task.authoritySupport,Frame.authoritySupport,List.flatMap_cons,List.flatMap_append,
    List.flatMap_nil,AuthoritySupport.recorded_append,AuthoritySupport.recorded_cons,AuthoritySupport.recorded_nil,
    true_and,and_true,CloseRegions.authority_support]
  case install installed =>
    have handlerRecorded := installed.authority_support taskRecorded
    exact ⟨(AuthoritySupport.recorded_append.mp (AuthoritySupport.recorded_append.mp handlerRecorded).1).2,handlerRecorded⟩
  case operationCall resolved => exact resolved.authority_support
  case terminal route started keptTransfer roots _ planned =>
    obtain ⟨_,handlerRecorded,outerRecorded⟩ := route.authority_support framesAfter
    have clauseRecorded := started.authority_support handlerRecorded
    exact ⟨⟨clauseRecorded,planned.authority_support⟩,⟨handlerRecorded,clauseRecorded⟩,outerRecorded⟩
  case suspend route started keptTransfer _ _ _ created planned _ =>
    obtain ⟨_,handlerRecorded,outerRecorded⟩ := route.authority_support framesAfter
    have clauseRecorded := started.authority_support handlerRecorded
    exact ⟨⟨Context.bind_authority_support clauseRecorded trivial,planned.authority_support⟩,
      ⟨handlerRecorded,clauseRecorded⟩,outerRecorded⟩
  case suspendTailArm route started keptTransfer _ _ _ planned _ =>
    obtain ⟨_,handlerRecorded,outerRecorded⟩ := route.authority_support framesAfter
    have clauseRecorded := started.authority_support handlerRecorded
    exact ⟨⟨clauseRecorded,planned.authority_support⟩,clauseRecorded,⟨handlerRecorded,clauseRecorded⟩,outerRecorded⟩
  case continuationCall argument =>
    obtain ⟨_,_,resolved⟩ := argument
    exact Context.resolves_recorded taskRecorded resolved
  case tailArmReturn => trivial
  case resumeLast found _ _ _ keptTransfer =>
    have savedRecorded := (saved _ _ found).mono retained
    simp only [Suspension.controlAuthoritySupport,AuthoritySupport.recorded_append] at savedRecorded
    exact ⟨savedRecorded.1.1,savedRecorded.2,savedRecorded.1.2⟩
  case resumeCopy found _ _ copied keptTransfer =>
    obtain ⟨contextRecorded,handlerRecorded,savedRecorded⟩ := copied.authority_support typed.1 (saved _ _ found)
    have transferred := keptTransfer.suspensionExtension.recorded
    exact ⟨contextRecorded.mono transferred,savedRecorded.mono transferred,handlerRecorded.mono transferred⟩
  case completionIdentity started keptTransfer roots _ =>
    have clauseRecorded := started.authority_support framesAfter.1
    exact ⟨clauseRecorded,clauseRecorded⟩
  case completion started keptTransfer roots _ _ planned =>
    have clauseRecorded := started.authority_support framesAfter.1
    exact ⟨⟨clauseRecorded,planned.authority_support trivial⟩,clauseRecorded⟩
  case finishedOwnedClause roots _ =>
    simp only [InstalledHandler.authoritySupport,AuthoritySupport.recorded_append] at taskRecorded
    exact ⟨taskRecorded.1.1,taskRecorded.2⟩
  case finishedLentClause =>
    exact (AuthoritySupport.recorded_append.mp (AuthoritySupport.recorded_append.mp taskRecorded).1).1
  case disposeContinuation =>
    split
    · exact AuthoritySupport.recorded_append.mpr ⟨taskAfter.1,taskAfter.2⟩
    · exact taskAfter.2

end Glorious.Language.Execution
