import GloriousLanguage.ControlAuthorityStorage

/-! All ordinary transitions retain actual loan provenance in current tasks
and frames. Explicit loan release and hidden Drop leases are included. -/
namespace Glorious.Language.Execution

open _root_.Glorious.Language.Kernel

theorem TailFrames.authority_support {frames rest : List Frame} {activation : Identity}
    {outer : Context} {regions : List Identity} {loans : Table Loan}
    (route : TailFrames frames activation outer regions rest)
    (recorded : AuthoritySupport.Recorded (frames.flatMap Frame.authoritySupport) loans) :
    AuthoritySupport.Recorded outer.authoritySupport loans ∧
      AuthoritySupport.Recorded (rest.flatMap Frame.authoritySupport) loans := by
  induction route with
  | activation => exact AuthoritySupport.recorded_append.mp recorded
  | scope _ ih | label _ ih => exact ih (AuthoritySupport.recorded_append.mp recorded).2

theorem FreshNamedFrame.authority_support {function : Function} {context : Context} {brand region : Identity} {loans : Table Loan}
    (recorded : AuthoritySupport.Recorded context.authoritySupport loans) :
    AuthoritySupport.Recorded ((FreshNamedFrame function context brand region).flatMap Frame.authoritySupport) loans := by
  unfold FreshNamedFrame
  split <;> simp only [List.flatMap_nil,List.flatMap_cons,Frame.authoritySupport,List.append_nil,AuthoritySupport.recorded_nil]
  exact recorded

theorem LocalStep.authority_support {program : Kernel.Program} {before after : State} {event : Option Event}
    (typed : Typing.WorldTyped program before.world)
    (taskRecorded : AuthoritySupport.Recorded before.task.authoritySupport before.world.loans)
    (frameRecorded : AuthoritySupport.Recorded (before.frames.flatMap Frame.authoritySupport) before.world.loans)
    (step : LocalStep program before event after) :
    AuthoritySupport.Recorded after.task.authoritySupport after.world.loans ∧
      AuthoritySupport.Recorded (after.frames.flatMap Frame.authoritySupport) after.world.loans := by
  have retained := step.suspensionExtension.recorded
  have taskAfter := taskRecorded.mono retained
  have framesAfter := frameRecorded.mono retained
  cases step
  all_goals simp_all only [Task.authoritySupport,Frame.authoritySupport,PatternAction.authoritySupport,
    EntrySource.authoritySupport,List.flatMap_cons,List.flatMap_append,List.flatMap_nil,List.map_append,
    List.map_cons,List.map_nil,AuthoritySupport.recorded_append,AuthoritySupport.recorded_cons,
    AuthoritySupport.recorded_nil,Authority.Recorded,true_and,and_true]
  case evaluate allocated => exact Context.bind_authority_support taskAfter trivial
  case bind allocated => exact Context.bind_authority_support taskAfter trivial
  case discard resolved => exact Context.resolves_recorded taskRecorded resolved
  case assign target source permission _ =>
    exact ⟨permission.recorded,Context.resolves_recorded taskRecorded source⟩
  case invoke allocated => exact Context.bind_authority_support taskAfter trivial
  case call resolved _ _ _ _ inputs resources =>
    exact ⟨Context.resolves_recorded taskRecorded resolved,inputs.authority_support taskRecorded,
      resources.authority_support (AuthoritySupport.recorded_map.mp
        (AuthoritySupport.recorded_append.mp taskRecorded).1)⟩
  case enter entered =>
    have recorded := entered.context_authority_support taskRecorded.2
    exact ⟨recorded,FreshNamedFrame.authority_support recorded⟩
  case enterTail entered relinquished route _ _ _ =>
    have recorded := (entered.context_authority_support taskRecorded.2).mono
      (RelinquishesCustody.suspensionExtension relinquished).recorded
    have extended := Context.append_contracts_authority_support recorded taskAfter.1
    obtain ⟨outer,rest⟩ := route.authority_support framesAfter
    refine ⟨ReleaseCustodyLoans.authority_support ?_,FreshNamedFrame.authority_support extended,outer,rest⟩
    simpa only [Task.authoritySupport,CloseRegions.authority_support,AuthoritySupport.recorded_append] using
      (And.intro taskAfter.1 extended)
  case bindReturn moved returned =>
    have middle := moved.suspensionExtension.recorded
    exact ReleaseCustodyLoans.authority_support
      (returned.context_authority_support (taskRecorded.mono middle) (frameRecorded.1.mono middle))
  case activationReturn kept returned _ _ | scopeReturn kept returned _ _ =>
    have middle := (Protect.suspensionExtension kept).recorded
    exact ReleaseCustodyLoans.authority_support (AuthoritySupport.recorded_append.mpr
      ⟨taskAfter,returned.context_authority_support (taskRecorded.mono middle) (frameRecorded.1.mono middle)⟩)
  case labelReturn returned =>
    exact ReleaseCustodyLoans.authority_support (returned.context_authority_support taskRecorded frameRecorded.1)
  case shellDone => exact ReleaseCustodyLoans.authority_support taskAfter

  case scope => exact taskAfter
  case label => exact taskRecorded
  case choose resolved _ planned =>
    exact planned.authority_support (Context.resolves_recorded taskRecorded resolved)
  case patternBind bound => exact Context.bind_authority_support taskAfter.1 (bound.authority_recorded taskRecorded.2.1)
  case unsafeAllowed => exact taskRecorded
  case destroyHook allocated borrowed _ =>
    obtain ⟨_,_,found⟩ := borrowed.created_handle
    exact ⟨taskAfter.1,_,found⟩
  case destroyReference stored reference _ _ written =>
    exact retained _ (typed.reference_recorded stored reference)
  case releaseStorageReturned found returned =>
    exact ReleaseLoans.authority_support
      (fun dependency member => retained _ (World.loan_dependencies_recorded typed.1 found dependency member)) taskAfter.2
  case releaseRoot found parent ended =>
    exact ReleaseLoans.authority_support
      (fun dependency member => retained _ (World.loan_dependencies_recorded typed.1 found dependency
        (List.mem_append.mpr (Or.inr member)))) taskAfter.2
  case releaseChild found parent ended =>
    have dependencies := World.loan_dependencies_recorded typed.1 found
    simp only [parent,Option.toList_some,List.cons_append,List.nil_append] at dependencies
    exact ReleaseLoans.authority_support (fun dependency member => retained _ (dependencies dependency member)) taskAfter.2
  case endLoan resolved stored reference =>
    exact ⟨Context.resolves_recorded taskRecorded resolved,typed.reference_recorded stored reference⟩

theorem AtomStep.authority_support {program : Kernel.Program} {before after : State} {event : Option Event}
    (taskRecorded : AuthoritySupport.Recorded before.task.authoritySupport before.world.loans)
    (frameRecorded : AuthoritySupport.Recorded (before.frames.flatMap Frame.authoritySupport) before.world.loans)
    (step : AtomStep program before event after) :
    AuthoritySupport.Recorded after.task.authoritySupport after.world.loans ∧
      AuthoritySupport.Recorded (after.frames.flatMap Frame.authoritySupport) after.world.loans := by
  have retained := step.suspensionExtension.recorded
  have taskAfter := taskRecorded.mono retained
  have framesAfter := frameRecorded.mono retained
  cases step
  all_goals simp_all only [Task.authoritySupport,RetireAddresses.authority_support,
    AuthoritySupport.recorded_append,and_true,true_and]
  case primitive resolved _ => exact resolved.authority_support

end Glorious.Language.Execution
