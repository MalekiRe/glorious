import GloriousLanguage.DropHandle
import GloriousLanguage.DropInvocation
import GloriousLanguage.PrivatePreservation

/-! Actual destructor dispatch and ordinary owned-input entry produce the
private stack/slot invariant consumed by complete-machine preservation.
The actual selected Drop contract supplies interval control restrictions; the
caller stack and host exposure are retained throughout. -/
namespace Glorious.Language.Execution

open _root_.Glorious.Language.Kernel Contracts

theorem LocalStep.hook_body_private {program : Kernel.Program} {host : Foreign.Model}
    {before entering body : State} {address : Address} {hook : DeclId}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (admitted : before.ControlWellFormed)
    (dispatch : LocalStep program before (some (.hookEnter address hook)) entering)
    (entry : LocalStep program entering none body) :
    ∃ (caller callee : Context) (function : Function) (authority : Authority)
      (handle : Address) (loan : Identity) (next : Task) (root : Root) (inner : List Frame),
      before.task = .destroy caller address authority next ∧
      entering.frames = .hook caller address authority handle loan next :: before.frames ∧
      body.task = .run callee function.body ∧
      body.frames = inner ++ .hook caller address authority handle loan next :: before.frames ∧
      root.home = .temporary caller.activation caller.scope ∧ root.live = true ∧
      handle.fields = [] ∧ handle.root = before.world.nextRoot ∧ loan = before.world.nextLoan ∧
      body.world.PrivateSlot handle.root root ∧
      handle.root ∉ before.frames.flatMap Frame.rootSupport ∧
      PrivateControl handle.root caller.activation inner body.task := by
  obtain ⟨caller,callee,function,authority,handle,loan,next,root,startTask,frames,task,bodyFrames,
      freshActivation,found,live,vacant,home,whole,fresh,freshLoan,safe,calleeOutside⟩ :=
    dispatch.hook_entry_private valid inventory typed entry
  have enteringControl := Step.controlWellFormed valid inventory lawful typed admitted (Or.inl dispatch) (by simp)
  have callerBound : caller.activation < entering.nextActivation :=
    enteringControl.activations.frames caller.activation (by rw [frames]; simp [Frame.activationSupport])
  have calleeFresh : callee.activation ≠ caller.activation := by
    rw [freshActivation]
    exact (Nat.ne_of_lt callerBound).symm
  have callerOutside : handle.root ∉ caller.rootSupport := by
    intro member
    have bound := admitted.task handle.root (by rw [startTask]; exact List.mem_append_left _ member)
    rw [fresh] at bound
    exact Nat.lt_irrefl _ bound
  have outerOutside : handle.root ∉ before.frames.flatMap Frame.rootSupport := by
    intro member
    have bound := admitted.frames handle.root member
    rw [fresh] at bound
    exact Nat.lt_irrefl _ bound
  let inner := FreshNamedFrame function callee entering.nextBrand callee.region ++
    [.activation { caller with unsafeAllowed := false } callee.activation callee.region]
  refine ⟨caller,callee,function,authority,handle,loan,next,root,inner,startTask,frames,task,?_,home,live,whole,
    fresh,freshLoan,⟨found,vacant,safe,by intro domain; simp [home]⟩,outerOutside,?_⟩
  · rw [bodyFrames,frames]
    simp only [inner,List.append_assoc,List.cons_append,List.nil_append]
  · rw [task]
    refine ⟨calleeOutside,?_,calleeFresh,?_⟩
    · simpa only [inner,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        Frame.rootSupport,Context.rootSupport,List.mem_append,not_or] using
        And.intro (FreshNamedFrame.avoids_root calleeOutside) callerOutside
    · exact PrivateFrames.fresh_named calleeFresh ⟨⟨calleeFresh,Or.inl rfl⟩,True.intro⟩

/-- Every prefix of the actual admitted hook interval preserves the allocated
private handle and its guard. Restrictions come from the selected declaration's
Drop contract, not a caller-supplied trace-safety premise. Internally handled
operations, including terminal operations, use the real routing relation. -/
theorem LocalStep.hook_body_admitted_private {program : Kernel.Program} {host : Foreign.Model}
    {before entering body : State} {address : Address} {hook : DeclId}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (drops : Specification.DropsAdmitted program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (admitted : before.ControlWellFormed)
    (registry : host.AuthoritiesRecorded before.world before.hostState)
    (callbacks : host.CallbacksWellFormed before)
    (source : ∀ caller authority next value, before.task = .destroy caller address authority next →
      before.world.Stores address value →
      value.ResourcesAccessible program before.world .unique ∧
      value.ViewsLoanCompatible before.world .unique address .unique (authority.guardLoans before.world))
    (dispatch : LocalStep program before (some (.hookEnter address hook)) entering)
    (entry : LocalStep program entering none body) :
    ∃ (caller : Context) (authority : Authority) (handle : Address) (loan : Identity) (next : Task) (root : Root),
      before.task = .destroy caller address authority next ∧ root.live = true ∧ handle.fields = [] ∧
      handle.root = before.world.nextRoot ∧ loan = before.world.nextLoan ∧
      root.home = .temporary caller.activation caller.scope ∧
      let boundary := InvocationBoundary.caller { caller with unsafeAllowed := false }
        (.hook caller address authority handle loan next :: before.frames)
      ∀ trace after, InvocationRun program host boundary body trace after →
        ∃ remaining, after.frames = remaining ++ .hook caller address authority handle loan next :: before.frames ∧
          after.world.PrivateSlot handle.root root ∧ PrivateControl handle.root caller.activation remaining after.task ∧
          (boundary.Inside program after ∨ ∃ result, boundary.Normal after result) := by
  classical
  obtain ⟨caller,callee,function,authority,handle,loan,next,root,inner,startTask,entryFrames,_,frames,home,live,whole,
      fresh,freshLoan,slot,outerOutside,privateControl⟩ := dispatch.hook_body_private valid inventory lawful typed admitted entry
  obtain ⟨actualCaller,actualFunction,actualAuthority,actualHandle,actualLoan,actualNext,value,
      _,_,selected,_,actualFrames,initial⟩ :=
    dispatch.hook_invocation_start valid inventory lawful typed admitted registry callbacks source
  have sameGuard := Frame.hook.inj (List.cons.inj (entryFrames.symm.trans actualFrames)).1
  obtain ⟨rfl,_,rfl,rfl,rfl,rfl⟩ := sameGuard
  rw [entryFrames] at initial
  have contract := drops.contracts _ _ _ _ selected
  have entered : Run program host before [.hookEnter address hook] body :=
    .visible (Or.inl dispatch) (.silent (Or.inl entry) .refl)
  refine ⟨caller,authority,handle,loan,next,root,startTask,live,whole,
    fresh,freshLoan,home,?_⟩
  dsimp only
  intro trace after run
  have interval : InvocationRun program host
      (.caller { caller with unsafeAllowed := false }
        (.hook caller address authority handle loan next :: before.frames)) entering trace after :=
    .silent ⟨initial.inside,Or.inl entry⟩ run
  have safe := (contract.2.1 host _ _ entering trace after lawful initial interval).1.1
  obtain ⟨remaining,afterFrames,afterSlot,afterControl⟩ :=
    run.private_guard valid inventory lawful (entered.worldTyped valid inventory lawful typed)
    (entered.controlWellFormed valid inventory lawful typed admitted (entered.nonFatal_of_trace (by simp)))
    slot home privateControl frames outerOutside
    (fun event member => ⟨(safe event member).1,(safe event member).2.2,(safe event member).2.1⟩)
  refine ⟨remaining,afterFrames,afterSlot,afterControl,?_⟩
  by_cases handoff : (InvocationBoundary.caller { caller with unsafeAllowed := false }
      (.hook caller address authority handle loan next :: before.frames)).Handoff after
  · apply Or.inr
    have progress := (contract.2.2.2 host _ _ entering trace after lawful initial
      (by intro input member _; cases List.mem_singleton.mp member; rfl) interval).1
    exact progress.handoff_normal handoff
  · refine Or.inl ⟨⟨remaining,afterFrames⟩,handoff,?_,?_⟩
    · intro context operation arguments payload pending
      exact contract.interval_perform_internal lawful initial interval pending
    · intro context brand result pending
      have impossible := afterControl.2.2.1
      rw [pending] at impossible
      exact False.elim impossible

/-- An arbitrary real machine run factors before the first normal return to
the hook's caller. The prefix retains the private slot and guard; the suffix
is unrestricted caller execution. This follows from actual Drop admission,
not an assumed restriction on the whole ambient trace. -/
theorem LocalStep.hook_body_private_until_return {program : Kernel.Program} {host : Foreign.Model}
    {before entering body after : State} {address : Address} {hook : DeclId} {trace : List Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (drops : Specification.DropsAdmitted program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (admitted : before.ControlWellFormed)
    (registry : host.AuthoritiesRecorded before.world before.hostState)
    (callbacks : host.CallbacksWellFormed before)
    (source : ∀ caller authority next value, before.task = .destroy caller address authority next →
      before.world.Stores address value →
      value.ResourcesAccessible program before.world .unique ∧
      value.ViewsLoanCompatible before.world .unique address .unique (authority.guardLoans before.world))
    (dispatch : LocalStep program before (some (.hookEnter address hook)) entering)
    (entry : LocalStep program entering none body) (run : Run program host body trace after) :
    ∃ (caller : Context) (authority : Authority) (handle : Address) (loan : Identity) (next : Task) (root : Root),
      before.task = .destroy caller address authority next ∧ root.live = true ∧ handle.fields = [] ∧
      handle.root = before.world.nextRoot ∧ loan = before.world.nextLoan ∧
      root.home = .temporary caller.activation caller.scope ∧
      let boundary := InvocationBoundary.caller { caller with unsafeAllowed := false }
        (.hook caller address authority handle loan next :: before.frames)
      ∃ first last finish remaining, trace = first ++ last ∧
        InvocationRun program host boundary body first finish ∧ Run program host finish last after ∧
        finish.frames = remaining ++ .hook caller address authority handle loan next :: before.frames ∧
        finish.world.PrivateSlot handle.root root ∧ PrivateControl handle.root caller.activation remaining finish.task ∧
        (finish = after ∨ ∃ result, boundary.Normal finish result) := by
  obtain ⟨caller,authority,handle,loan,next,root,task,live,whole,fresh,freshLoan,home,privatePrefix⟩ :=
    dispatch.hook_body_admitted_private valid inventory drops lawful typed admitted registry callbacks source entry
  refine ⟨caller,authority,handle,loan,next,root,task,live,whole,fresh,freshLoan,home,?_⟩
  dsimp only
  obtain ⟨first,last,finish,events,interval,rest,exit⟩ := invocation_first_exit
    (boundary := .caller { caller with unsafeAllowed := false }
      (.hook caller address authority handle loan next :: before.frames)) run
  obtain ⟨remaining,frames,slot,control,closed⟩ := privatePrefix first finish interval
  refine ⟨first,last,finish,remaining,events,interval,rest,frames,slot,control,?_⟩
  rcases exit with outside | ⟨_,same⟩
  · exact closed.elim (fun inside => False.elim (outside inside)) Or.inr
  · exact Or.inl same

end Glorious.Language.Execution
