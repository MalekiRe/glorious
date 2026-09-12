import GloriousLanguage.DropHandle
import GloriousLanguage.PrivatePreservation

/-! Actual destructor dispatch and ordinary owned-input entry produce the
private stack/slot invariant consumed by complete-machine preservation.
The ambient run's control restrictions remain an explicit semantic premise. -/
namespace Glorious.Language.Execution

open Kernel

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
      body.task = .run callee function.body ∧
      body.frames = inner ++ .hook caller address authority handle loan next :: before.frames ∧
      root.home = .temporary caller.activation caller.scope ∧ root.live = true ∧
      handle.fields = [] ∧ handle.root = before.world.nextRoot ∧ loan = before.world.nextLoan ∧
      body.world.PrivateSlot handle.root root ∧
      handle.root ∉ before.frames.flatMap Frame.rootSupport ∧
      PrivateControl handle.root caller.activation inner body.task := by
  obtain ⟨caller,callee,function,authority,handle,loan,next,root,startTask,frames,task,bodyFrames,
      freshActivation,found,live,vacant,home,whole,fresh,freshLoan,safe,bindings⟩ :=
    dispatch.hook_entry_private valid inventory typed entry
  have enteringControl := (Step.controlWellFormed valid inventory lawful typed admitted (Or.inl dispatch))
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
  have calleeOutside : handle.root ∉ callee.rootSupport := by
    intro member
    obtain ⟨binding,present,same⟩ := List.mem_map.mp member
    exact bindings binding present same
  let inner := FreshNamedFrame function callee entering.nextBrand callee.region ++
    [.activation { caller with unsafeAllowed := false } callee.activation callee.region]
  refine ⟨caller,callee,function,authority,handle,loan,next,root,inner,startTask,task,?_,home,live,whole,
    fresh,freshLoan,⟨found,vacant,safe,by intro domain; simp [home]⟩,outerOutside,?_⟩
  · rw [bodyFrames,frames]
    simp only [inner,List.append_assoc,List.cons_append,List.nil_append]
  · rw [task]
    refine ⟨calleeOutside,?_,calleeFresh,?_⟩
    · simpa only [inner,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        Frame.rootSupport,Context.rootSupport,List.mem_append,not_or] using
        And.intro (FreshNamedFrame.avoids_root calleeOutside) callerOutside
    · exact PrivateFrames.fresh_named calleeFresh ⟨⟨calleeFresh,Or.inl rfl⟩,True.intro⟩

/-- For the actual allocated hook handle, either the body still holds its
guard and private slot, or its first real guard return is found inside the
given run. The invariant is derived at entry and propagated, not supplied as
an after-body certificate. Ambient trace admission is not inferred by erasing
the caller's frames or host exposure. -/
theorem LocalStep.hook_body_private_until_return {program : Kernel.Program} {host : Foreign.Model}
    {before entering body after : State} {address : Address} {hook : DeclId} {trace : List Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (admitted : before.ControlWellFormed)
    (dispatch : LocalStep program before (some (.hookEnter address hook)) entering)
    (entry : LocalStep program entering none body) (run : Run program host body trace after)
    (safe : ∀ event ∈ trace, (∀ brand, event ≠ .leave brand) ∧
      (∀ key last, event ≠ .replay key last) ∧ (∀ operation arguments, event ≠ .perform operation arguments)) :
    ∃ (caller : Context) (authority : Authority) (handle : Address) (loan : Identity) (next : Task) (root : Root),
      before.task = .destroy caller address authority next ∧ root.live = true ∧ handle.fields = [] ∧
      handle.root = before.world.nextRoot ∧ loan = before.world.nextLoan ∧
      root.home = .temporary caller.activation caller.scope ∧
      ((∃ remaining, after.frames = remaining ++ .hook caller address authority handle loan next :: before.frames ∧
        after.world.PrivateSlot handle.root root ∧ PrivateControl handle.root caller.activation remaining after.task) ∨
      (∃ returning returned first last,
        trace = first ++ last ∧ Run program host body first returning ∧
        LocalStep program returning none returned ∧ Run program host returned last after ∧
        returning.frames = .hook caller address authority handle loan next :: before.frames ∧ returned.frames = before.frames ∧
        returning.world.PrivateSlot handle.root root ∧ returned.world.PrivateSlot handle.root root ∧
        PrivateControl handle.root caller.activation [] returning.task)) := by
  obtain ⟨caller,callee,function,authority,handle,loan,next,root,inner,startTask,_,frames,home,live,whole,
      fresh,freshLoan,slot,outerOutside,privateControl⟩ := dispatch.hook_body_private valid inventory lawful typed admitted entry
  have entered : Run program host before [.hookEnter address hook] body :=
    .visible (Or.inl dispatch) (.silent (Or.inl entry) .refl)
  exact ⟨caller,authority,handle,loan,next,root,startTask,live,whole,fresh,freshLoan,home,
    run.private_until_guard_pop valid inventory lawful (entered.worldTyped valid inventory lawful typed)
      (entered.controlWellFormed valid inventory lawful typed admitted) slot home privateControl frames outerOutside safe⟩

end Glorious.Language.Execution
