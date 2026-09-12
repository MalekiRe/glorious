import GloriousLanguage.DropHandle
import GloriousLanguage.ControlOriginPreservation

/-! The destructor's actual freshly allocated saved handle is excluded from
every pre-existing suspension inventory and saved control address graph.
The proof follows real hook entry and arbitrary body execution; it does not
assume post-body privacy or that abandoned caller frames remain live. -/
namespace Glorious.Language.Execution

theorem LocalStep.hook_entry_old_suspensions {program : Kernel.Program} {host : Foreign.Model}
    {before entering body after : State} {address : Address} {hook : DeclId} {trace : List Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (control : before.ControlWellFormed)
    (dispatch : LocalStep program before (some (.hookEnter address hook)) entering)
    (entry : LocalStep program entering none body) (run : Run program host body trace after) :
    ∃ (caller callee : Context) (function : Kernel.Function) (authority : Authority)
      (handle : Address) (loan : Identity) (next : Task) (root : Root),
      entering.frames = .hook caller address authority handle loan next :: before.frames ∧
      body.task = .run callee function.body ∧
      body.world.roots.get handle.root = some root ∧ root.live = true ∧ root.value = none ∧
      root.home = .temporary caller.activation caller.scope ∧ handle.fields = [] ∧
      handle.root = before.world.nextRoot ∧ CanEndStorage body.world handle.root ∧
      (∀ binding ∈ callee.environment, binding.address.root ≠ handle.root) ∧
      after.ControlWellFormed ∧
      (∀ id original, before.resumptions.get id = some original →
        ∀ current, after.resumptions.get id = some current →
          handle.root ∉ current.roots ∧ handle.root ∉ current.controlRootSupport) ∧
      (∀ id original, before.resumptions.get id = some original →
        ∀ canceled, EffectStep program after (some (.cancel id)) canceled →
        ∀ context roots next, canceled.task = .cleanup context roots next → handle.root ∉ roots) := by
  obtain ⟨caller,callee,function,authority,handle,loan,next,root,frame,task,found,live,vacant,home,whole,fresh,safe,excluded⟩ :=
    dispatch.hook_entry_private valid inventory typed entry
  have execution : Run program host before (.hookEnter address hook :: trace) after :=
    .visible (Or.inl dispatch) (.silent (Or.inl entry) run)
  refine ⟨caller,callee,function,authority,handle,loan,next,root,frame,task,found,live,vacant,home,whole,fresh,safe,excluded,
    execution.controlWellFormed valid inventory lawful typed control,?_,?_⟩
  · intro id original beforeAt current afterAt
    exact ⟨execution.old_inventory_excludes_future_root control.suspensions beforeAt afterAt (Nat.le_of_eq fresh.symm),
      execution.old_saved_control_excludes_future_root valid inventory lawful typed control beforeAt afterAt (Nat.le_of_eq fresh.symm)⟩
  · intro id original beforeAt canceled cancellation
    exact execution.cancel_old_excludes_future_root control.suspensions beforeAt (Nat.le_of_eq fresh.symm) cancellation

end Glorious.Language.Execution
