import GloriousLanguage.PrivateStorage
import GloriousLanguage.ActivationStorageOrigin

/-! The actual hook dispatch and common input binder establish caller-handle
privacy. Generic storage and input framing live in the lower shared producer. -/
namespace Glorious.Language.Execution

/-- Two actual machine steps establish saved-handle privacy at the hook body,
including its vacant live caller-owned root and exclusion from the callee's
environment. No after-entry storage certificate is an input. -/
theorem LocalStep.hook_entry_private {program : Kernel.Program} {before entering body : State}
    {address : Address} {hook : DeclId}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (dispatch : LocalStep program before (some (.hookEnter address hook)) entering)
    (entry : LocalStep program entering none body) :
    ∃ (caller callee : Context) (function : Kernel.Function) (authority : Authority)
      (handle : Address) (loan : Identity) (next : Task) (root : Root),
      before.task = .destroy caller address authority next ∧
      entering.frames = .hook caller address authority handle loan next :: before.frames ∧
      body.task = .run callee function.body ∧
      body.frames = FreshNamedFrame function callee entering.nextBrand callee.region ++
        .activation { caller with unsafeAllowed := false } callee.activation callee.region :: entering.frames ∧
      callee.activation = entering.nextActivation ∧
      body.world.roots.get handle.root = some root ∧ root.live = true ∧ root.value = none ∧
      root.home = .temporary caller.activation caller.scope ∧ handle.fields = [] ∧
      handle.root = before.world.nextRoot ∧
      loan = before.world.nextLoan ∧
      CanEndStorage body.world handle.root ∧
      (∀ binding ∈ callee.environment, binding.address.root ≠ handle.root) := by
  have afterTyped := dispatch.worldTyped valid inventory typed
  cases dispatch with
  | @destroyHook context _ authority next value _ function allocated handle after loan beforeTask stored _ _ selected temporary borrowed identity =>
    obtain ⟨root,found,home,whole,privateRoot⟩ := temporary.borrowed_handle_private typed.1 stored borrowed
    have live := (World.root_found found).2.1
    have freshLoan : loan = before.world.nextLoan := identity.trans temporary.choose_spec.nextLoan
    have fresh : handle.root = before.world.nextRoot := by
      obtain ⟨_,allocated⟩ := temporary
      cases allocated
      rfl
    cases entry <;> try contradiction
    case enter caller actual source callee final task entered =>
      cases task
      have moved := entered.owned_handle_private afterTyped rfl whole found privateRoot
      exact ⟨context,callee,function,authority,handle,loan,next,{ root with value := none },beforeTask,rfl,rfl,rfl,
        entered.activation,moved.1,live,rfl,home,whole,fresh,freshLoan,moved.2.1,moved.2.2⟩

end Glorious.Language.Execution
