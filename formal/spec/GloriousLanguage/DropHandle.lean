import GloriousLanguage.PrivateStorage
import GloriousLanguage.ActivationStorageOrigin
import GloriousLanguage.InputBatchProgress

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
      handle.root ∉ callee.rootSupport := by
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
      have moved := entered.owned_handle_private afterTyped trivial rfl whole found privateRoot
      exact ⟨context,callee,function,authority,handle,loan,next,{ root with value := none },beforeTask,rfl,rfl,rfl,
        entered.fresh_context.1,moved.1,live,rfl,home,whole,fresh,freshLoan,moved.2.1,moved.2.2⟩

/-- Actual destructor dispatch constructs the full common input admission:
initialized handoff readiness, formal coordinates, the real positive allocation
request and the selected declaration's original caller contract. Source
readiness and row compatibility are checked only in the original world. -/
theorem LocalStep.hook_inputs_admitted {program : Kernel.Program} {before entering : State}
    {address : Address} {hook : DeclId}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (source : ∀ caller authority next value, before.task = .destroy caller address authority next →
      before.world.Stores address value →
      value.ResourcesAccessible program before.world .unique ∧
      value.ViewsLoanCompatible before.world .unique address .unique (authority.guardLoans before.world))
    (dispatch : LocalStep program before (some (.hookEnter address hook)) entering) :
    ∃ (caller : Context) (function : Kernel.Function) (authority : Authority)
      (handle : Address) (loan : Identity) (next : Task) (original : Value),
      before.task = .destroy caller address authority next ∧ before.world.Stores address original ∧
      Kernel.DropInstance program original.type (.runtimeRegion caller.region) hook function ∧
      entering.task = .enter { caller with unsafeAllowed := false } function
        (.supplied [⟨.argument 0,function.parameters.head!,handle,.owner,.owned⟩]) false ∧
      entering.frames = .hook caller address authority handle loan next :: before.frames ∧
      Contracts.InputsTyped program [⟨.argument 0,function.parameters.head!,handle,.owner,.owned⟩] entering.world ∧
      Contracts.FunctionInputs function [⟨.argument 0,function.parameters.head!,handle,.owner,.owned⟩] ∧
      (EntrySource.supplied [⟨.argument 0,function.parameters.head!,handle,.owner,.owned⟩]).Admitted
        program entering.world caller.region function := by
  have afterTyped := dispatch.worldTyped valid inventory typed
  cases dispatch with
  | @destroyHook caller _ authority next value _ function allocated handle after loan task stored _ _ selected temporary borrowed loanId =>
    obtain ⟨ready,compatible⟩ := source caller authority next value task stored
    obtain ⟨type,handleStored,initialized,resources⟩ := temporary.borrowed_handle_ready typed.1 stored ready borrowed compatible
    obtain ⟨root,found,home,whole,privateRoot⟩ := temporary.borrowed_handle_private typed.1 stored borrowed
    obtain ⟨formal,parameters,formalType⟩ := selected.2.2.parameter
    have headFormal : function.parameters.head! = formal := by rw [parameters]; rfl
    have handleType := afterTyped.stored_root_type whole handleStored
      (AddressType.root_transport borrowed.locations whole temporary.addressType)
    have permission : Permitted after .owner .owned handle := by
      refine ⟨⟨root,found⟩,?_⟩
      intro identity loan found live overlap conflict
      exact privateRoot.1 identity loan found live overlap.1.symm
    let input : Kernel.InvocationInput := ⟨.argument 0,function.parameters.head!,handle,.owner,.owned⟩
    have inputReady : input.Ready program after :=
      ⟨_,handleStored,initialized,by simpa only [headFormal,formalType] using handleType,
        Value.ResourcesAccessible.private_handoff resources privateRoot,permission⟩
    obtain ⟨layout,allocation⟩ := temporary
    have request : input.StorageRequest program after caller.region := by
      change ∃ layout, AllocationRequest program.declarations after caller.region (function.parameters.head!).type layout
      refine ⟨layout,?_⟩
      rw [headFormal,formalType]
      exact allocation.request.same_regions (borrowed.region_state.1.trans allocation.region_state.1)
        (borrowed.region_state.2.trans allocation.region_state.2)
    have product := Kernel.InvocationInputsCompatible.singleton inputReady request permission.recorded
    have incoming : Kernel.IncomingResources program function after [input] := by
      obtain ⟨arguments,selectedBody⟩ := selected.2.1
      have absent := selectedBody.unsafe_contract_none inventory selected.2.2.1.2.2.2
      refine ⟨by simp,?_⟩
      rw [absent]
      intro actual member
      have same := List.mem_singleton.mp member
      subst actual
      exact Or.inl trivial
    have declared : ∃ declaration, program.declarations.function function.declaration = some declaration := by
      obtain ⟨arguments,template,declaration,substitution,body,found,signature,instantiated,constraints,closed,rfl⟩ := selected.2.1
      change ∃ declaration, program.declarations.function template.declaration = some declaration
      rw [Kernel.Program.function_declaration body]
      exact ⟨declaration,found⟩
    refine ⟨caller,function,authority,handle,loan,next,value,task,stored,selected,rfl,rfl,
      ⟨afterTyped,by simp,product.ready⟩,?_,EntrySource.Admitted.supplied product incoming declared⟩
    simpa only [headFormal] using
      (Contracts.FunctionInputs.argument (address := handle) (authority := .owner) selected.2.2.2.1 parameters)



end Glorious.Language.Execution
