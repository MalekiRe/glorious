import GloriousLanguage.DropHandle
import GloriousLanguage.DropObservation
import GloriousLanguage.ForeignRuntimePreservation

/-! The actual destructor dispatch establishes common invocation admission on
its complete caller stack, including host callback exposure. The hook's fresh
argument handle is not an assumed input or an erased-stack reconstruction. -/
namespace Glorious.Language.Execution

open _root_.Glorious.Language.Kernel Contracts

theorem LocalStep.hook_invocation_start {program : Kernel.Program} {host : Foreign.Model}
    {before entering : State} {address : Address} {hook : DeclId}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (control : before.ControlWellFormed) (registry : host.AuthoritiesRecorded before.world before.hostState)
    (callbacks : host.CallbacksWellFormed before)
    (source : ∀ caller authority next value, before.task = .destroy caller address authority next →
      before.world.Stores address value →
      value.ResourcesAccessible program before.world .unique ∧
      value.ViewsLoanCompatible before.world .unique address .unique (authority.guardLoans before.world))
    (dispatch : LocalStep program before (some (.hookEnter address hook)) entering) :
    ∃ (caller : Context) (function : Function) (authority : Authority)
      (handle : Address) (loan : Identity) (next : Task) (value : Value),
      before.task = .destroy caller address authority next ∧ before.world.Stores address value ∧
      DropInstance program value.type (.runtimeRegion caller.region) hook function ∧
      entering.task = .enter { caller with unsafeAllowed := false } function
        (.supplied [⟨.argument 0,function.parameters.head!,handle,.owner,.owned⟩]) false ∧
      entering.frames = .hook caller address authority handle loan next :: before.frames ∧
      InvocationStart program host function [⟨.argument 0,function.parameters.head!,handle,.owner,.owned⟩]
        (.caller { caller with unsafeAllowed := false } entering.frames) entering := by
  have afterControl := Step.controlWellFormed valid inventory lawful typed control (Or.inl dispatch) (by simp)
  have afterRegistry := Step.host_authorities valid inventory lawful typed control registry (Or.inl dispatch)
  have afterCallbacks := Step.callbacks valid inventory lawful typed control.suspensions callbacks (Or.inl dispatch)
  obtain ⟨caller,function,authority,handle,loan,next,value,task,stored,selected,enterTask,frames,inputsTyped,formals,admitted⟩ :=
    dispatch.hook_inputs_admitted valid inventory typed source
  obtain ⟨layout,request⟩ := admitted.inputs.requests _ List.mem_cons_self
  refine ⟨caller,function,authority,handle,loan,next,value,task,stored,selected,enterTask,frames,
    ⟨inputsTyped,formals,afterControl,afterRegistry,afterCallbacks,
      { caller with unsafeAllowed := false },.supplied _,false,enterTask,rfl,Or.inl ⟨rfl,rfl,rfl⟩,
      request.region_live,?_,admitted⟩⟩
  intro needsUnsafe
  have safe := selected.2.2.1.2.2.2
  cases safe.symm.trans needsUnsafe

/-- The selected Drop admission now applies directly to real ambient traces.
This does not assert that the current Drop event profile is the final adequate
form of the language's field-transfer and internally handled effect rules. -/
theorem LocalStep.hook_admitted_interval {program : Kernel.Program} {host : Foreign.Model}
    {before entering : State} {address : Address} {hook : DeclId}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (admitted : Specification.DropsAdmitted program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (control : before.ControlWellFormed) (registry : host.AuthoritiesRecorded before.world before.hostState)
    (callbacks : host.CallbacksWellFormed before)
    (source : ∀ caller authority next value, before.task = .destroy caller address authority next →
      before.world.Stores address value →
      value.ResourcesAccessible program before.world .unique ∧
      value.ViewsLoanCompatible before.world .unique address .unique (authority.guardLoans before.world))
    (dispatch : LocalStep program before (some (.hookEnter address hook)) entering) :
    ∃ (caller : Context) (function : Function) (authority : Authority)
      (handle : Address) (loan : Identity) (next : Task) (value : Value),
      before.task = .destroy caller address authority next ∧ before.world.Stores address value ∧
      entering.frames = .hook caller address authority handle loan next :: before.frames ∧
      let inputs := [InvocationInput.mk (.argument 0) function.parameters.head! handle .owner .owned]
      let boundary := InvocationBoundary.caller { caller with unsafeAllowed := false } entering.frames
      InvocationStart program host function inputs boundary entering ∧
      DropContract program value.type (.runtimeRegion caller.region) function ∧
      ∀ events finish, InvocationRun program host boundary entering events finish →
        DropTraceSafe entering.world inputs events ∧
        (∀ result, boundary.Normal finish result →
          Observes program host function ⟨inputs,entering.world,events,finish.world,.normal result⟩) := by
  obtain ⟨caller,function,authority,handle,loan,next,value,task,stored,selected,_,frames,initial⟩ :=
    dispatch.hook_invocation_start valid inventory lawful typed control registry callbacks source
  have contract := admitted.contracts _ _ _ _ selected
  refine ⟨caller,function,authority,handle,loan,next,value,task,stored,frames,initial,contract,?_⟩
  intro events finish run
  exact ⟨(contract.2.1 host _ _ entering events finish lawful initial run).1,
    fun _ normal => initial.normal_observation run normal⟩

end Glorious.Language.Execution
