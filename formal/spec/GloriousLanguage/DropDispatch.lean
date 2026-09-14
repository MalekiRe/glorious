import GloriousLanguage.Specification
import GloriousLanguage.DropObservation
import GloriousLanguage.DropCapabilities
import GloriousLanguage.LocalPreservation
import GloriousLanguage.ResumptionPreservation
import GloriousLanguage.DropHandle

/-! Admitted destructor declarations dispatch through the ordinary function
instance and machine hook-entry rules. Neither an executable body, a zero-arg
specialization, nor an after-world typing judgment is an admission premise. -/
namespace Glorious.Language

theorem PrincipalOf.drop_mayDiscard {program : Program} (valid : ProgramWellFormed program) {id : DeclId} {data : DataDefinition}
    {arguments : List Term} {hook : DeclId} {principal : Principal}
    (selected : program.data id = some data) (drops : data.dropHook = some hook)
    (capability : PrincipalOf program (.nominal id arguments) principal) : principal.MayDiscard :=
  capability.nominal_drop_discardable valid selected drops


namespace Specification

/-- The actual body inventory and checked function admission complete the
declaration-level application. Every generic nominal argument and the actual
borrow region are retained by the selected parameter type. -/
theorem DropsAdmitted.dispatch {program : Kernel.Program}
    (inventory : Kernel.BodyInventory program) (functions : FunctionsAdmitted program)
    (admitted : DropsAdmitted program) {id : DeclId} {data : DataDefinition} {hook : DeclId}
    {arguments : List Term} {substitution : Substitution} {region : Term}
    (selected : program.declarations.data id = some data) (drops : data.dropHook = some hook)
    (instantiated : Instantiates data.generics arguments substitution)
    (kinded : ∀ argument ∈ arguments, Kinding program.declarations ⟨[],[],0,data.header.module,false,{}⟩ argument argument.kind)
    (requirements : ConstraintsHold program.declarations ⟨[],[],0,data.header.module,false,{}⟩ substitution data.requirements)
    (regionKinded : Kinding program.declarations ⟨[],[],0,data.header.module,false,{}⟩ region .region) :
    ∃ function principal, Kernel.DropInstance program (.nominal id arguments) region hook function ∧
      Typing.FunctionType program function ∧ Contracts.DropContract program (.nominal id arguments) region function ∧
      PrincipalOf program.declarations (.nominal id arguments) principal ∧ principal.MayDiscard := by
  obtain ⟨hookArguments,declaration,hookSubstitution,application⟩ :=
    admitted.applications id data hook arguments substitution region selected drops instantiated kinded requirements regionKinded
  obtain ⟨function,bodyInstance,signature,captures⟩ := Kernel.DropApplication.body inventory application
  obtain ⟨principal,capability,discard⟩ := application.capability
  have typed := (functions hook hookArguments function bodyInstance).1
  have parameterTypes := typed.choose_spec.2.1
  have dispatch : Kernel.DropInstance program (.nominal id arguments) region hook function :=
    ⟨Or.inl ⟨id,arguments,data,rfl,selected,drops⟩,⟨hookArguments,bodyInstance⟩,signature,captures,parameterTypes⟩
  exact ⟨function,principal,dispatch,typed,admitted.contracts _ _ _ _ dispatch,capability,discard⟩

theorem WellFormed.drop_dispatch {program : Kernel.Program} (valid : WellFormed program)
    {id : DeclId} {data : DataDefinition} {hook : DeclId} {arguments : List Term}
    {substitution : Substitution} {region : Term}
    (selected : program.declarations.data id = some data) (drops : data.dropHook = some hook)
    (instantiated : Instantiates data.generics arguments substitution)
    (kinded : ∀ argument ∈ arguments, Kinding program.declarations ⟨[],[],0,data.header.module,false,{}⟩ argument argument.kind)
    (requirements : ConstraintsHold program.declarations ⟨[],[],0,data.header.module,false,{}⟩ substitution data.requirements)
    (regionKinded : Kinding program.declarations ⟨[],[],0,data.header.module,false,{}⟩ region .region) :
    ∃ function principal, Kernel.DropInstance program (.nominal id arguments) region hook function ∧
      Typing.FunctionType program function ∧ Contracts.DropContract program (.nominal id arguments) region function ∧
      PrincipalOf program.declarations (.nominal id arguments) principal ∧ principal.MayDiscard :=
  valid.drops.dispatch valid.inventory valid.functions selected drops instantiated kinded requirements regionKinded

end Specification

namespace Execution

/-- Progress at the hook-dispatch boundary. Allocation and borrowing are
the actual resource prerequisites; admitted declarations produce the body,
and the original receiver graph supplies the common input admission. Structural
typing alone is not handoff readiness. The hook may diverge. -/
theorem destroyHook_progress {program : Kernel.Program} {before : State} {context : Context}
    {address : Address} {authority : Authority} {next : Task} {value : Value}
    {id : DeclId} {data : DataDefinition} {hook : DeclId} {arguments : List Term}
    {substitution : Substitution} {handle : Address} {withHandle after : World}
    (valid : Specification.WellFormed program) (typed : Typing.WorldTyped program before.world)
    (task : before.task = .destroy context address authority next)
    (stored : before.world.Stores address value) (initialized : value.Initialized)
    (ready : value.ResourcesAccessible program before.world .unique)
    (compatible : value.ViewsLoanCompatible before.world .unique address .unique (authority.guardLoans before.world))
    (nominal : value.type = .nominal id arguments)
    (selected : program.declarations.data id = some data) (drops : data.dropHook = some hook)
    (instantiated : Instantiates data.generics arguments substitution)
    (kinded : ∀ argument ∈ arguments, Kinding program.declarations ⟨[],[],0,data.header.module,false,{}⟩ argument argument.kind)
    (requirements : ConstraintsHold program.declarations ⟨[],[],0,data.header.module,false,{}⟩ substitution data.requirements)
    (allocated : Temporary program context (.reference .unique (.runtimeRegion context.region) value.type)
      before.world handle withHandle)
    (borrowed : FormsLoan program .destructor withHandle authority .unique context.region address handle after) :
    ∃ (function : Kernel.Function) (formal : Kernel.Local),
      function.parameters = [formal] ∧ formal.type = .reference .unique (.runtimeRegion context.region) value.type ∧
      Contracts.DropContract program value.type (.runtimeRegion context.region) function ∧
      Contracts.FunctionInputs function [⟨.argument 0,formal,handle,.owner,.owned⟩] ∧
      Contracts.InputsTyped program [⟨.argument 0,formal,handle,.owner,.owned⟩] after ∧
      LocalStep program before (some (.hookEnter address hook))
        { before with world := after, task := .enter { context with unsafeAllowed := false } function (.supplied [⟨.argument 0,formal,handle,.owner,.owned⟩]) false, frames := .hook context address authority handle withHandle.nextLoan next :: before.frames } ∧
      Typing.WorldTyped program after := by
  obtain ⟨function,principal,dispatch,_,contract,capability,discard⟩ := valid.drop_dispatch selected drops instantiated kinded requirements
    (Kinding.runtimeRegion (id := context.region))
  rw [← nominal] at dispatch contract capability
  have valueTyped := typed.2.1 address value (World.resident_iff_stores.mpr stored)
  have disposable := valueTyped.mayDispose valid.declarations valid.inventory initialized capability discard
  have live := (initialized [] value .root).1
  obtain ⟨formal,parameters,formalType⟩ := dispatch.2.2.parameter
  have step := LocalStep.destroyHook task stored live disposable dispatch allocated borrowed rfl
  simp only [parameters,List.head!] at step
  have afterTyped := LocalStep.worldTyped valid.declarations valid.inventory typed step
  have captures := dispatch.2.2.2.1
  have source : ∀ caller permission following resident, before.task = .destroy caller address permission following →
      before.world.Stores address resident →
      resident.ResourcesAccessible program before.world .unique ∧
      resident.ViewsLoanCompatible before.world .unique address .unique (permission.guardLoans before.world) := by
    intro caller permission following resident currentTask currentStored
    obtain ⟨callerEq,_,permissionEq,followingEq⟩ := Task.destroy.inj (currentTask.symm.trans task)
    subst caller permission following
    have same : resident = value := Option.some.inj (currentStored.symm.trans stored)
    subst resident
    exact ⟨ready,compatible⟩
  obtain ⟨caller,actualFunction,actualAuthority,actualHandle,loan,following,original,
    _,_,_,enterTask,_,inputs,_,_⟩ := step.hook_inputs_admitted valid.declarations valid.inventory typed source
  obtain ⟨_,_,sourcesEq,_⟩ := Task.enter.inj enterTask
  have inputsEq := EntrySource.supplied.inj sourcesEq
  refine ⟨function,formal,parameters,formalType,contract,Contracts.FunctionInputs.argument captures parameters,?_,step,afterTyped⟩
  rw [inputsEq]
  exact inputs

end Execution
end Glorious.Language
