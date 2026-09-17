import GloriousLanguage.Specification
import GloriousLanguage.DropObservation
import GloriousLanguage.DropCapabilities
import GloriousLanguage.LocalPreservation
import GloriousLanguage.ResumptionPreservation
import GloriousLanguage.DropHandle
import GloriousLanguage.InputBindingProgress
import GloriousLanguage.SnapshotTyping

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

/-- Constructive hook dispatch from the original receiver and positive handle
request. Physical exhaustion is distinct from missing static evidence; the
successful branch retains the actual input admission. The hook may diverge. -/
theorem destroyHook_progress {program : Kernel.Program} {before : State} {context : Context}
    {address : Address} {authority : Authority} {next : Task} {value : Value}
    {id : DeclId} {data : DataDefinition} {hook : DeclId} {arguments : List Term}
    {substitution : Substitution} {layout : Layout}
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
    (sourceType : AddressType program.declarations before.world address value.type)
    (permission : Permitted before.world authority .unique address)
    (request : AllocationRequest program.declarations before.world context.region
      (.reference .unique (.runtimeRegion context.region) value.type) layout) :
    (∃ (handle : Address) (withHandle after : World) (function : Kernel.Function) (formal : Kernel.Local),
      function.parameters = [formal] ∧ formal.type = .reference .unique (.runtimeRegion context.region) value.type ∧
      Contracts.DropContract program value.type (.runtimeRegion context.region) function ∧
      Contracts.FunctionInputs function [⟨.argument 0,formal,handle,.owner,.owned⟩] ∧
      Contracts.InputsTyped program [⟨.argument 0,formal,handle,.owner,.owned⟩] after ∧
      LocalStep program before (some (.hookEnter address hook))
        { before with world := after, task := .enter { context with unsafeAllowed := false } function (.supplied [⟨.argument 0,formal,handle,.owner,.owned⟩]) false, frames := .hook context address authority handle withHandle.nextLoan next :: before.frames } ∧
      Typing.WorldTyped program after) ∨
      AllocationExhausted program.declarations before.world context.region
        (.reference .unique (.runtimeRegion context.region) value.type) layout ∧
      LocalStep program before (some (.fatal .resource)) { before with task := .fatal .resource } := by
  obtain ⟨function,principal,dispatch,_,contract,capability,discard⟩ := valid.drop_dispatch selected drops instantiated kinded requirements
    (Kinding.runtimeRegion (id := context.region))
  rw [← nominal] at dispatch contract capability
  have valueTyped := typed.2.1 address value (World.resident_iff_stores.mpr stored)
  have disposable := valueTyped.mayDispose valid.declarations valid.inventory initialized capability discard
  have live := (initialized [] value .root).1
  rcases request.success_or_exhausted (.temporary context.activation context.scope) true with
    ⟨handle,withHandle,allocation⟩ | exhausted
  case inr =>
    exact Or.inr ⟨exhausted,.destroyHookExhausted task stored live disposable dispatch permission exhausted⟩
  apply Or.inl
  have allocated : Temporary program context
      (.reference .unique (.runtimeRegion context.region) value.type) before.world handle withHandle :=
    ⟨layout,allocation⟩
  have regionState : withHandle.liveRegions = before.world.liveRegions := by cases allocation; rfl
  have readyAfter := (allocation.handoffReady typed.1
    (show value.HandoffReady program before.world .unique [] from ⟨ready,by simp⟩)).1
  have permissionAfter := permission.locationExtension (allocation.locationExtension typed.1) allocation.loans
  have addressable : LoanPurpose.destructor.Admitted program.declarations value.type := by
    rw [nominal]
    exact .nominal
  obtain ⟨after,borrowed⟩ := FormsLoan.exists (purpose := .destructor) (mode := .unique)
    ((allocation.read typed.1 address).trans stored) (allocation.addressType typed.1 sourceType)
    initialized (by simpa only [regionState] using request.region_live) addressable
    readyAfter permissionAfter allocation.created_vacant allocation.created_addressType
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
  refine ⟨handle,withHandle,after,function,formal,parameters,formalType,contract,Contracts.FunctionInputs.argument captures parameters,?_,step,afterTyped⟩
  rw [inputsEq]
  exact inputs

end Execution

namespace Contracts

/-- The hook-shell branch of invocation progress consumes the constructed
dispatch outcome, not an assumed cleanup run or a completed handle loan. -/
theorem StateProgress.destroyHook {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {boundary : InvocationBoundary}
    {before : Execution.State} {context : Execution.Context}
    {address : Address} {authority : Authority} {next : Execution.Task} {value : Value}
    {id : DeclId} {data : DataDefinition} {hook : DeclId} {arguments : List Term}
    {substitution : Substitution}
    (valid : Specification.WellFormed program) (typed : Typing.WorldTyped program before.world)
    (inside : boundary.Inside program before)
    (task : before.task = .destroy context address authority next)
    (stored : before.world.Stores address value) (initialized : value.Initialized)
    (ready : value.ResourcesAccessible program before.world .unique)
    (compatible : value.ViewsLoanCompatible before.world .unique address .unique (authority.guardLoans before.world))
    (nominal : value.type = .nominal id arguments)
    (selected : program.declarations.data id = some data) (drops : data.dropHook = some hook)
    (instantiated : Instantiates data.generics arguments substitution)
    (kinded : ∀ argument ∈ arguments, Kinding program.declarations ⟨[],[],0,data.header.module,false,{}⟩ argument argument.kind)
    (requirements : ConstraintsHold program.declarations ⟨[],[],0,data.header.module,false,{}⟩ substitution data.requirements)
    (sourceType : AddressType program.declarations before.world address value.type)
    (permission : Permitted before.world authority .unique address)
    (live : context.region ∈ before.world.liveRegions)
    (capacity : program.declarations.input.target.pointerBits / 8 ≤
      program.declarations.input.target.maximumObjectBytes) :
    StateProgress program host function before boundary := by
  have referentSupported := typed.address_runtimeRegionsBelow valid.declarations sourceType
  have supported : (Term.reference .unique (.runtimeRegion context.region) value.type).RuntimeRegionsBelow
      before.world.nextRegion := by
    intro id occurs
    cases occurs with
    | child member nested =>
      simp only [Term.children,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · cases nested with
        | here => exact World.region_bound typed.1 live
        | child member _ => cases member
      · exact referentSupported id nested
  have request := AllocationRequest.reference (valid.declarations.1.1.2.2.2.2.1)
    live supported capacity
  have outcome := Execution.destroyHook_progress valid typed task stored initialized ready compatible
    nominal selected drops instantiated kinded requirements sourceType permission request
  apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
  rcases outcome with ⟨handle,withHandle,after,callee,formal,_,_,_,_,_,step,_⟩ | ⟨_,step⟩
  · exact ⟨_,_,inside,Or.inl step⟩
  · exact ⟨_,_,inside,Or.inl step⟩

end Contracts
end Glorious.Language
