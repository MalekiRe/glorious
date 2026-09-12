import GloriousLanguage.Specification
import GloriousLanguage.DropObservation
import GloriousLanguage.DropCapabilities
import GloriousLanguage.LocalPreservation
import GloriousLanguage.ResumptionPreservation

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

/-- The hook's fresh handle is an owned invocation input, not merely a
well-typed resident. Existing loans cannot name its fresh storage identity,
and the new loan names the original receiver rather than the handle. -/
theorem Temporary.borrowed_handle {program : Kernel.Program} {before withHandle after : World}
    {context : Context} {value : Value} {referent handle : Address} {authority : Authority}
    (well : before.WellFormed) (stored : before.Stores referent value)
    (allocated : Temporary program context (.reference .unique (.runtimeRegion context.region) value.type)
      before handle withHandle)
    (borrowed : Borrows program.declarations withHandle authority .unique context.region referent handle after) :
    ∃ resident, after.Stores handle resident ∧ resident.Initialized ∧
      resident.type = .reference .unique (.runtimeRegion context.region) value.type ∧
      Permitted after .owner .owned handle := by
  obtain ⟨layout,allocation⟩ := allocated
  have fresh : handle.root = before.nextRoot := by cases allocation; rfl
  have loans : withHandle.loans = before.loans := by cases allocation; rfl
  have referentBound : referent.root < before.nextRoot := by
    obtain ⟨root,_,found,_⟩ := World.resident_iff_stores.mpr stored
    exact World.root_bound well found
  cases borrowed with
  | @borrow actual middle parent found _ _ _ _ _ _ _ _ written =>
    have original : actual = value := Option.some.inj
      (found.symm.trans ((allocation.read well referent).trans stored))
    subst actual
    have handleStored := World.write_read_inside written []
    simp only [List.append_nil,Value.atPath] at handleStored
    have finalStored :
        ({ middle with loans := withHandle.loans.set withHandle.nextLoan ⟨withHandle.nextLoan,parent,referent,.unique,context.region,true⟩, nextOwner := withHandle.nextOwner+1, nextLoan := withHandle.nextLoan+1 }).Stores handle
          (.resident withHandle.nextOwner (.reference .unique (.runtimeRegion context.region) value.type)
            (.reference withHandle.nextLoan) true []) := handleStored
    refine ⟨_,finalStored,?_,rfl,?_⟩
    · intro path resident inside
      cases inside with
      | root => exact ⟨rfl,by simp [Value.fields]⟩
      | field selected _ => simp [Value.fields] at selected
    · constructor
      · exact (Option.bind_eq_some_iff.mp finalStored).imp fun _ selected => selected.1
      · intro id loan selected live overlap _
        by_cases same : id = withHandle.nextLoan
        · subst id
          have identity : loan = ⟨withHandle.nextLoan,parent,referent,.unique,context.region,true⟩ :=
            Option.some.inj (selected.symm.trans (Table.get_set _ _ _))
          subst loan
          have impossible : before.nextRoot = referent.root := fresh.symm.trans overlap.1
          exact Nat.lt_irrefl _ (impossible ▸ referentBound)
        · have old : before.loans.get id = some loan := by
            simpa only [Table.get_set_other _ _ _ _ same,loans] using selected
          have bound := World.live_loan_root_bound well old live
          have impossible : before.nextRoot = loan.referent.root := fresh.symm.trans overlap.1
          exact Nat.lt_irrefl _ (impossible ▸ bound)

/-- Progress at the hook-dispatch boundary. Allocation and borrowing are
the actual resource prerequisites; admitted declarations produce the body.
The hook itself may diverge, so this does not assume cleanup termination. -/
theorem destroyHook_progress {program : Kernel.Program} {before : State} {context : Context}
    {address : Address} {authority : Authority} {next : Task} {value : Value}
    {id : DeclId} {data : DataDefinition} {hook : DeclId} {arguments : List Term}
    {substitution : Substitution} {handle : Address} {withHandle after : World}
    (valid : Specification.WellFormed program) (typed : Typing.WorldTyped program before.world)
    (task : before.task = .destroy context address authority next)
    (stored : before.world.Stores address value) (initialized : value.Initialized)
    (nominal : value.type = .nominal id arguments)
    (selected : program.declarations.data id = some data) (drops : data.dropHook = some hook)
    (instantiated : Instantiates data.generics arguments substitution)
    (kinded : ∀ argument ∈ arguments, Kinding program.declarations ⟨[],[],0,data.header.module,false,{}⟩ argument argument.kind)
    (requirements : ConstraintsHold program.declarations ⟨[],[],0,data.header.module,false,{}⟩ substitution data.requirements)
    (allocated : Temporary program context (.reference .unique (.runtimeRegion context.region) value.type)
      before.world handle withHandle)
    (borrowed : Borrows program.declarations withHandle authority .unique context.region address handle after) :
    ∃ function formal,
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
  obtain ⟨resident,handleStored,initialized,residentType,permission⟩ :=
    allocated.borrowed_handle typed.1 stored borrowed
  have captures := dispatch.2.2.2.1
  refine ⟨function,formal,parameters,formalType,contract,?_,?_,step,afterTyped⟩
  · constructor
    · simp [parameters,captures]
    · intro index input found
      cases index with
      | zero =>
        simp only [List.getElem?_cons_zero,Option.some.injEq] at found
        subst input
        exact Or.inr ⟨by simp [captures],by simp [captures]⟩
      | succ => simp at found
  · refine ⟨afterTyped,by simp,?_,?_⟩
    · intro input member
      simp only [List.mem_singleton] at member
      subst input
      exact ⟨resident,handleStored,initialized,residentType.trans formalType.symm,permission⟩
    · intro left first right last different _
      simp only [List.mem_singleton] at first last
      exact False.elim (different (first.trans last.symm))

end Execution
end Glorious.Language
