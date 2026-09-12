import GloriousLanguage.DropHandle
import GloriousLanguage.DropObservation
import GloriousLanguage.ForeignRuntimePreservation

/-! The actual destructor dispatch establishes common invocation admission on
its complete caller stack, including host callback exposure. The hook's fresh
argument handle is not an assumed input or an erased-stack reconstruction. -/
namespace Glorious.Language.Execution

open Kernel Contracts

theorem LocalStep.hook_invocation_start {program : Kernel.Program} {host : Foreign.Model}
    {before entering : State} {address : Address} {hook : DeclId}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (control : before.ControlWellFormed) (registry : host.AuthoritiesRecorded before.world before.hostState)
    (callbacks : host.CallbacksWellFormed before)
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
  have afterTyped := dispatch.worldTyped valid inventory typed
  have afterControl := Step.controlWellFormed valid inventory lawful typed control (Or.inl dispatch)
  have afterRegistry := Step.host_authorities valid inventory lawful typed control registry (Or.inl dispatch)
  have afterCallbacks := Step.callbacks valid inventory lawful typed control.suspensions callbacks (Or.inl dispatch)
  cases dispatch with
  | @destroyHook caller _ authority next value _ function allocated handle after loan task stored _ _ selected temporary borrowed loanId =>
    obtain ⟨formal,parameters,formalType⟩ := selected.2.2.parameter
    have headFormal : function.parameters.head! = formal := by rw [parameters]; rfl
    obtain ⟨root,found,_,whole,privateRoot⟩ := temporary.borrowed_handle_private typed.1 stored borrowed
    obtain ⟨self,handleStored,_⟩ := borrowed.created_handle
    have handleType := afterTyped.stored_root_type whole handleStored
      (AddressType.root_transport borrowed.locations whole temporary.addressType)
    have initialized : (Value.resident allocated.nextOwner (.reference .unique (.runtimeRegion caller.region) self)
        (.reference allocated.nextLoan) true []).Initialized := by
      intro path resident residentAt
      cases residentAt with
      | root => exact ⟨rfl,by simp [Value.fields]⟩
      | field field _ => simp [Value.fields] at field
    have permission : Permitted after .owner .owned handle := by
      refine ⟨⟨root,found⟩,?_⟩
      intro id loan found live overlap conflict
      exact privateRoot.1 id loan found live overlap.1.symm
    refine ⟨caller,function,authority,handle,loan,next,value,task,stored,selected,rfl,rfl,
      ⟨?_,?_,afterControl,afterRegistry,afterCallbacks,
        { caller with unsafeAllowed := false },.supplied _,false,rfl,rfl,Or.inl ⟨rfl,rfl,rfl⟩,borrowed.region_live,
          by intro needsUnsafe; have safe := selected.2.2.1.2.2.2; cases safe.symm.trans needsUnsafe⟩⟩
    · refine ⟨afterTyped,by simp,?_,?_⟩
      · intro input member
        have same : input = ⟨.argument 0,function.parameters.head!,handle,.owner,.owned⟩ := List.mem_singleton.mp member
        subst input
        exact ⟨_,handleStored,initialized,by simpa only [headFormal,formalType] using handleType,permission⟩
      · intro left leftMem right rightMem different overlap
        exact False.elim (different ((List.mem_singleton.mp leftMem).trans (List.mem_singleton.mp rightMem).symm))
    · constructor
      · change [function.parameters.head!] = function.captures ++ function.parameters
        rw [headFormal,selected.2.2.2.1,parameters]
        rfl
      · intro index input inputAt
        cases index with
        | zero =>
          simp only [List.getElem?_cons_zero,Option.some.injEq] at inputAt
          subst input
          exact Or.inr ⟨by rw [selected.2.2.2.1]; exact Nat.le_refl 0,
            by simp only [selected.2.2.2.1,List.length_nil,Nat.sub_zero],rfl⟩
        | succ index => simp only [List.getElem?_cons_succ,List.getElem?_nil,reduceCtorEq] at inputAt

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
    dispatch.hook_invocation_start valid inventory lawful typed control registry callbacks
  have contract := admitted.contracts _ _ _ _ selected
  refine ⟨caller,function,authority,handle,loan,next,value,task,stored,frames,initial,contract,?_⟩
  intro events finish run
  exact ⟨(contract.2.1 host _ _ entering events finish lawful initial run).1,
    fun _ normal => initial.normal_observation run normal⟩

end Glorious.Language.Execution
