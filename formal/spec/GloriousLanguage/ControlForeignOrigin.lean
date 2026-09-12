import GloriousLanguage.ControlEffectOrigin

/-! Host sessions keep only actual exposed addresses. Fresh publication,
callback entry and callback return preserve their support through the same
allocation, invocation lease and ordinary transfer producers. -/
namespace Glorious.Language

theorem World.stores_root_bound {world : World} {address : Address} {value : Value}
    (well : world.WellFormed) (stored : world.Stores address value) : address.root < world.nextRoot := by
  obtain ⟨root,found,_⟩ := Option.bind_eq_some_iff.mp stored
  exact World.address_root_bound well found

theorem Transfers.source_root_bound {program : Program} {before after : World}
    {source destination : Address} {authority : Authority} (well : before.WellFormed)
    (transferred : Transfers program before authority source destination after) : source.root < after.nextRoot := by
  have bounded : source.root < before.nextRoot := by
    cases transferred with
    | move stored _ _ _ _ _ _ _ => exact World.stores_root_bound well stored
  exact Nat.lt_of_lt_of_le bounded transferred.suspensionExtension.counter

namespace Kernel

theorem LendsResident.lease_root_support {program : Language.Program} {before after : World}
    {activation scope region address authority access lease permission}
    (well : before.WellFormed)
    (lent : LendsResident program activation scope region before address authority access lease permission after) :
    RootSupport.Below (lease.toList.map (fun lease => lease.handle.root)) after.nextRoot := by
  by_cases owned : access = .owned
  · subst access
    cases lent with
    | owned => simp
    | lent access _ _ _ => simp at access
  · obtain ⟨witness,root,_,_,_,selected,_,_,found,_⟩ := lent.lease_origin owned
    rw [selected]
    simp only [Option.toList_some,List.map_cons,List.map_nil,RootSupport.below_cons,RootSupport.below_nil,and_true]
    exact World.address_root_bound (lent.wellFormed well) found

end Kernel

namespace Execution

open Kernel

theorem PrimitiveStep.control_support {program : Kernel.Program} {before after : State} {event : Option Event}
    (taskBound : RootSupport.Below before.task.rootSupport before.world.nextRoot)
    (frameBound : RootSupport.Below (before.frames.flatMap Frame.rootSupport) before.world.nextRoot)
    (step : PrimitiveStep program before event after) :
    RootSupport.Below after.task.rootSupport after.world.nextRoot ∧
      RootSupport.Below (after.frames.flatMap Frame.rootSupport) after.world.nextRoot := by
  have frontier := step.suspensionExtension.counter
  have taskAfter := taskBound.mono frontier
  have framesAfter := frameBound.mono frontier
  cases step <;> simp_all only [Task.rootSupport,RootSupport.below_append,RootSupport.below_cons,
    RootSupport.below_nil,true_and]

theorem CaptureInputs.root_support {world : World} {receiver : Address} {authority : Authority} {access : Access}
    {formals : List Local} {inputs : List InvocationInput} (well : world.WellFormed)
    (prepared : CaptureInputs world receiver authority access formals inputs) :
    RootSupport.Below (inputs.flatMap InvocationInput.rootSupport) world.nextRoot := by
  simp only [RootSupport.below_flatMap,InvocationInput.rootSupport,RootSupport.below_cons,
    RootSupport.below_nil,and_true]
  intro input member
  exact (prepared.2 input member).2.root_bound well

theorem ForeignSession.known_root_support {session : ForeignSession} {limit : Identity}
    (bounded : RootSupport.Below session.rootSupport limit) :
    RootSupport.Below (session.known.map (fun place => place.address.root)) limit := by
  simp only [ForeignSession.rootSupport,ForeignCall.rootSupport,RootSupport.below_append,RootSupport.below_cons] at bounded
  simpa only [ForeignSession.known,List.map_append,List.map_map,Function.comp_def,RootSupport.below_append] using
    And.intro bounded.1.2.2 bounded.2

theorem ForeignSession.returned_root_support {session : ForeignSession} {result : Address} {state : List Nat}
    {limit : Identity} (bounded : RootSupport.Below session.rootSupport limit) (value : result.root < limit) :
    RootSupport.Below (session.returned result state).rootSupport limit := by
  simp only [ForeignSession.rootSupport,RootSupport.below_append] at bounded
  simp only [ForeignSession.returned,ForeignSession.rootSupport,List.map_cons,
    RootSupport.below_append,RootSupport.below_cons]
  exact ⟨bounded.1,value,bounded.2⟩

end Execution

namespace Foreign

open Kernel Execution

theorem CallbackInputs.root_support {world : World} {formals : List Local}
    {arguments : List ResolvedPlace} {inputs : List InvocationInput}
    (well : world.WellFormed) (prepared : CallbackInputs world formals arguments inputs) :
    RootSupport.Below (inputs.flatMap InvocationInput.rootSupport) world.nextRoot := by
  rw [prepared.1,RootSupport.below_flatMap]
  intro input member
  obtain ⟨⟨⟨formal,argument⟩,index⟩,pairMember,equal⟩ := List.mem_map.mp member
  subst input
  have argumentAt := (List.getElem?_zip_eq_some.mp (List.mem_zipIdx_iff_getElem?.mp pairMember)).2
  obtain ⟨_,_,_,_,_,_,permission⟩ := prepared.2.get_right argumentAt
  exact RootSupport.below_cons.mpr ⟨permission.root_bound well,RootSupport.below_nil _⟩

theorem AmbientExposed.root_support {frames : List Frame} {limit : Identity}
    (bounded : RootSupport.Below (frames.flatMap Frame.rootSupport) limit) :
    RootSupport.Below ((AmbientExposed frames).map (fun place => place.address.root)) limit := by
  induction frames with
  | nil => simp [AmbientExposed]
  | cons frame rest ih =>
    simp only [List.flatMap_cons,RootSupport.below_append] at bounded
    cases frame <;> simp only [AmbientExposed,List.flatMap_cons,List.nil_append,List.map_append]
    all_goals try exact ih bounded.2
    exact RootSupport.below_append.mpr ⟨ForeignSession.known_root_support (RootSupport.below_append.mp bounded.1).1,ih bounded.2⟩

theorem FreshExposed.root_support {before after : World} (well : after.WellFormed) :
    RootSupport.Below ((FreshExposed before after).map (fun place => place.address.root)) after.nextRoot := by
  rw [RootSupport.below_map]
  intro place exposed
  obtain ⟨⟨id,root⟩,member,selected⟩ := List.mem_filterMap.mp exposed
  dsimp only at selected
  split at selected
  · cases selected
    exact World.root_bound well (well.1.get_of_mem member)
  · cases selected

theorem _root_.Glorious.Language.Execution.ForeignSession.advance_root_support
    {session : ForeignSession} {before after : World} {state : List Nat}
    (well : after.WellFormed) (bounded : RootSupport.Below session.rootSupport after.nextRoot) :
    RootSupport.Below (session.advance before after state).rootSupport after.nextRoot := by
  simp only [ForeignSession.rootSupport,RootSupport.below_append] at bounded
  simp only [ForeignSession.advance,ForeignSession.rootSupport,List.map_append,RootSupport.below_append]
  exact ⟨bounded.1,bounded.2,FreshExposed.root_support well⟩

theorem CallbackReturnTask.root_support {session : ForeignSession} {registration : CallbackEntry} {result : Address}
    {lease : Option ReceiverLease} {next : Code} {limit : Identity}
    (sessionBound : RootSupport.Below session.rootSupport limit) (resultBound : result.root < limit)
    (leaseBound : RootSupport.Below (lease.toList.map (fun lease => lease.handle.root)) limit) :
    RootSupport.Below (CallbackReturnTask session registration result lease next).rootSupport limit := by
  cases lease with
  | none => exact RootSupport.below_append.mpr ⟨sessionBound,by simpa using resultBound⟩
  | some lease =>
    have contextBound := (RootSupport.below_append.mp (RootSupport.below_append.mp sessionBound).1).1
    have handleBound : lease.handle.root < limit := by simpa using leaseBound
    simp only [CallbackReturnTask,Task.rootSupport,RootSupport.below_append,RootSupport.below_cons,
      RootSupport.below_nil,and_true]
    exact ⟨contextBound,handleBound,handleBound,sessionBound,resultBound⟩

theorem Step.control_support {program : Kernel.Program} {model : Model} {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : model.Lawful program) (typed : Typing.WorldTyped program before.world)
    (taskBound : RootSupport.Below before.task.rootSupport before.world.nextRoot)
    (frameBound : RootSupport.Below (before.frames.flatMap Frame.rootSupport) before.world.nextRoot)
    (step : Step program model before event after) :
    RootSupport.Below after.task.rootSupport after.world.nextRoot ∧
      RootSupport.Below (after.frames.flatMap Frame.rootSupport) after.world.nextRoot := by
  have frontier := (step.suspensionExtension lawful typed.1).counter
  have taskAfter := taskBound.mono frontier
  have framesAfter := frameBound.mono frontier
  have afterTyped := step.worldTyped valid inventory lawful typed
  have afterWell := afterTyped.1
  cases step
  all_goals simp_all only [Task.rootSupport,Frame.rootSupport,EntrySource.rootSupport,List.flatMap_cons,List.flatMap_append,
    RootSupport.below_append,RootSupport.below_cons,RootSupport.below_nil,and_true]
  case enter kept _ _ _ =>
    exact RootSupport.below_append.mpr ⟨RootSupport.below_append.mpr
      ⟨taskAfter.1,RootSupport.below_cons.mpr ⟨taskAfter.2.1,kept.root_support⟩⟩,
      AmbientExposed.root_support framesAfter⟩
  case host => exact ForeignSession.advance_root_support afterWell taskAfter
  case result selected active transition _ transferred =>
    have hostWell := (lawful.host_worldTyped valid inventory typed selected active transition).1
    have contextBound := (RootSupport.below_append.mp (RootSupport.below_append.mp taskAfter).1).1
    exact ⟨transferred.source_root_bound hostWell,contextBound⟩
  case callback selected active transition _ lent captures inputs consumed =>
    have hostWell := (lawful.host_worldTyped valid inventory typed selected active transition).1
    have lendWell := lent.wellFormed hostWell
    have hostFrontier := (lawful.host_suspensionExtension typed.1 selected active transition).counter
    have consumedFrontier := consumed.suspensionExtension.counter
    have hostToFinal := Nat.le_trans lent.suspensionExtension.counter consumedFrontier
    have contextBound := (RootSupport.below_append.mp (RootSupport.below_append.mp taskAfter).1).1
    refine ⟨⟨contextBound,(captures.root_support lendWell).mono consumedFrontier,
      (inputs.root_support lendWell).mono consumedFrontier⟩,?_,
      (lent.lease_root_support hostWell).mono consumedFrontier⟩
    exact (ForeignSession.advance_root_support hostWell (taskBound.mono hostFrontier)).mono hostToFinal
  case callbackResult kept retired =>
    exact CallbackReturnTask.root_support framesAfter.1.1
      (Nat.lt_of_lt_of_le kept.root_bound retired.suspensionExtension.counter) framesAfter.1.2
  case callbackReturned => exact ForeignSession.returned_root_support taskBound.1 taskBound.2

end Foreign
end Glorious.Language
