import GloriousLanguage.ControlLocalOrigin

/-! Labels, reservations and pattern witnesses retain the address support
of their actual dynamic products through ordinary control transfer. -/
namespace Glorious.Language.Execution

open Kernel

theorem LabelRoute.control_support {frames inner outer : List Frame} {brand region : Identity}
    {context : Context} {type : Term} {limit : Identity}
    (route : LabelRoute frames brand inner context region type outer)
    (bounded : RootSupport.Below (frames.flatMap Frame.rootSupport) limit) :
    RootSupport.Below context.rootSupport limit ∧ RootSupport.Below (outer.flatMap Frame.rootSupport) limit := by
  rw [route.1] at bounded
  simp only [List.flatMap_append,List.flatMap_cons,Frame.rootSupport,RootSupport.below_append] at bounded
  exact bounded.2

theorem AbandonedRoots.root_support {world : World} {frames : List Frame} {kept roots : List Identity}
    (well : world.WellFormed) (selected : AbandonedRoots world frames kept roots) :
    RootSupport.Below roots world.nextRoot := by
  intro id member
  obtain ⟨root,found,_⟩ := (selected.2 id).mp member
  exact World.root_bound well found

theorem ReservationInputs.root_support {world : World} {available : Availability} {access : Access}
    {formals : List Local} {inputs : List InvocationInput} (well : world.WellFormed)
    (prepared : ReservationInputs world available access formals inputs) :
    RootSupport.Below (inputs.flatMap InvocationInput.rootSupport) world.nextRoot := by
  simp only [RootSupport.below_flatMap,InvocationInput.rootSupport,RootSupport.below_cons,
    RootSupport.below_nil,and_true]
  intro input member
  exact (prepared.2.2.2 input member).1.root_bound well

theorem DisposesReservations.root_support {context : Context} {places : List ResolvedPlace} {next : Task}
    {limit : Identity} (contextBound : RootSupport.Below context.rootSupport limit)
    (placesBound : RootSupport.Below (places.map (fun place => place.address.root)) limit)
    (continued : RootSupport.Below next.rootSupport limit) :
    RootSupport.Below (DisposesReservations context places next).rootSupport limit := by
  induction places with
  | nil => exact continued
  | cons _ _ ih =>
    simp only [List.map_cons,RootSupport.below_cons] at placesBound
    exact RootSupport.below_append.mpr ⟨contextBound,RootSupport.below_cons.mpr ⟨placesBound.1,ih placesBound.2⟩⟩

theorem ControlStep.control_support {program : Kernel.Program} {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (taskBound : RootSupport.Below before.task.rootSupport before.world.nextRoot)
    (frameBound : RootSupport.Below (before.frames.flatMap Frame.rootSupport) before.world.nextRoot)
    (step : ControlStep program before event after) :
    RootSupport.Below after.task.rootSupport after.world.nextRoot ∧
      RootSupport.Below (after.frames.flatMap Frame.rootSupport) after.world.nextRoot := by
  have frontier := step.suspensionExtension.counter
  have taskAfter := taskBound.mono frontier
  have framesAfter := frameBound.mono frontier
  have afterWell := (step.worldTyped valid inventory typed).1
  cases step
  all_goals simp_all only [Task.rootSupport,EntrySource.rootSupport,List.flatMap_append,List.map_cons,List.map_nil,
    RootSupport.below_append,RootSupport.below_cons,RootSupport.below_nil,true_and,and_true,CloseRegions.root_support]
  case labelCall argument =>
    obtain ⟨_,_,resolved⟩ := argument
    exact Context.resolves_root_bound typed.1 taskBound resolved
  case leave route kept roots _ =>
    obtain ⟨outerBound,restBound⟩ := route.control_support framesAfter
    exact ⟨⟨roots.root_support afterWell,outerBound,kept.root_bound⟩,restBound⟩
  case reserve allocated created =>
    exact Context.bind_root_support taskAfter (Nat.lt_of_lt_of_le allocated.root_bound created.suspensionExtension.counter)
  case closeAvailable resolved _ _ => exact Context.resolves_root_bound typed.1 taskBound resolved
  case destroyAvailable found permission _ _ =>
    apply DisposesReservations.root_support taskAfter.1 ?_ taskAfter.2.2
    apply RootSupport.Below.mono (last := _) (first := before.world.nextRoot) ?_ frontier
    rw [RootSupport.below_map]
    intro place member
    exact World.reserved_root_bound typed.1 found permission.1 (List.mem_reverse.mp member)
  case contextualCall receiver _ _ _ _ witness _ _ _ _ _ captures inputs _ _ =>
    exact ⟨Nat.lt_of_lt_of_le (receiver.root_bound typed.1) frontier,
      Nat.lt_of_lt_of_le (witness.root_bound typed.1) frontier,
      (captures.root_support typed.1).mono frontier,(inputs.root_support typed.1 taskBound).mono frontier⟩
  case positiveTest allocated tested =>
    exact Context.bind_root_support taskAfter (Nat.lt_of_lt_of_le allocated.root_bound tested.suspensionExtension.counter)
  case negativeTest allocated tested =>
    exact Context.bind_root_support taskAfter (Nat.lt_of_lt_of_le allocated.root_bound tested.suspensionExtension.counter)

end Glorious.Language.Execution
