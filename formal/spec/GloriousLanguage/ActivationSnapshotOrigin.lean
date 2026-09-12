import GloriousLanguage.ActivationLocalOrigin

/-! Capture and replay use the actual saved control and home inventory.
Relocated activations remain below the enlarged counter, and newly selected
activation identities cannot collide with any previously allocated identity. -/
namespace Glorious.Language.Execution

open Kernel

theorem Routes.activation_support {program : Kernel.Program} {before : State}
    {operation : DeclId} {arguments : List Term} {payload : List ResolvedPlace}
    {inner outer : List Frame} {handler : InstalledHandler} {owns : Bool} {arm : OperationArm}
    {limit : Identity} (routes : Routes program before operation arguments payload inner handler owns arm outer)
    (bounded : RootSupport.Below (before.frames.flatMap Frame.activationSupport) limit) :
    RootSupport.Below (inner.flatMap Frame.activationSupport) limit ∧
      RootSupport.Below handler.activationSupport limit ∧ RootSupport.Below (outer.flatMap Frame.activationSupport) limit := by
  rw [routes.1] at bounded
  simpa only [List.flatMap_append,List.flatMap_cons,Frame.activationSupport,RootSupport.below_append] using bounded

theorem suspendRoots.activationsBelow {world : World} {roots : List Identity} {id limit : Identity}
    (bounded : world.ActivationsBelow limit) : (suspendRoots world roots id).ActivationsBelow limit := by
  intro key root found
  rw [suspendRoots.get] at found
  obtain ⟨original,present,equal⟩ := Option.map_eq_some_iff.mp found
  split at equal
  · subst root
    exact Home.suspended_activationsBelow _ _
  · subst root
    exact bounded key original present

theorem restoreRoots.activationsBelow {world : World} {homes : Table Home} {limit : Identity}
    (bounded : world.ActivationsBelow limit)
    (saved : ∀ id home, homes.get id = some home → home.ActivationsBelow limit) :
    (restoreRoots world homes).ActivationsBelow limit := by
  intro id root found
  rw [restoreRoots.get] at found
  obtain ⟨original,present,rfl⟩ := Option.map_eq_some_iff.mp found
  cases selected : homes.get id with
  | none => exact bounded id original present
  | some home => exact saved id home selected

theorem Relocation.activation_support_bound {map : Relocation} {activation limit : Identity}
    (bounded : activation < limit) : map.activation activation < map.activationBase + limit :=
  relocateId_bound bounded

theorem Relocation.home_activationsBelow {map : Relocation} {home : Home} {limit : Identity}
    (bounded : home.ActivationsBelow limit) : (map.home home).ActivationsBelow (map.activationBase+limit) := by
  cases home with
  | localSlot owner scope | temporary owner scope =>
    simp only [Relocation.home,Home.localSlot_activationsBelow,Home.temporary_activationsBelow] at bounded ⊢
    exact map.activation_support_bound bounded
  | capture | suspended | allocation | staticData | external =>
    simp [Relocation.home,Home.ActivationsBelow,HomeOwnedByActivation]

theorem Relocation.installed_activation_support {map : Relocation} {handler : InstalledHandler} {limit : Identity}
    (bounded : RootSupport.Below handler.activationSupport limit) :
    RootSupport.Below (map.installed handler).activationSupport (map.activationBase+limit) := by
  simp only [InstalledHandler.activationSupport,RootSupport.below_cons,RootSupport.below_nil,and_true] at bounded
  simp only [Relocation.installed,InstalledHandler.activationSupport,Relocation.context,
    RootSupport.below_cons,RootSupport.below_nil,and_true]
  exact ⟨map.activation_support_bound bounded.1,map.activation_support_bound bounded.2.1,
    map.activation_support_bound bounded.2.2⟩

theorem Relocation.frame_activation_support {map : Relocation} {frame : Frame} {limit : Identity}
    (bounded : RootSupport.Below frame.activationSupport limit) :
    RootSupport.Below (map.frame frame).activationSupport (map.activationBase+limit) := by
  have retained := bounded.mono (last := map.activationBase+limit) (Nat.le_add_left _ _)
  cases frame <;> simp only [Relocation.frame,Frame.activationSupport,Relocation.context,
    RootSupport.below_cons,RootSupport.below_nil,and_true] at bounded retained ⊢
  all_goals first
    | exact retained
    | exact map.activation_support_bound bounded
    | exact map.installed_activation_support bounded
    | exact ⟨map.activation_support_bound bounded.1,map.activation_support_bound bounded.2⟩
    | exact ⟨map.activation_support_bound bounded.1,map.installed_activation_support bounded.2⟩

theorem CopiesSnapshot.activation_frontier {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation} (copied : CopiesSnapshot program before suspension map after) :
    before.nextActivation ≤ after.nextActivation := by
  rw [copied.result]
  exact Nat.le_add_left _ _

theorem CopiesSnapshot.activation_support {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation} (copied : CopiesSnapshot program before suspension map after)
    (bounded : RootSupport.Below suspension.controlActivationSupport before.nextActivation) :
    (map.context suspension.context).activation < after.nextActivation ∧
      RootSupport.Below (map.installed suspension.handler).activationSupport after.nextActivation ∧
      RootSupport.Below ((suspension.frames.map map.frame).flatMap Frame.activationSupport) after.nextActivation := by
  simp only [Suspension.controlActivationSupport,RootSupport.below_cons,RootSupport.below_append] at bounded
  rw [copied.result]
  refine ⟨map.activation_support_bound bounded.1.1,map.installed_activation_support bounded.1.2,?_⟩
  rw [RootSupport.below_flatMap]
  intro frame member
  obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
  exact map.frame_activation_support (RootSupport.below_flatMap.mp bounded.2 original present)

theorem CopiesSnapshot.homes_activationsBelow {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation} (copied : CopiesSnapshot program before suspension map after)
    (well : before.world.WellFormed) (bounded : before.world.ActivationsBelow before.nextActivation)
    (origin : suspension.CaptureOrigin)
    (saved : RootSupport.Below suspension.controlActivationSupport before.nextActivation) :
    after.world.ActivationsBelow after.nextActivation := by
  rw [copied.result]
  intro id root found
  rcases Relocation.root_origin well.1 found with original | ⟨old,original,present,_,_,rfl⟩
  · exact (bounded id root original).mono (Nat.le_add_left _ _)
  · change (map.home ((suspension.homes.get old).getD original.home)).ActivationsBelow _
    apply map.home_activationsBelow
    cases selected : suspension.homes.get old with
    | none => exact bounded old original present
    | some home => exact origin.homes_activationsBelow saved selected

/-- The map's selected activation domain also comes from actual owning
frames or saved homes; it cannot reserve arbitrary future identities. -/
theorem SnapshotMap.activations_bounded {program : Kernel.Program} {before : State}
    {suspension : Suspension} {map : Relocation} (selected : SnapshotMap program before suspension map)
    (origin : suspension.CaptureOrigin)
    (bounded : RootSupport.Below suspension.controlActivationSupport before.nextActivation) :
    RootSupport.Below map.activations before.nextActivation := by
  intro activation member
  rcases (selected.activations activation).mp member with ⟨caller,region,frame⟩ | ⟨root,home,scope,_,saved,shape⟩
  · have framesBound := (RootSupport.below_append.mp (RootSupport.below_cons.mp bounded).2).2
    have frameBound := RootSupport.below_flatMap.mp framesBound _ frame
    exact frameBound activation (by simp [Frame.activationSupport])
  · have homeBound := origin.homes_activationsBelow bounded saved
    rcases shape with rfl | rfl
    · exact homeBound activation (Or.inl ⟨scope,rfl⟩)
    · exact homeBound activation (Or.inr ⟨scope,rfl⟩)

/-- Fresh copied activation identities are disjoint from the entire old
allocated range, not just from the finite roots selected for this replay. -/
theorem SnapshotMap.activation_fresh {program : Kernel.Program} {before : State}
    {suspension : Suspension} {map : Relocation} (selected : SnapshotMap program before suspension map)
    {activation : Identity} (member : activation ∈ map.activations) :
    before.nextActivation ≤ map.activation activation := by
  simp only [Relocation.activation,relocateId,if_pos member,selected.activationBase]
  exact Nat.le_add_right _ _

theorem SnapshotMap.activation_injective_below {program : Kernel.Program} {before : State}
    {suspension : Suspension} {map : Relocation} (selected : SnapshotMap program before suspension map)
    {left right : Identity} (leftBound : left < before.nextActivation) (rightBound : right < before.nextActivation)
    (same : map.activation left = map.activation right) : left = right := by
  by_cases one : left ∈ map.activations <;> by_cases two : right ∈ map.activations
  · simpa only [Relocation.activation,relocateId,if_pos one,if_pos two,Nat.add_left_cancel_iff] using same
  · have fresh := selected.activation_fresh one
    have unselected : map.activation right = right := by simp [Relocation.activation,relocateId,two]
    rw [same,unselected] at fresh
    exact False.elim (Nat.not_lt_of_ge fresh rightBound)
  · have fresh := selected.activation_fresh two
    have unselected : map.activation left = left := by simp [Relocation.activation,relocateId,one]
    rw [← same,unselected] at fresh
    exact False.elim (Nat.not_lt_of_ge fresh leftBound)
  · simpa only [Relocation.activation,relocateId,if_neg one,if_neg two] using same

end Glorious.Language.Execution
