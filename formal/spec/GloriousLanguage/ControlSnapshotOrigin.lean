import GloriousLanguage.ControlOrigin
import GloriousLanguage.SuspensionOwnership

/-! Actual capture and replay preserve the historical address support of
saved execution, including nested hook cleanup tasks. Relocation uses the
machine's one address map; no copied-control support is independently guessed. -/
namespace Glorious.Language.Execution

open _root_.Glorious.Language.Kernel

theorem Routes.control_support {program : Kernel.Program} {before : State}
    {operation : DeclId} {arguments : List Term} {payload : List ResolvedPlace}
    {inner outer : List Frame} {handler : InstalledHandler} {owns : Bool} {arm : OperationArm}
    {limit : Identity} (routes : Routes program before operation arguments payload inner handler owns arm outer)
    (bounded : RootSupport.Below (before.frames.flatMap Frame.rootSupport) limit) :
    RootSupport.Below (inner.flatMap Frame.rootSupport) limit ∧
      RootSupport.Below handler.rootSupport limit ∧ RootSupport.Below (outer.flatMap Frame.rootSupport) limit := by
  rw [routes.1] at bounded
  simpa only [List.flatMap_append,List.flatMap_cons,Frame.rootSupport,RootSupport.below_append] using bounded

/-- The save frontier is the actual post-payload world, before allocating
the continuation handle. Both capture forms use exactly the routed frames. -/
theorem EffectStep.created_control_origin {program : Kernel.Program} {before after : State} {id : Identity}
    (control : before.ControlWellFormed)
    (step : EffectStep program before (some (.suspend id)) after) :
    ∃ suspension, after.resumptions.get id = some suspension ∧
      RootSupport.Below suspension.controlRootSupport suspension.captureRootLimit := by
  cases step with
  | suspend task selected terminal quantity bound continuation routes started keptTransfer roots permission homes created plan suspension =>
    subst suspension
    have taskBound := control.task
    rw [task] at taskBound
    have contextBound := (RootSupport.below_append.mp taskBound).1
    obtain ⟨innerBound,handlerBound,_⟩ := routes.control_support control.frames
    have frontier := Nat.le_trans started.suspensionExtension.counter keptTransfer.suspensionExtension.counter
    refine ⟨_,Table.get_set _ _ _,?_⟩
    simp only [Suspension.controlRootSupport,RootSupport.below_append]
    exact ⟨⟨contextBound.mono frontier,handlerBound.mono frontier⟩,innerBound.mono frontier⟩
  | suspendTailArm task selected terminal quantity bound contains continuation routes started keptTransfer roots permission homes plan suspension =>
    subst suspension
    have taskBound := control.task
    rw [task] at taskBound
    have contextBound := (RootSupport.below_append.mp taskBound).1
    obtain ⟨innerBound,handlerBound,_⟩ := routes.control_support control.frames
    have frontier := Nat.le_trans started.suspensionExtension.counter keptTransfer.suspensionExtension.counter
    refine ⟨_,Table.get_set _ _ _,?_⟩
    simp only [Suspension.controlRootSupport,RootSupport.below_append]
    exact ⟨⟨contextBound.mono frontier,handlerBound.mono frontier⟩,innerBound.mono frontier⟩

theorem Relocation.root_support_bound {map : Relocation} {root limit : Identity}
    (bounded : root < limit) : map.root root < map.rootBase + limit := by
  unfold Relocation.root relocateId
  split
  · exact Nat.add_lt_add_left bounded _
  · exact Nat.lt_of_lt_of_le bounded (Nat.le_add_left _ _)

theorem Relocation.context_root_support {map : Relocation} {context : Context} {limit : Identity}
    (bounded : RootSupport.Below context.rootSupport limit) :
    RootSupport.Below (map.context context).rootSupport (map.rootBase + limit) := by
  have envBound : ∀ binding ∈ context.environment,
      (map.binding binding).address.root < map.rootBase + limit := by
    intro binding inner
    exact Relocation.root_support_bound (bounded binding.address.root (by
      simp only [Context.rootSupport]
      exact List.mem_append_left _ (List.mem_map.mpr ⟨binding,inner,rfl⟩)))
  have contractsBound : ∀ contract ∈ context.resourceContracts, ∀ binding ∈ contract.inputs,
      (map.binding binding).address.root < map.rootBase + limit := by
    intro contract inner binding inner2
    exact Relocation.root_support_bound (bounded binding.address.root (by
      simp only [Context.rootSupport]
      exact List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨contract,inner,(List.mem_map.mpr ⟨binding,inner2,rfl⟩)⟩)))
  have envLift : ∀ (binding : Binding), binding ∈ context.environment →
      (map.binding binding).address.root < map.rootBase + limit := by
    intro binding inner
    exact Relocation.root_support_bound (bounded binding.address.root (by
      simp only [Context.rootSupport]
      exact List.mem_append_left _ (List.mem_map.mpr ⟨binding,inner,rfl⟩)))
  have contractsLift : ∀ (contract : _), contract ∈ context.resourceContracts →
      ∀ (binding : Binding), binding ∈ contract.inputs →
      (map.binding binding).address.root < map.rootBase + limit := by
    intro contract outer binding inner
    exact Relocation.root_support_bound (bounded binding.address.root (by
      simp only [Context.rootSupport]
      exact List.mem_append_right _
        (List.mem_flatMap.mpr ⟨contract,outer,List.mem_map.mpr ⟨binding,inner,rfl⟩⟩)))
  intro root member
  rcases List.mem_append.mp (by
    simpa only [Context.rootSupport,Relocation.context] using member) with h | h
  · obtain ⟨binding,inner,same⟩ := List.mem_map.mp h
    obtain ⟨original,member,sameBinding⟩ := List.mem_map.mp inner
    rw [← sameBinding] at same
    exact same ▸ envLift original member
  · obtain ⟨contract,contractMember,rootMember⟩ := List.mem_flatMap.mp h
    obtain ⟨original,member,sameContract⟩ := List.mem_map.mp contractMember
    rw [← sameContract] at rootMember
    obtain ⟨binding,bindingMember,sameBinding⟩ := List.mem_map.mp rootMember
    obtain ⟨preImage,preMember,samePreImage⟩ := List.mem_map.mp bindingMember
    rw [← samePreImage] at sameBinding
    exact sameBinding ▸ contractsLift original member preImage preMember

theorem Relocation.installed_root_support {map : Relocation} {handler : InstalledHandler} {limit : Identity}
    (bounded : RootSupport.Below handler.rootSupport limit) :
    RootSupport.Below (map.installed handler).rootSupport (map.rootBase + limit) := by
  simp only [InstalledHandler.rootSupport,RootSupport.below_append] at bounded
  simp only [Relocation.installed,InstalledHandler.rootSupport,RootSupport.below_append]
  exact ⟨⟨map.context_root_support bounded.1.1,map.context_root_support bounded.1.2⟩,
    map.context_root_support bounded.2⟩

theorem Relocation.frame_root_support {map : Relocation} {frame : Frame} {limit : Identity}
    (bounded : RootSupport.Below frame.rootSupport limit) :
    RootSupport.Below (map.frame frame).rootSupport (map.rootBase + limit) := by
  cases frame <;> simp only [Relocation.frame,Frame.rootSupport,RootSupport.below_append,
    RootSupport.below_cons,RootSupport.below_nil,and_true] at bounded ⊢
  case binding => exact ⟨map.context_root_support bounded.1,map.root_support_bound bounded.2⟩
  case activation => exact map.context_root_support bounded
  case scope => exact map.context_root_support bounded
  case label => exact map.context_root_support bounded
  case handler => exact map.installed_root_support bounded
  case serviced => exact ⟨map.installed_root_support bounded.1,map.context_root_support bounded.2⟩
  case completion => exact ⟨map.installed_root_support bounded.1,map.context_root_support bounded.2⟩
  case resumed => exact map.context_root_support bounded
  case tailResume => exact bounded.mono (Nat.le_add_left _ _)
  case hook =>
    exact ⟨bounded.1.mono (Nat.le_add_left _ _),Nat.lt_of_lt_of_le bounded.2.1 (Nat.le_add_left _ _),
      Nat.lt_of_lt_of_le bounded.2.2.1 (Nat.le_add_left _ _),bounded.2.2.2.mono (Nat.le_add_left _ _)⟩
  case hostCallback => exact ⟨bounded.1.mono (Nat.le_add_left _ _),bounded.2.mono (Nat.le_add_left _ _)⟩

/-- Replay of every permitted snapshot copies the saved address graph
within the real enlarged world. Unrelocated frames also retain their bounds. -/
theorem CopiesSnapshot.control_support {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation} (copied : CopiesSnapshot program before suspension map after)
    (bounded : RootSupport.Below suspension.controlRootSupport before.world.nextRoot) :
    RootSupport.Below (map.context suspension.context).rootSupport after.world.nextRoot ∧
      RootSupport.Below (map.installed suspension.handler).rootSupport after.world.nextRoot ∧
      RootSupport.Below ((suspension.frames.map map.frame).flatMap Frame.rootSupport) after.world.nextRoot := by
  simp only [Suspension.controlRootSupport,RootSupport.below_append] at bounded
  rw [copied.result]
  refine ⟨map.context_root_support bounded.1.1,map.installed_root_support bounded.1.2,?_⟩
  rw [RootSupport.below_flatMap]
  intro frame member
  obtain ⟨original,originalMember,equal⟩ := List.mem_map.mp member
  subst frame
  exact map.frame_root_support (RootSupport.below_flatMap.mp bounded.2 original originalMember)

theorem ResumptionChange.saved_property {before after : State} {event : Option Event} {property : Suspension → Prop}
    (change : ResumptionChange before event after)
    (budget : ∀ suspension remaining used active, property suspension →
      property { suspension with remaining := remaining, used := used, active := active })
    (saved : ∀ id suspension, before.resumptions.get id = some suspension → property suspension)
    (created : ∀ id, event = some (.suspend id) → ∃ suspension,
      after.resumptions.get id = some suspension ∧ property suspension) :
    ∀ id suspension, after.resumptions.get id = some suspension → property suspension := by
  cases change with
  | unchanged table _ _ _ => simpa only [table] using saved
  | create _ _ _ _ _ _ table _ =>
    intro id suspension found
    by_cases same : id = before.nextContinuation
    · subst id
      obtain ⟨actual,present,bounded⟩ := created _ rfl
      exact Option.some.inj (found.symm.trans present) ▸ bounded
    · exact saved id suspension (by simpa only [table,Table.get_set_other _ _ _ _ same] using found)
  | @last _ target original present _ _ table _ =>
    intro id suspension found
    by_cases same : id = target
    · subst id
      rw [table,Table.get_set] at found
      cases found
      exact budget original _ _ _ (saved target original present)
    · exact saved id suspension (by simpa only [table,Table.get_set_other _ _ _ _ same] using found)
  | @copy _ target original present _ _ table _ =>
    intro id suspension found
    by_cases same : id = target
    · subst id
      rw [table,Table.get_set] at found
      cases found
      exact budget original _ _ _ (saved target original present)
    · exact saved id suspension (by simpa only [table,Table.get_set_other _ _ _ _ same] using found)
  | @cancel _ target original present _ _ table _ =>
    intro id suspension found
    by_cases same : id = target
    · subst id
      rw [table,Table.get_set] at found
      cases found
      exact budget original _ _ _ (saved target original present)
    · exact saved id suspension (by simpa only [table,Table.get_set_other _ _ _ _ same] using found)

theorem ResumptionChange.saved_control_origin {before after : State} {event : Option Event}
    (change : ResumptionChange before event after)
    (saved : ∀ id suspension, before.resumptions.get id = some suspension →
      RootSupport.Below suspension.controlRootSupport suspension.captureRootLimit)
    (created : ∀ id, event = some (.suspend id) → ∃ suspension,
      after.resumptions.get id = some suspension ∧
      RootSupport.Below suspension.controlRootSupport suspension.captureRootLimit) :
    ∀ id suspension, after.resumptions.get id = some suspension →
      RootSupport.Below suspension.controlRootSupport suspension.captureRootLimit :=
  change.saved_property (fun _ _ _ _ bounded => bounded) saved created

/-- Every actual transition preserves saved address provenance. Capture
establishes it from routed control; replay and cancellation retain it exactly. -/
theorem Step.saved_control_origin {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {event : Option Event} (control : before.ControlWellFormed)
    (step : Step program host before event after) :
    ∀ id suspension, after.resumptions.get id = some suspension →
      RootSupport.Below suspension.controlRootSupport suspension.captureRootLimit := by
  apply step.resumption_change.saved_control_origin control.saved
  intro id equal
  rcases step with localStep | atom | effect | controlStep | primitive | foreign
  · cases localStep <;> cases equal
  · cases atom <;> simp_all <;> split at equal <;> (try split at equal) <;> contradiction
  · rw [equal] at effect
    exact effect.created_control_origin control
  · cases controlStep <;> cases equal
  · cases primitive <;> cases equal
  · cases foreign <;> cases equal

end Glorious.Language.Execution
