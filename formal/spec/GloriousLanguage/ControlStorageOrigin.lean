import GloriousLanguage.ControlSnapshotOrigin
import GloriousLanguage.InvocationLending

/-! Runtime-address support is produced by ordinary place resolution,
allocation, input preparation and pattern planning. These lemmas consume the
same executable products used by invocation and control transitions. -/
namespace Glorious.Language

@[simp] theorem RootSupport.below_map {α : Type} {items : List α}
    {support : α → Identity} {limit : Identity} :
    RootSupport.Below (items.map support) limit ↔ ∀ item ∈ items, support item < limit := by
  simp only [RootSupport.Below,List.mem_map]
  constructor
  · intro bounded item member
    exact bounded _ ⟨item,member,rfl⟩
  · rintro bounded root ⟨item,member,rfl⟩
    exact bounded item member

theorem World.address_root_bound {world : World} (well : world.WellFormed)
    {address : Address} {root : Root} (found : world.root address = some root) :
    address.root < world.nextRoot := World.root_bound well (World.root_found found).1

theorem Permitted.root_bound {world : World} {authority : Authority} {access : Access} {address : Address}
    (well : world.WellFormed) (permitted : Permitted world authority access address) :
    address.root < world.nextRoot := by
  have existsRoot : ∃ root, world.root address = some root := by
    cases authority <;> exact permitted.1
  obtain ⟨root,found⟩ := existsRoot
  exact World.address_root_bound well found

theorem Allocates.root_bound {program : Program} {before after : World}
    {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after) :
    address.root < after.nextRoot := by
  cases allocated
  exact Nat.lt_succ_self _

namespace Kernel

theorem ResolvesProjections.root_bound {world : World} {environment : Environment}
    {base result : Address} {authority permission : Authority} {projections : List Projection}
    (well : world.WellFormed)
    (resolved : ResolvesProjections world environment base authority projections result permission)
    (bounded : base.root < world.nextRoot) : result.root < world.nextRoot := by
  induction resolved with
  | nil => exact bounded
  | field _ _ _ ih => exact ih bounded
  | vacantField => exact bounded
  | index _ _ _ _ _ _ _ ih => exact ih bounded
  | dereference _ _ _ _ found live _ _ ih => exact ih (World.live_loan_root_bound well found live)

theorem ResolvesPlace.root_bound {world : World} {environment : Environment}
    {place : Place} {address : Address} {authority : Authority}
    (well : world.WellFormed)
    (bounded : ∀ binding ∈ environment, binding.address.root < world.nextRoot)
    (resolved : ResolvesPlace world environment place address authority) : address.root < world.nextRoot := by
  cases resolved with
  | localSlot selected projections => exact projections.root_bound well (bounded _ selected.1)

end Kernel

namespace Execution

open _root_.Glorious.Language.Kernel

theorem Context.bind_root_support {context : Context} {localSlot : Local} {address : Address}
    {authority : Authority} {limit : Identity}
    (bounded : RootSupport.Below context.rootSupport limit) (fresh : address.root < limit) :
    RootSupport.Below (context.bind localSlot address authority).rootSupport limit := by
  rw [Context.rootSupport] at bounded
  rw [RootSupport.below_append] at bounded
  rw [Context.rootSupport,Context.bind,RootSupport.below_append]
  refine ⟨?_,bounded.2⟩
  rw [RootSupport.below_map]
  intro entry member
  simp only [List.mem_cons,List.mem_filter] at member
  rcases member with rfl | rest
  · exact fresh
  · exact bounded.1 entry.address.root
      (List.mem_map.mpr ⟨entry,rest.1,rfl⟩)

theorem Context.resolves_root_bound {context : Context} {world : World} {place : Place}
    {address : Address} {authority : Authority} (well : world.WellFormed)
    (bounded : RootSupport.Below context.rootSupport world.nextRoot)
    (resolved : ResolvesPlace world context.environment place address authority) : address.root < world.nextRoot := by
  rw [Context.rootSupport] at bounded
  rw [RootSupport.below_append] at bounded
  exact resolved.root_bound well (RootSupport.below_map.mp bounded.1)

theorem ResolvedOperands.root_support {world : World} {environment : Environment}
    {places : List Place} {operands : List ResolvedPlace} (well : world.WellFormed)
    (resolved : ResolvedOperands world environment places operands) :
    RootSupport.Below (operands.map (fun place => place.address.root)) world.nextRoot := by
  rw [RootSupport.below_map]
  induction resolved with
  | nil => simp
  | cons first _ ih =>
    intro operand member
    rcases List.mem_cons.mp member with rfl | member
    · exact first.2.root_bound well
    · exact ih operand member

theorem Temporary.root_bound {program : Kernel.Program} {context : Context}
    {type : Term} {before after : World} {address : Address}
    (allocated : Temporary program context type before address after) : address.root < after.nextRoot :=
  allocated.choose_spec.root_bound

theorem Protect.root_bound {program : Kernel.Program} {context : Context} {before after : World}
    {source destination : Address} {authority : Authority}
    (kept : Protect program context before source authority destination after) : destination.root < after.nextRoot := by
  obtain ⟨_,_,_,allocated,transferred⟩ := kept
  exact Nat.lt_of_lt_of_le allocated.root_bound transferred.suspensionExtension.counter

theorem Protects.root_support {program : Kernel.Program} {context : Context} {before after : World}
    {sources : List ResolvedPlace} {destinations : List Address}
    (kept : Protects program context before sources destinations after) :
    RootSupport.Below (destinations.map Address.root) after.nextRoot := by
  refine ProtectsFor.inductionOn
    (motive := fun before sources destinations after _ =>
      RootSupport.Below (destinations.map Address.root) after.nextRoot) kept
    (fun world => by simp)
    (fun ready head tail ih => by
      simp only [List.map_cons,RootSupport.below_cons]
      exact ⟨Nat.lt_of_lt_of_le head.root_bound tail.suspensionExtension.counter,ih⟩)

theorem Captures.root_support {program : Kernel.Program} {context : Context} {before after : World}
    {captures : List Capture} {addresses : List Address}
    (captured : Captures program context before captures addresses after) :
    RootSupport.Below (addresses.map Address.root) after.nextRoot := by
  induction captured with
  | nil => simp
  | owned _ _ allocated acquired rest ih =>
    simp only [List.map_cons,RootSupport.below_cons]
    exact ⟨Nat.lt_of_lt_of_le allocated.root_bound
      (Nat.le_trans acquired.suspensionExtension.counter rest.suspensionExtension.counter),ih⟩
  | borrowed _ _ _ allocated borrowed rest ih =>
    simp only [List.map_cons,RootSupport.below_cons]
    exact ⟨Nat.lt_of_lt_of_le allocated.root_bound
      (Nat.le_trans borrowed.suspensionExtension.counter rest.suspensionExtension.counter),ih⟩

/-- The loan-release fold only schedules retirements: `Task.rootSupport` of a
`releaseLoan` step is the continuation's, so the fold never widens the support
of the task it wraps. -/
theorem ReleaseLoans.root_support (identities : List Identity) (task : Task) :
    (ReleaseLoans identities task).rootSupport = task.rootSupport := by
  unfold ReleaseLoans
  induction identities.eraseDups with
  | nil => rfl
  | cons head tail ih => exact ih

theorem ReleaseCustodyLoans.root_support (world : World) (custody : ClaimCustody) (task : Task) :
    (ReleaseCustodyLoans world custody task).rootSupport = task.rootSupport :=
  ReleaseLoans.root_support _ _

theorem _root_.Glorious.Language.RelinquishesCustody.nextRoot_eq {before after : World} {custody : ClaimCustody}
    (relinquished : RelinquishesCustody before custody after) : after.nextRoot = before.nextRoot := by
  cases relinquished
  rfl

theorem _root_.Glorious.Language.RelinquishesCustody.counter {before after : World} {custody : ClaimCustody}
    (relinquished : RelinquishesCustody before custody after) : before.nextRoot ≤ after.nextRoot :=
  Nat.le_of_eq (_root_.Glorious.Language.RelinquishesCustody.nextRoot_eq relinquished).symm

/-- The receiver's inheritance of the source's implicit environment stays inside
any limit both contexts are already inside: the added rows come from the source's
environment and the retained rows from the receiver's own. -/
theorem Context.inheritResources_root_support {source receiver : Context} {limit : Identity}
    (sourceBound : RootSupport.Below source.rootSupport limit)
    (receiverBound : RootSupport.Below receiver.rootSupport limit) :
    RootSupport.Below (receiver.inheritResources source).rootSupport limit := by
  have sourceParts : RootSupport.Below (source.environment.map (fun binding => binding.address.root))
        limit ∧ RootSupport.Below
        (source.resourceContracts.flatMap
          (fun contract => contract.inputs.map (fun binding => binding.address.root))) limit := by
    rw [Context.rootSupport] at sourceBound
    exact RootSupport.below_append.mp sourceBound
  have receiverParts : RootSupport.Below (receiver.environment.map (fun binding => binding.address.root))
        limit ∧ RootSupport.Below
        (receiver.resourceContracts.flatMap
          (fun contract => contract.inputs.map (fun binding => binding.address.root))) limit := by
    rw [Context.rootSupport] at receiverBound
    exact RootSupport.below_append.mp receiverBound
  intro root member
  rw [Context.rootSupport,Context.inheritResources,Environment.inheritImplicit,Environment.install,
    List.map_append] at member
  rcases List.mem_append.mp member with first | contractPart
  · rcases List.mem_append.mp first with sourcePart | receiverPart
    · obtain ⟨binding,bindingMember,same⟩ := List.mem_map.mp sourcePart
      rw [← same]
      exact sourceParts.1 _ (List.mem_map.mpr ⟨binding,(List.mem_filter.mp bindingMember).1,rfl⟩)
    · obtain ⟨binding,bindingMember,same⟩ := List.mem_map.mp receiverPart
      rw [← same]
      exact receiverParts.1 _
        (List.mem_map.mpr ⟨binding,(List.mem_filter.mp bindingMember).1,rfl⟩)
  · obtain ⟨contract,contractMember,inner⟩ := List.mem_flatMap.mp contractPart
    obtain ⟨binding,bindingMember,same⟩ := List.mem_map.mp inner
    rw [← same]
    exact receiverParts.2 _ (List.mem_flatMap.mpr ⟨contract,contractMember,
      List.mem_map.mpr ⟨binding,bindingMember,rfl⟩⟩)

/-- Installing hand-off bindings into an environment stays inside any limit the
context and the bindings are already inside. -/
theorem Context.install_root_support {context : Context} {bindings : Environment} {limit : Identity}
    (contextBound : RootSupport.Below context.rootSupport limit)
    (bindingsBound : RootSupport.Below (bindings.map (fun binding => binding.address.root)) limit) :
    RootSupport.Below
      ({ context with environment :=
        context.environment.install (bindings.map StorageBinding.asObligation) }).rootSupport limit := by
  have contextParts : RootSupport.Below (context.environment.map (fun binding => binding.address.root))
        limit ∧ RootSupport.Below
        (context.resourceContracts.flatMap
          (fun contract => contract.inputs.map (fun binding => binding.address.root))) limit := by
    rw [Context.rootSupport] at contextBound
    exact RootSupport.below_append.mp contextBound
  intro root member
  rw [Context.rootSupport,Environment.install,List.map_append] at member
  rcases List.mem_append.mp member with first | contractPart
  · rcases List.mem_append.mp first with bindingPart | retainedPart
    · obtain ⟨mapped,mappedMember,sameRoot⟩ := List.mem_map.mp bindingPart
      obtain ⟨original,originalMember,sameBinding⟩ := List.mem_map.mp mappedMember
      rw [← sameBinding] at sameRoot
      rw [← sameRoot]
      exact bindingsBound _ (List.mem_map.mpr ⟨original,originalMember,rfl⟩)
    · obtain ⟨binding,bindingMember,same⟩ := List.mem_map.mp retainedPart
      rw [← same]
      exact contextParts.1 _
        (List.mem_map.mpr ⟨binding,(List.mem_filter.mp bindingMember).1,rfl⟩)
  · obtain ⟨contract,contractMember,inner⟩ := List.mem_flatMap.mp contractPart
    obtain ⟨binding,bindingMember,same⟩ := List.mem_map.mp inner
    rw [← same]
    exact contextParts.2 _ (List.mem_flatMap.mpr ⟨contract,contractMember,
      List.mem_map.mpr ⟨binding,bindingMember,rfl⟩⟩)

theorem ReturnsResources.context_root_support {program : Kernel.Program} {source receiver : Context}
    {before after : World} {result : Address} {context : Context}
    (returned : ReturnsResources program source receiver before result context after)
    (well : before.WellFormed)
    (sourceBound : RootSupport.Below source.rootSupport after.nextRoot)
    (receiverBound : RootSupport.Below receiver.rootSupport after.nextRoot) :
    RootSupport.Below context.rootSupport after.nextRoot := by
  cases returned with
  | localReturn same => exact Context.inheritResources_root_support sourceBound receiverBound
  | invocationReturn activationNe outputs outgoing bound relinquished =>
    exact Context.install_root_support receiverBound
      (RootSupport.below_map.mpr (fun binding member =>
        Nat.lt_of_lt_of_le (bound.bindings_root_bound well binding member) relinquished.counter))

theorem ReturnsResources.counter {program : Kernel.Program} {source receiver : Context}
    {before after : World} {result : Address} {context : Context}
    (returned : ReturnsResources program source receiver before result context after) :
    before.nextRoot ≤ after.nextRoot := by
  cases returned with
  | localReturn same => exact Nat.le_refl _
  | invocationReturn activationNe outputs outgoing bound relinquished =>
    exact Nat.le_trans (Kernel.BindsInputsAttemptFor.suspensionExtension bound).counter relinquished.counter

theorem ArgumentInputs.root_support {world : World} {context : Context} {index : Nat}
    {formals : List Local} {places : List Place} {inputs : List InvocationInput}
    (well : world.WellFormed) (bounded : RootSupport.Below context.rootSupport world.nextRoot)
    (prepared : ArgumentInputs world context index formals places inputs) :
    RootSupport.Below (inputs.flatMap InvocationInput.rootSupport) world.nextRoot := by
  induction prepared with
  | nil => simp
  | cons resolved _ _ ih =>
    simp only [List.flatMap_cons,InvocationInput.rootSupport,RootSupport.below_append,
      RootSupport.below_cons,RootSupport.below_nil,and_true]
    exact ⟨Context.resolves_root_bound well bounded resolved,ih⟩

theorem _root_.Glorious.Language.Kernel.PatternPlan.root_support {program : Language.Program} {world : World}
    {address : Address} {authority : Authority} {access : Access} {pattern : Pattern}
    {actions : PatternActions} (well : world.WellFormed)
    (planned : PatternPlan program world address authority access pattern actions)
    (bounded : address.root < world.nextRoot) :
    RootSupport.Below ((ScheduledPattern actions).flatMap PatternAction.rootSupport) world.nextRoot := by
  refine PatternPlan.rec
    (motive_1 := fun address _ _ _ actions _ => address.root < world.nextRoot →
      RootSupport.Below ((ScheduledPattern actions).flatMap PatternAction.rootSupport) world.nextRoot)
    (motive_2 := fun address _ _ _ _ actions _ => address.root < world.nextRoot →
      RootSupport.Below ((ScheduledPattern actions).flatMap PatternAction.rootSupport) world.nextRoot)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ planned bounded
  all_goals intros
  all_goals simp_all only [ScheduledPattern,List.nil_append,List.append_nil,List.flatMap_nil,List.flatMap_cons,
    List.flatMap_append,PatternAction.rootSupport,RootSupport.below_append,RootSupport.below_cons,
    RootSupport.below_nil,true_and,and_true,Address.child]
  case refine_8 =>
    split <;> simp_all only [List.flatMap_cons,List.flatMap_nil,PatternAction.rootSupport,
      RootSupport.below_append,RootSupport.below_cons,RootSupport.below_nil,and_true]
  case refine_9 =>
    rename_i found _ live _ _ _ _ ih bound
    have nested := ih (World.live_loan_root_bound well found live)
    split <;> simp_all only [List.flatMap_cons,List.flatMap_nil,PatternAction.rootSupport,
      RootSupport.below_append,RootSupport.below_cons,RootSupport.below_nil,and_true]

theorem PreparesEntryAttempt.wellFormed {program : Kernel.Program} {callee : Context} {function : Function}
    {before after : World} {source : EntrySource} {inputs : List InvocationInput} {outcome : PreparationOutcome}
    (prepared : PreparesEntryAttempt program callee function before source inputs after outcome)
    (well : before.WellFormed) : after.WellFormed := by
  cases prepared with
  | supplied => exact well
  | resident _ _ lends _ consumes =>
    exact ConsumesReceiver.wellFormed consumes (LendsResident.wellFormed lends well)
  | contextual _ _ _ _ receiverLends witnessLends _ consumes consumesAvailability =>
    exact ConsumesAvailability.wellFormed consumesAvailability
      (ConsumesReceiver.wellFormed consumes
        (LendsResident.wellFormed witnessLends (LendsResident.wellFormed receiverLends well)))
  | residentExhausted | contextualReceiverExhausted => exact well
  | contextualWitnessExhausted _ _ _ _ lends _ => exact lends.wellFormed well

theorem EnterWorld.context_root_support {program : Kernel.Program} {before : State} {caller context : Context}
    {function : Function} {source : EntrySource} {after : World}
    (well : before.world.WellFormed) (entered : EnterWorld program before caller function source context after) :
    RootSupport.Below context.rootSupport after.nextRoot := by
  obtain ⟨withRegion,prepared,inputs,environment,declaration,bound,functionAt,region,prepares,
    incoming,binds,finish,contextEq,unsafeOk⟩ := entered.prepared
  have boundAt := BindsInputsFor.bindings_root_bound binds
    (prepares.wellFormed (region.wellFormed well))
  have frontier : bound.nextRoot ≤ after.nextRoot := finish.suspensionExtension.counter
  rw [contextEq, Context.rootSupport, RootSupport.below_append]
  refine ⟨?_,?_⟩
  · rw [RootSupport.below_map]
    exact fun binding member => Nat.lt_of_lt_of_le (boundAt binding member) frontier
  · simp only [List.flatMap_cons,List.flatMap_nil,RootSupport.below_append,RootSupport.below_nil]
    refine ⟨?_,trivial⟩
    rw [RootSupport.below_map]
    exact fun binding member => Nat.lt_of_lt_of_le (boundAt binding member) frontier

theorem _root_.Glorious.Language.Kernel.ActivationRoots.root_support {world : World} {activation : Identity} {kept roots : List Identity}
    (well : world.WellFormed) (selected : ActivationRoots world activation kept roots) :
    RootSupport.Below roots world.nextRoot := by
  intro id member
  obtain ⟨root,found,_⟩ := (selected.2 id).mp member
  exact World.root_bound well found

theorem _root_.Glorious.Language.Kernel.ScopeRoots.root_support {world : World} {activation scope : Identity} {kept roots : List Identity}
    (well : world.WellFormed) (selected : ScopeRoots world activation scope kept roots) :
    RootSupport.Below roots world.nextRoot := by
  intro id member
  obtain ⟨root,found,_⟩ := (selected.2 id).mp member
  exact World.root_bound well found

@[simp] theorem CloseRegions.root_support (regions : List Identity) (next : Task) :
    (CloseRegions regions next).rootSupport = next.rootSupport := by
  unfold CloseRegions
  induction regions.eraseDups with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem RetireAddresses.root_support {addresses : List Address} {next : Task} {limit : Identity}
    (bounded : RootSupport.Below (addresses.map Address.root) limit)
    (continued : RootSupport.Below next.rootSupport limit) :
    RootSupport.Below (addresses.foldr (fun address nextTask => .retire address.root nextTask) next).rootSupport limit := by
  induction addresses with
  | nil => exact continued
  | cons _ _ ih =>
    simp only [List.map_cons,RootSupport.below_cons] at bounded
    exact RootSupport.below_cons.mpr ⟨bounded.1,ih bounded.2⟩

end Execution
end Glorious.Language
