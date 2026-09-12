import GloriousLanguage.RuntimeWorldEquivariance

/-! Complete effect coverage transports through the same actual world,
permission, operation-instance, and ordered pattern judgments. -/
namespace Glorious.Language

theorem RegionPermutation.operationArm_operation (permutation : RegionPermutation) (arm : Kernel.OperationArm) :
    (arm.mapTerms permutation.term).operation = arm.operation := by
  cases arm; simp only [Kernel.OperationArm.mapTerms,Kernel.OperationArm.transformTerms,Kernel.OperationArm.operation]

theorem RegionPermutation.operationArm_arguments (permutation : RegionPermutation) (arm : Kernel.OperationArm) :
    (arm.mapTerms permutation.term).arguments = arm.arguments.map permutation.term := by
  cases arm
  simp only [Kernel.OperationArm.mapTerms,Kernel.OperationArm.transformTerms,Kernel.OperationArm.arguments,List.map_append]

theorem RegionPermutation.operationArm_patterns (permutation : RegionPermutation) (arm : Kernel.OperationArm) :
    (arm.mapTerms permutation.term).patterns = arm.patterns.map (Kernel.Pattern.mapTerms permutation.term) := by
  cases arm; simp only [Kernel.OperationArm.mapTerms,Kernel.OperationArm.transformTerms,Kernel.OperationArm.patterns]

theorem RegionPermutation.handler_operations (permutation : RegionPermutation) (handler : Kernel.Handler) :
    (handler.mapTerms permutation.term).operations = handler.operations.map (Kernel.OperationArm.mapTerms permutation.term) := by
  cases handler; simp only [Kernel.Handler.mapTerms,Kernel.Handler.transformTerms,Kernel.Handler.operations,Kernel.OperationArm.mapTerms]

theorem Execution.ArmAccepts.permute {program : Kernel.Program} (valid : ProgramWellFormed program.declarations)
    {world : World} {context : Language.Context} {operation : DeclId} {arguments : List Term}
    {payload : List ResolvedPlace} {arm : Kernel.OperationArm}
    (accepted : Execution.ArmAccepts program world context operation arguments payload arm) (permutation : RegionPermutation) :
    Execution.ArmAccepts program (permutation.world world) (permutation.context context) operation
      (arguments.map permutation.term) payload (arm.mapTerms permutation.term) := by
  refine ⟨by rw [permutation.operationArm_operation]; exact accepted.1,?_,?_⟩
  · rw [permutation.operationArm_arguments]
    have related := accepted.2.1
    clear accepted
    generalize arm.arguments = types at related ⊢
    induction related with
    | nil => exact .nil
    | cons first _ ih => exact .cons (first.permute valid permutation) ih
  · rw [permutation.operationArm_patterns]
    have related := accepted.2.2
    clear accepted
    generalize arm.patterns = patterns at related ⊢
    induction related with
    | nil => exact .nil
    | cons first _ ih => exact .cons ⟨permutation.permitted_iff.mpr first.1,permutation.matches first.2⟩ ih

theorem Execution.ArmAccepts.world_twice {program : Kernel.Program} {world : World} {context : Language.Context}
    {operation : DeclId} {arguments : List Term} {payload : List ResolvedPlace} {arm : Kernel.OperationArm}
    (permutation : RegionPermutation)
    (accepted : Execution.ArmAccepts program (permutation.world (permutation.world world)) context operation arguments payload arm) :
    Execution.ArmAccepts program world context operation arguments payload arm := by
  refine ⟨accepted.1,accepted.2.1,?_⟩
  have related := accepted.2.2
  clear accepted
  generalize arm.patterns = patterns at related ⊢
  induction related with
  | nil => exact .nil
  | cons first _ ih =>
    exact .cons ⟨permutation.permitted_iff.mp (permutation.permitted_iff.mp first.1),first.2.transport
      (fun address => (permutation.world_read_twice world address).symm)
      (fun id => (permutation.world_loans_twice world id).symm)⟩ ih

theorem RegionPermutation.typedPayload (permutation : RegionPermutation) {world : World}
    {payload : List ResolvedPlace} {types : List Term}
    (typed : ListRel (fun source type => Permitted world source.authority .shared source.address ∧
      ∃ value, world.Stores source.address value ∧ value.type = type ∧ value.Initialized) payload types) :
    ListRel (fun source type => Permitted (permutation.world world) source.authority .shared source.address ∧
      ∃ value, (permutation.world world).Stores source.address value ∧ value.type = type ∧ value.Initialized)
      payload (types.map permutation.term) := by
  induction typed with
  | nil => exact .nil
  | cons first _ ih =>
    obtain ⟨allowed,value,stored,shape,initialized⟩ := first
    exact .cons ⟨permutation.permitted_iff.mpr allowed,permutation.value value,permutation.stores stored,
      by rw [permutation.value_type,shape],permutation.value_initialized initialized⟩ ih

theorem Typing.CompletelyHandles.permute {program : Kernel.Program} (valid : ProgramWellFormed program.declarations)
    (inventory : Kernel.BodyInventory program) {context : Language.Context} {handler : Kernel.Handler} {instanceTerm : Term}
    (covered : Typing.CompletelyHandles program context handler instanceTerm) (permutation : RegionPermutation) :
    Typing.CompletelyHandles program (permutation.context context) (handler.mapTerms permutation.term) (permutation.term instanceTerm) := by
  obtain ⟨id,arguments,family,substitution,rfl,found,instantiated,requirements,covered⟩ := covered
  have lexical := valid.lexical (List.mem_of_find?_eq_some (Program.effect_lookup found))
  refine ⟨id,arguments.map permutation.term,family,permutation.substitution substitution,
    by simp only [RegionPermutation.term,Term.renameRuntimeRegions],found,instantiated.permute permutation,?_,?_⟩
  · exact requirements.permute valid (fun requirement member term present => lexical term (by
      have nested : term ∈ family.requirements.flatMap Constraint.terms := List.mem_flatMap.mpr ⟨requirement,member,present⟩
      simp only [Definition.terms,List.mem_append,nested,true_or])) permutation
  · intro operationId member itemArguments operation signature selected world payload typed supplied
    have originalInstance := selected.permute valid permutation
    simp only [List.map_append,List.map_map,Function.comp_def,permutation.term_involutive,List.map_id'] at originalInstance
    have worldTyped : Typing.WorldTyped program (permutation.world world) := permutation.worldTyped valid inventory typed
    obtain ⟨arm,present,accepted⟩ := covered operationId member (itemArguments.map permutation.term) operation
      (permutation.signature signature) originalInstance (permutation.world world) payload worldTyped
      (permutation.typedPayload supplied)
    refine ⟨arm.mapTerms permutation.term,?_,?_⟩
    · rw [permutation.handler_operations]
      exact List.mem_map.mpr ⟨arm,present,rfl⟩
    · have transported := (accepted.permute valid permutation).world_twice permutation
      simpa only [List.map_append,List.map_map,Function.comp_def,permutation.term_involutive,List.map_id'] using transported

theorem Typing.HandledInstances.permute {program : Kernel.Program} (valid : ProgramWellFormed program.declarations)
    (inventory : Kernel.BodyInventory program) {context : Language.Context} {handler : Kernel.Handler} {instances : List Term}
    (covered : Typing.HandledInstances program context handler instances) (permutation : RegionPermutation) :
    Typing.HandledInstances program (permutation.context context) (handler.mapTerms permutation.term) (instances.map permutation.term) := by
  intro instanceTerm member
  obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
  exact (covered original present).permute valid inventory permutation

end Glorious.Language
