import GloriousLanguage.RuntimeEquivariance

/-! Runtime-name transport of the actual invocation signature and scope-closing
operations. Generic defaults and quantified constraints use the same semantic
term action as parameters, results and environment access. -/
namespace Glorious.Language

theorem List.flatMap_congr_left {α β : Type} {values : List α} {first second : α → List β}
    (agree : ∀ value ∈ values, first value = second value) : values.flatMap first = values.flatMap second := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp only [List.flatMap_cons,agree value List.mem_cons_self,
      ih (fun value member => agree value (List.mem_cons_of_mem _ member))]

theorem Constraint.terms_mapTerms (f : Term → Term) (constraint : Constraint) :
    (constraint.mapTerms f).terms = constraint.terms.map f := by
  cases constraint <;>
    simp only [Constraint.mapTerms,Constraint.terms,List.map_cons,List.map_nil,List.map_append,
      List.flatMap_map,List.map_flatMap,Option.toList_map]
  case quantified binders requirements =>
    congr 1
    apply List.flatMap_congr_left
    intro requirement _
    exact requirement.terms_mapTerms f
termination_by constraint

theorem Signature.terms_mapTerms (f : Term → Term) (signature : Signature) :
    (signature.mapTerms f).terms = signature.terms.map f := by
  simp only [Signature.mapTerms,Signature.terms,List.map_cons,List.map_append,
    List.flatMap_map,List.map_flatMap,Constraint.terms_mapTerms,Option.toList_map]

theorem Constraint.mapTerms_id (constraint : Constraint) : constraint.mapTerms id = constraint := by
  cases constraint <;> simp only [Constraint.mapTerms,id_eq,List.map_id_fun,Option.map_id_fun]
  all_goals try rfl
  case quantified binders requirements =>
    congr 1
    · exact List.map_eq_self_of _ _ (fun binder _ => by cases binder; rfl)
    · exact List.map_eq_self_of _ _ (fun requirement _ => requirement.mapTerms_id)
termination_by constraint

theorem Constraint.mapTerms_comp (first second : Term → Term) (constraint : Constraint) :
    (constraint.mapTerms first).mapTerms second = constraint.mapTerms (second ∘ first) := by
  cases constraint <;> simp only [Constraint.mapTerms,List.map_map,Function.comp_def,Option.map_map]
  all_goals try rfl
  case quantified binders requirements =>
    congr 1
    apply List.map_congr_left
    intro requirement _
    exact requirement.mapTerms_comp first second
termination_by constraint

theorem Constraint.mapTerms_congr (first second : Term → Term) (constraint : Constraint)
    (agree : ∀ term ∈ constraint.terms, first term = second term) :
    constraint.mapTerms first = constraint.mapTerms second := by
  cases constraint <;> simp only [Constraint.mapTerms]
  all_goals try {
    congr 1
    all_goals first
    | apply agree; simp [Constraint.terms]
    | apply List.map_congr_left
      intro term member
      apply agree
      simp [Constraint.terms,member] }
  case quantified binders requirements =>
    congr 1
    · apply List.map_congr_left
      intro binder member
      congr 1
      apply Option.map_congr
      intro term selected
      apply agree
      simp only [Constraint.terms,List.mem_append,List.mem_flatMap]
      exact Or.inl ⟨binder,member,by simpa only [Option.mem_toList] using selected⟩
    · apply List.map_congr_left
      intro requirement member
      exact requirement.mapTerms_congr first second (fun term present => agree term (by
        simp only [Constraint.terms,List.mem_append,List.mem_flatMap]
        exact Or.inr ⟨requirement,member,present⟩))
termination_by constraint

theorem Signature.mapTerms_comp (first second : Term → Term) (signature : Signature) :
    (signature.mapTerms first).mapTerms second = signature.mapTerms (second ∘ first) := by
  simp only [Signature.mapTerms,List.map_map,Function.comp_def,Option.map_map,Constraint.mapTerms_comp]

theorem Signature.mapTerms_congr (first second : Term → Term) (signature : Signature)
    (agree : ∀ term ∈ signature.terms, first term = second term) :
    signature.mapTerms first = signature.mapTerms second := by
  have members : ∀ term, term = signature.result ∨ term = signature.effects ∨ term ∈ signature.parameters ∨
      term ∈ signature.constraints.flatMap Constraint.terms ∨
      term ∈ signature.generics.flatMap (fun binder => binder.defaultValue.toList) → first term = second term := by
    intro term present
    apply agree
    simpa only [Signature.terms,List.mem_append,List.mem_cons,or_assoc] using present
  simp only [Signature.mapTerms]
  congr 1
  · apply List.map_congr_left
    intro binder member
    congr 1
    apply Option.map_congr
    intro term selected
    exact members term (Or.inr (Or.inr (Or.inr (Or.inr (List.mem_flatMap.mpr
      ⟨binder,member,by simpa only [Option.mem_toList] using selected⟩)))))
  · exact List.map_congr_left (fun term member => members term (Or.inr (Or.inr (Or.inl member))))
  · exact members _ (Or.inl rfl)
  · exact members _ (Or.inr (Or.inl rfl))
  · apply List.map_congr_left
    intro constraint member
    exact constraint.mapTerms_congr first second (fun term present =>
      members term (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_flatMap.mpr ⟨constraint,member,present⟩))))))

def RegionPermutation.signature (permutation : RegionPermutation) (signature : Signature) : Signature :=
  signature.mapTerms permutation.term

theorem Signature.mapTerms_instantiate (f : Term → Term) (mapped : Substitution → Substitution)
    (terms : ∀ substitution term, f (term.substitute substitution) = (f term).substitute (mapped substitution))
    (filtered : ∀ substitution (keep : Identity → Bool), mapped (substitution.filter (fun entry => keep entry.1)) =
      (mapped substitution).filter (fun entry => keep entry.1))
    (signature : Signature) (substitution : Substitution) :
    (signature.instantiate substitution).mapTerms f = (signature.mapTerms f).instantiate (mapped substitution) := by
  simp only [Signature.mapTerms,Signature.instantiate,List.map_nil,List.map_map,Function.comp_def,terms]
  congr 1
  apply List.map_congr_left
  intro constraint _
  exact constraint.mapTerms_substitute f mapped terms filtered substitution

theorem RegionPermutation.signature_instantiate (permutation : RegionPermutation)
    (signature : Signature) (substitution : Substitution) :
    permutation.signature (signature.instantiate substitution) =
      (permutation.signature signature).instantiate (permutation.substitution substitution) :=
  signature.mapTerms_instantiate permutation.term permutation.substitution permutation.term_substitute permutation.substitution_filter substitution

theorem RegionPermutation.lexical_signature (permutation : RegionPermutation) {signature : Signature}
    (lexical : ∀ term ∈ signature.terms, term.Lexical) : permutation.signature signature = signature := by
  have same := signature.mapTerms_congr permutation.term id (fun term member => permutation.lexical_term (lexical term member))
  refine same.trans ?_
  simp only [Signature.mapTerms,List.map_id_fun,id_eq,Option.map_id_fun]
  congr 1
  · exact List.map_eq_self_of _ _ (fun binder _ => by cases binder; rfl)
  · exact List.map_eq_self_of _ _ (fun constraint _ => constraint.mapTerms_id)

theorem Typing.CallSignature.permute {program : Program} (valid : ProgramWellFormed program)
    {context : Language.Context} {id : DeclId} {arguments : List Term} {signature : Signature}
    (selected : Typing.CallSignature program context id arguments signature) (permutation : RegionPermutation) :
    Typing.CallSignature program (permutation.context context) id (arguments.map permutation.term)
      (permutation.signature signature) := by
  obtain ⟨kinded,selected⟩ := selected
  refine ⟨?_,?_⟩
  · intro argument member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    simpa only [permutation.term_kind] using (kinded original present).permute permutation
  rcases selected with selected | selected
  all_goals rcases selected with ⟨declaration,substitution,found,instantiated,requirements,rfl⟩
  · have lexical := valid.lexical (List.mem_of_find?_eq_some (Program.function_lookup found))
    have signatureLexical : ∀ term ∈ declaration.signature.terms, term.Lexical :=
      fun term member => lexical term (by simp only [Definition.terms,List.mem_append]; exact Or.inl (Or.inl member))
    refine Or.inl ⟨declaration,permutation.substitution substitution,found,instantiated.permute permutation,
      requirements.permute valid (fun constraint member term present => signatureLexical term (by
        simp only [Signature.terms,List.mem_append,List.mem_cons]
        exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨constraint,member,present⟩)))) permutation,?_⟩
    rw [permutation.signature_instantiate,permutation.lexical_signature signatureLexical]
  · have lexical := valid.lexical (List.mem_of_find?_eq_some (Program.operation_lookup found))
    have signatureLexical : ∀ term ∈ declaration.signature.terms, term.Lexical :=
      fun term member => lexical term (by simpa only [Definition.terms] using member)
    refine Or.inr ⟨declaration,permutation.substitution substitution,found,instantiated.permute permutation,
      requirements.permute valid (fun constraint member term present => signatureLexical term (by
        simp only [Signature.terms,List.mem_append,List.mem_cons]
        exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨constraint,member,present⟩)))) permutation,?_⟩
    rw [permutation.signature_instantiate,permutation.lexical_signature signatureLexical]

theorem Execution.OperationInstance.permute {program : Kernel.Program} (valid : ProgramWellFormed program.declarations)
    {id : DeclId} {arguments : List Term} {operation : OperationDefinition} {signature : Signature}
    (selected : Execution.OperationInstance program id arguments operation signature) (permutation : RegionPermutation) :
    Execution.OperationInstance program id (arguments.map permutation.term) operation (permutation.signature signature) := by
  obtain ⟨substitution,found,instantiated,requirements,rfl⟩ := selected
  have lexical := valid.lexical (List.mem_of_find?_eq_some (Program.operation_lookup found))
  refine ⟨permutation.substitution substitution,found,instantiated.permute permutation,?_,?_⟩
  · simpa only [RegionPermutation.context,List.map_nil] using requirements.permute valid (fun constraint member term present => lexical term (by
      have nested : term ∈ operation.signature.constraints.flatMap Constraint.terms := List.mem_flatMap.mpr ⟨constraint,member,present⟩
      simp only [Definition.terms,Signature.terms,List.mem_append,List.mem_cons,nested,or_true,true_or])) permutation
  · rw [permutation.signature_instantiate,permutation.lexical_signature (fun term member => lexical term (by
      simpa only [Definition.terms] using member))]

theorem ScopeInstantiation.term_renameRuntimeRegions (scope : ScopeInstantiation) (rename : Identity → Identity)
    (term : Term) :
    (scope.term term).renameRuntimeRegions rename =
      ({ scope with regions := scope.regions.map (fun (lexical,runtime) => (lexical,rename runtime)) } : ScopeInstantiation).term
        (term.renameRuntimeRegions rename) := by
  cases term <;> simp only [ScopeInstantiation.term,Term.renameRuntimeRegions]
  case scopedRegion id =>
    rw [Table.get_map_values]
    cases scope.regions.get id <;> simp only [Option.map,Option.getD,Term.renameRuntimeRegions]
  case scopedBrand id =>
    cases scope.brands.get id <;> simp only [Option.map,Option.getD,Term.renameRuntimeRegions]
  all_goals try rfl
  all_goals try simp only [List.map_map,Function.comp_def]
  all_goals
    congr 1
    all_goals first
    | exact scope.term_renameRuntimeRegions rename _
    | apply List.map_congr_left
      intro child _
      exact scope.term_renameRuntimeRegions rename child
termination_by term

namespace Execution

open Kernel

theorem Relocation.context_term (map : Relocation) (context : Context) (term : Term) :
    map.term (context.term term) = (map.context context).term (map.term term) :=
  context.instantiation.term_renameRuntimeRegions map.region term

theorem Relocation.context_signature (map : Relocation) (context : Context) (signature : Signature) :
    map.signature (signature.close context.instantiation) =
      (map.signature signature).close (map.context context).instantiation := by
  simp only [Relocation.signature,Signature.close,Signature.mapTerms_comp]
  exact signature.mapTerms_congr _ _ (fun term _ => map.context_term context term)

theorem Relocation.context_invocation (map : Relocation) (context : Context) (call : Invocation) :
    map.invocation (context.invocation call) = (map.context context).invocation (map.invocation call) := by
  simp only [Relocation.invocation,Context.invocation,Invocation.mapTerms,Invocation.transformTerms,
    Signature.mapTerms_comp,Option.map_map,Function.comp_def]
  congr 1
  · apply Option.map_congr
    intro access _
    simp only [EnvironmentAccess.mapTerms,map.context_term]
  · exact call.signature.mapTerms_congr _ _ (fun term _ => map.context_term context term)

/-- Closing a relocated tail request produces exactly the relocated call,
including its selected signature and availability-environment contract. -/
theorem LocalStep.relocated_tailRequest {program : Kernel.Program} {before : State}
    (map : Relocation) (context : Context) (call : Invocation)
    (running : before.task = .run (map.context context) (map.code (.tail call))) :
    LocalStep program before none
      { before with task := .apply (map.context context) (map.invocation (context.invocation call)) true } := by
  rw [map.context_invocation]
  exact .tailRequest (by simpa only [Relocation.code,Code.mapTerms,Code.transformTerms,
    Relocation.invocation,Invocation.mapTerms] using running)

end Execution

end Glorious.Language
