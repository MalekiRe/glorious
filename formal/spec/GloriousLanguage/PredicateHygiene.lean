import GloriousLanguage.Terms

/-! Fresh predicate binders are derived from lexical parameter support, not
assumed globally fresh. These proofs justify the actual capture-avoiding
substitution operation, including caller values whose identities coincide
with the source predicate's bound names. -/
namespace Glorious.Language

theorem Term.parameterIds_children (term : Term) {id : Identity}
    (member : id ∈ term.children.flatMap Term.parameterIds) : id ∈ term.parameterIds := by
  cases term <;> simp only [Term.children,Term.parameterIds,List.flatMap_cons,List.flatMap_nil,
    List.flatMap_append,List.append_nil,List.append_assoc] at member ⊢
  all_goals first | exact member | exact False.elim (List.not_mem_nil member)

theorem Occurs.parameterIds {term : Term} {id : Identity} {kind : Kind}
    (occurs : Occurs (.parameter id kind) term) : id ∈ term.parameterIds := by
  induction occurs with
  | here => simp only [Term.parameterIds]; exact List.mem_cons_self
  | child member _ ih => exact Term.parameterIds_children _ (List.mem_flatMap.mpr ⟨_,member,ih⟩)

theorem Constraint.parameter_lt_freshSeed (constraint : Constraint) (substitution : Substitution)
    {id : Identity} (member : id ∈ constraint.parameterIds) : id < constraint.freshSeed substitution := by
  have bound := List.nat_le_sum_of_mem (List.mem_append_left substitution.parameterIds member)
  simp only [Constraint.freshSeed]
  exact Nat.lt_succ_of_le bound

theorem Substitution.parameter_lt_freshSeed (constraint : Constraint) (substitution : Substitution)
    {id : Identity} (member : id ∈ substitution.parameterIds) : id < constraint.freshSeed substitution := by
  have bound := List.nat_le_sum_of_mem (List.mem_append_right constraint.parameterIds member)
  simp only [Constraint.freshSeed]
  exact Nat.lt_succ_of_le bound

theorem Binder.freshRename_member {binders : List Binder} {binder : Binder} {seed : Identity}
    (member : binder ∈ binders) : Binder.freshRename binders seed binder.id = seed + binder.id := by
  simp only [Binder.freshRename,if_pos (List.mem_map.mpr ⟨binder,member,rfl⟩)]

theorem Binder.freshRename_not_mem {binders : List Binder} {seed id : Identity}
    (absent : id ∉ binders.map (·.id)) : Binder.freshRename binders seed id = id := by
  simp only [Binder.freshRename,if_neg absent]

theorem Binder.freshRename_injective_on {binders : List Binder} {seed : Identity} {left right : Binder}
    (first : left ∈ binders) (second : right ∈ binders)
    (same : Binder.freshRename binders seed left.id = Binder.freshRename binders seed right.id) : left.id = right.id := by
  rw [Binder.freshRename_member first,Binder.freshRename_member second] at same
  exact Nat.add_left_cancel same

/-- Every generated binder is fresh for every caller value, including values
that syntactically mention the old source binder. No normalization or missing
evidence is used to justify capture avoidance. -/
theorem Constraint.freshBinder_avoids_substitution {binders : List Binder} {requirements : List Constraint}
    {substitution : Substitution} {binder : Binder} (member : binder ∈ binders)
    {entry : Identity × Term} (present : entry ∈ substitution) {kind : Kind} :
    ¬ Occurs (.parameter (Binder.freshRename binders
      ((Constraint.quantified binders requirements).freshSeed substitution) binder.id) kind) entry.2 := by
  intro occurs
  have old := occurs.parameterIds
  have smaller := Substitution.parameter_lt_freshSeed (.quantified binders requirements) substitution
    (List.mem_flatMap.mpr ⟨entry,present,List.mem_cons_of_mem _ old⟩)
  rw [Binder.freshRename_member member] at smaller
  exact Nat.not_lt_of_ge (Nat.le_add_right _ _) smaller

theorem Constraint.freshBinder_avoids_source {binders : List Binder} {requirements : List Constraint}
    {substitution : Substitution} {binder : Binder} (member : binder ∈ binders) :
    Binder.freshRename binders ((Constraint.quantified binders requirements).freshSeed substitution) binder.id ∉
      (Constraint.quantified binders requirements).parameterIds := by
  intro present
  have smaller := Constraint.parameter_lt_freshSeed (.quantified binders requirements) substitution present
  rw [Binder.freshRename_member member] at smaller
  exact Nat.not_lt_of_ge (Nat.le_add_right _ _) smaller

theorem Term.renameParameters_kind (rename : Identity → Identity) (term : Term) :
    (term.renameParameters rename).kind = term.kind := by
  cases term <;> simp only [Term.renameParameters,Term.kind]

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

theorem Constraint.boundIds_mapTerms (f : Term → Term) (constraint : Constraint) :
    (constraint.mapTerms f).boundIds = constraint.boundIds := by
  cases constraint <;> simp only [Constraint.mapTerms,Constraint.boundIds]
  case quantified binders requirements =>
    simp only [List.map_map,List.flatMap_map,Function.comp_def]
    congr 1
    apply List.flatMap_congr_left
    intro requirement _
    exact requirement.boundIds_mapTerms f
termination_by constraint

theorem Term.parameterIds_renameRuntimeRegions (rename : Identity → Identity) (term : Term) :
    (term.renameRuntimeRegions rename).parameterIds = term.parameterIds := by
  cases term <;> simp only [Term.renameRuntimeRegions,Term.parameterIds,List.flatMap_map]
  all_goals try rfl
  all_goals repeat' first
    | exact Term.parameterIds_renameRuntimeRegions rename _
    | apply List.flatMap_congr_left
      intro child _
      exact child.parameterIds_renameRuntimeRegions rename
    | congr 1
termination_by term

theorem Term.renameParameters_renameRuntimeRegions (parameters regions : Identity → Identity) (term : Term) :
    (term.renameParameters parameters).renameRuntimeRegions regions =
      (term.renameRuntimeRegions regions).renameParameters parameters := by
  cases term <;> simp only [Term.renameParameters,Term.renameRuntimeRegions,List.map_map,Function.comp_def]
  all_goals try rfl
  all_goals congr 1
  all_goals first
    | exact Term.renameParameters_renameRuntimeRegions parameters regions _
    | apply List.map_congr_left
      intro child _
      exact child.renameParameters_renameRuntimeRegions parameters regions
termination_by term

theorem Term.renameRuntimeRegions_substitute (rename : Identity → Identity) (substitution : Substitution) (term : Term) :
    (term.substitute substitution).renameRuntimeRegions rename =
      (term.renameRuntimeRegions rename).substitute
        (substitution.map (fun entry => (entry.1,entry.2.renameRuntimeRegions rename))) := by
  cases term <;> simp only [Term.substitute,Term.renameRuntimeRegions]
  case parameter id kind =>
    rw [Table.get_map_values]
    cases substitution.get id <;> simp only [Option.getD,Option.map,Term.renameRuntimeRegions]
  all_goals try rfl
  all_goals try simp only [List.map_map,Function.comp_def]
  all_goals
    congr 1
    all_goals first
    | exact Term.renameRuntimeRegions_substitute rename substitution _
    | apply List.map_congr_left
      intro child _
      exact child.renameRuntimeRegions_substitute rename substitution
termination_by term

theorem Constraint.parameterIds_renameRuntimeRegions (rename : Identity → Identity) (constraint : Constraint) :
    (constraint.mapTerms (Term.renameRuntimeRegions rename)).parameterIds = constraint.parameterIds := by
  simp only [Constraint.parameterIds,Constraint.terms_mapTerms,Constraint.boundIds_mapTerms,List.flatMap_map,
    Term.parameterIds_renameRuntimeRegions]

theorem Constraint.freshSeed_renameRuntimeRegions (rename : Identity → Identity) (constraint : Constraint)
    (substitution : Substitution) :
    (constraint.mapTerms (Term.renameRuntimeRegions rename)).freshSeed
      (substitution.map (fun entry => (entry.1,entry.2.renameRuntimeRegions rename))) = constraint.freshSeed substitution := by
  simp only [Constraint.freshSeed,Constraint.parameterIds_renameRuntimeRegions,Substitution.parameterIds,
    List.flatMap_map,Term.parameterIds_renameRuntimeRegions]

theorem Constraint.renameParameters_renameRuntimeRegions (parameters regions : Identity → Identity)
    (constraint : Constraint) :
    (constraint.renameParameters parameters).mapTerms (Term.renameRuntimeRegions regions) =
      (constraint.mapTerms (Term.renameRuntimeRegions regions)).renameParameters parameters := by
  cases constraint <;> simp only [Constraint.renameParameters,Constraint.mapTerms,List.map_map,Function.comp_def,
    Term.renameParameters_renameRuntimeRegions]
  all_goals try rfl
  case quantified binders requirements =>
    congr 1
    · apply List.map_congr_left
      intro binder _
      simp only [Binder.renameParameters,Option.map_map,Function.comp_def,Term.renameParameters_renameRuntimeRegions]
    · apply List.map_congr_left
      intro requirement _
      exact requirement.renameParameters_renameRuntimeRegions parameters regions
termination_by constraint

theorem Constraint.renameRuntimeRegions_substitute (rename : Identity → Identity)
    (substitution : Substitution) (constraint : Constraint) :
    (constraint.substitute substitution).mapTerms (Term.renameRuntimeRegions rename) =
      (constraint.mapTerms (Term.renameRuntimeRegions rename)).substitute
        (substitution.map (fun entry => (entry.1,entry.2.renameRuntimeRegions rename))) := by
  cases constraint <;> simp only [Constraint.substitute,Constraint.mapTerms,Term.renameRuntimeRegions_substitute,
    List.map_map,Function.comp_def]
  all_goals try rfl
  case quantified binders requirements =>
    have fresh := Constraint.freshSeed_renameRuntimeRegions rename (.quantified binders requirements) substitution
    simp only [Constraint.mapTerms] at fresh
    have renamings (sourceBinders : List Binder) (seed : Identity) :
        Binder.freshRename (sourceBinders.map (fun binder => { binder with
          defaultValue := binder.defaultValue.map (Term.renameRuntimeRegions rename) })) seed =
          Binder.freshRename sourceBinders seed := by
      funext id
      simp only [Binder.freshRename,List.map_map,Function.comp_def]
    simp only [fresh,renamings,List.any_map,List.filter_map,← List.map_take,List.map_mapIdx,List.mapIdx_map,Function.comp_def,
      Option.map_map,Term.renameParameters_renameRuntimeRegions,Term.renameRuntimeRegions_substitute]
    congr 1
    simp only [List.attach_map,List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro requirement _
    rw [← Constraint.renameParameters_renameRuntimeRegions]
    exact Constraint.renameRuntimeRegions_substitute rename _ (requirement.val.renameParameters _)
termination_by constraint.quantifierCount
decreasing_by
  simp only [Constraint.quantifierCount_renameParameters,Constraint.quantifierCount]
  have smaller := List.nat_le_sum_of_mem (List.mem_map_of_mem (f := Constraint.quantifierCount) requirement.property)
  omega

end Glorious.Language
