import GloriousLanguage.Foundation
import GloriousLanguage.ScopedInterpretation
import GloriousLanguage.TermScope
import GloriousLanguage.PredicateInterpretation

/-! The actual invocation instantiation read at the runtime image: the scope
decoding fixes a declaration's instantiated constraints, so the caller's
`ConstraintsHold` evidence is exactly the image reading of the entered context's
own assumptions. -/
namespace Glorious.Language

/-- A constraint whose own semantic terms the map fixes is fixed by the
constraint map; the quantified case recurses over the nested requirements. -/
theorem Constraint.mapTerms_eq_self {f : Term → Term} (constraint : Constraint)
    (terms : ∀ term ∈ constraint.terms, f term = term) : Constraint.mapTerms f constraint = constraint := by
  cases constraint with
  | equal a b =>
      simp only [Constraint.mapTerms]
      rw [terms a (by simp only [Constraint.terms]; simp),
        terms b (by simp only [Constraint.terms]; simp)]
  | outlives a b =>
      simp only [Constraint.mapTerms]
      rw [terms a (by simp only [Constraint.terms]; simp),
        terms b (by simp only [Constraint.terms]; simp)]
  | typeOutlives a b =>
      simp only [Constraint.mapTerms]
      rw [terms a (by simp only [Constraint.terms]; simp),
        terms b (by simp only [Constraint.terms]; simp)]
  | rowIncludes a b =>
      simp only [Constraint.mapTerms]
      rw [terms a (by simp only [Constraint.terms]; simp),
        terms b (by simp only [Constraint.terms]; simp)]
  | implements trait arguments negative =>
      simp only [Constraint.mapTerms]
      congr 1
      exact List.map_eq_self_of _ _ (fun term member =>
        terms term (by simpa only [Constraint.terms] using member))
  | use type quantity =>
      simp only [Constraint.mapTerms]
      rw [terms type (by simp only [Constraint.terms]; simp)]
  | callable receiver arguments output effects unsafeAllowed =>
      simp only [Constraint.mapTerms]
      rw [terms receiver (by simp only [Constraint.terms]; simp),
        terms output (by simp only [Constraint.terms]; simp),
        terms effects (by simp only [Constraint.terms]; simp)]
      congr 1
      exact List.map_eq_self_of _ _ (fun term member =>
        terms term (by simp only [Constraint.terms,List.mem_cons]; exact Or.inr (Or.inr (Or.inr member))))
  | runsIn receiver access arguments after unsafeAllowed =>
      simp only [Constraint.mapTerms]
      rw [terms receiver (by simp only [Constraint.terms]; simp),
        terms access (by simp only [Constraint.terms]; simp),
        terms after (by simp only [Constraint.terms]; simp)]
      congr 1
      exact List.map_eq_self_of _ _ (fun term member =>
        terms term (by simp only [Constraint.terms,List.mem_cons]; exact Or.inr (Or.inr (Or.inr member))))
  | quantified binders requirements =>
      simp only [Constraint.mapTerms]
      congr 1
      · apply List.map_eq_self_of
        intro binder member
        cases binder with
        | mk id name kind defaultValue =>
          cases defaultValue with
          | none => rfl
          | some term =>
            simp only [Option.map]
            rw [terms term (by
              simp only [Constraint.terms,List.mem_append]
              exact Or.inl (List.mem_flatMap.mpr ⟨_, member, by simp⟩))]
      · apply List.map_eq_self_of
        intro requirement member
        exact Constraint.mapTerms_eq_self requirement (fun term present => terms term (by
          simp only [Constraint.terms,List.mem_append]
          exact Or.inr (List.mem_flatMap.mpr ⟨_, member, present⟩)))


/-- A declaration template that the decoding fixes together with fixed
substitution values yields a fixed substituted term: the actual arguments of an
invocation are scope-closed, so the instantiated constraint terms are fixed by
the decoding exactly as their templates are. -/
theorem ScopeInstantiation.substituted_fixed {scope : ScopeInstantiation} {term : Term}
    {substitution : Substitution} (termFixed : scope.term term = term)
    (valuesFixed : ∀ entry ∈ substitution, scope.term entry.2 = entry.2) :
    scope.term (term.substitute substitution) = term.substitute substitution := by
  rw [ScopeInstantiation.map_substituted_values scope term substitution
    (ScopeInstantiation.atomsFixed scope term),termFixed]
  have same : List.map (fun entry => (entry.1, scope.term entry.2)) substitution = substitution :=
    List.map_eq_self_of (f := fun entry : Identity × Term => (entry.1, scope.term entry.2)) substitution
      (fun entry member => Prod.ext rfl (valuesFixed entry member))
  rw [same]

/-- The decoding commutes with parameter renaming: it replaces exactly the two
executable lexical atoms while the renaming replaces exactly the parameters, so
the two actions are independent on every term. -/
theorem ScopeInstantiation.renameParameters (scope : ScopeInstantiation) (parameters : Identity → Identity)
    (term : Term) :
    scope.term (term.renameParameters parameters) = (scope.term term).renameParameters parameters := by
  cases term
  case parameter id kind => simp only [Term.renameParameters,ScopeInstantiation.term]
  case rigid id kind level =>
    rw [ScopeInstantiation.rigid_fixed scope]; simp only [Term.renameParameters,ScopeInstantiation.term]
  case «variable» id kind level =>
    rw [ScopeInstantiation.variable_fixed scope]; simp only [Term.renameParameters,ScopeInstantiation.term]
  case runtimeRegion id =>
    rw [ScopeInstantiation.runtimeRegion_fixed scope]; simp only [Term.renameParameters,ScopeInstantiation.term]
  case scopedRegion id =>
    cases h : scope.regions.get id
    · simp only [h,Option.map,Option.getD,ScopeInstantiation.term,Term.renameParameters]
    · simp only [h,Option.map,Option.getD,ScopeInstantiation.term,Term.renameParameters]
  case scopedBrand id =>
    cases h : scope.brands.get id
    · simp only [h,Option.map,Option.getD,ScopeInstantiation.term,Term.renameParameters]
    · simp only [h,Option.map,Option.getD,ScopeInstantiation.term,Term.renameParameters]
  all_goals simp only [Term.renameParameters,ScopeInstantiation.term,List.map_map,Function.comp_def]
  all_goals try rfl
  all_goals congr 1
  all_goals
    first
    | (apply List.map_congr_left
       intro child member
       exact ScopeInstantiation.renameParameters scope parameters child)
    | (exact ScopeInstantiation.renameParameters scope parameters _)
termination_by term
/-- The decoding commutes with the substitution filter: filtering is decided by
the table keys, which the decoding leaves in place. -/
theorem ScopeInstantiation.substitution_filter (scope : ScopeInstantiation) (substitution : Substitution)
    (keep : Identity → Bool) :
    (substitution.filter (fun entry => keep entry.1)).map (fun entry => (entry.1, scope.term entry.2)) =
      (substitution.map (fun entry => (entry.1, scope.term entry.2))).filter
        (fun entry => keep entry.1) := by
  simp only [List.filter_map,Function.comp_def]

/-- The decoding commutes with parameter renaming at the constraint level. -/
theorem Constraint.mapTerms_renameParameters (scope : ScopeInstantiation) (parameters : Identity → Identity)
    (constraint : Constraint) :
    (constraint.renameParameters parameters).mapTerms scope.term =
      (constraint.mapTerms scope.term).renameParameters parameters := by
  cases constraint <;> simp only [Constraint.renameParameters,Constraint.mapTerms,List.map_map,
    Function.comp_def,ScopeInstantiation.renameParameters]
  all_goals try rfl
  case quantified binders requirements =>
    congr 1
    · apply List.map_congr_left
      intro binder _
      simp only [Binder.renameParameters,Option.map_map,Function.comp_def,ScopeInstantiation.renameParameters]
    · apply List.map_congr_left
      intro requirement _
      exact Constraint.mapTerms_renameParameters scope parameters requirement
termination_by constraint
/-- The decoding preserves a term's parameter support: it replaces exactly the
two executable lexical atoms and leaves every parameter in place. -/
theorem ScopeInstantiation.parameterIds (scope : ScopeInstantiation) (term : Term) :
    (scope.term term).parameterIds = term.parameterIds := by
  cases term
  case parameter id kind => simp only [ScopeInstantiation.term,Term.parameterIds]
  case rigid id kind level =>
    simp only [ScopeInstantiation.rigid_fixed scope,Term.parameterIds]
  case «variable» id kind level =>
    simp only [ScopeInstantiation.variable_fixed scope,Term.parameterIds]
  case runtimeRegion id =>
    simp only [ScopeInstantiation.runtimeRegion_fixed scope,Term.parameterIds]
  case runtimeBrand id => simp only [ScopeInstantiation.term,Term.parameterIds]
  case scopedRegion id =>
    cases h : scope.regions.get id
    · simp only [h,Option.map,Option.getD,ScopeInstantiation.term,Term.parameterIds]
    · simp only [h,Option.map,Option.getD,ScopeInstantiation.term,Term.parameterIds]
  case scopedBrand id =>
    cases h : scope.brands.get id
    · simp only [h,Option.map,Option.getD,ScopeInstantiation.term,Term.parameterIds]
    · simp only [h,Option.map,Option.getD,ScopeInstantiation.term,Term.parameterIds]
  all_goals simp only [ScopeInstantiation.term,Term.parameterIds,List.flatMap_map]
  all_goals try rfl
  all_goals repeat' first
    | exact ScopeInstantiation.parameterIds scope _
    | (apply List.flatMap_congr_left
       intro child _
       exact ScopeInstantiation.parameterIds scope child)
    | congr 1
termination_by term
/-- The decoding preserves a substitution table's parameter support. -/
theorem ScopeInstantiation.substitution_parameterIds (scope : ScopeInstantiation)
    (substitution : Substitution) :
    Substitution.parameterIds (substitution.map (fun entry => (entry.1, scope.term entry.2))) =
      Substitution.parameterIds substitution := by
  simp only [Substitution.parameterIds,List.flatMap_map,ScopeInstantiation.parameterIds]

/-- The decoding preserves a constraint's parameter support. -/
theorem Constraint.mapTerms_parameterIds (scope : ScopeInstantiation) (constraint : Constraint) :
    (constraint.mapTerms scope.term).parameterIds = constraint.parameterIds := by
  simp only [Constraint.parameterIds,Constraint.terms_mapTerms,Constraint.boundIds_mapTerms,
    List.flatMap_map,ScopeInstantiation.parameterIds]

/-- The fresh seed is read at the image: the decoding preserves both the
constraint's and the substitution table's parameter support. -/
theorem Constraint.freshSeed_mapTerms (scope : ScopeInstantiation) (constraint : Constraint)
    (substitution : Substitution) :
    (constraint.mapTerms scope.term).freshSeed
        (substitution.map (fun entry => (entry.1, scope.term entry.2))) =
      constraint.freshSeed substitution := by
  simp only [Constraint.freshSeed,Constraint.mapTerms_parameterIds,
    ScopeInstantiation.substitution_parameterIds]

/-- The decoding commutes with constraint substitution: the substituted template
terms decode exactly as the templates decoded with the decoded table. -/
theorem Constraint.mapTerms_substitute (scope : ScopeInstantiation) (substitution : Substitution)
    (constraint : Constraint) :
    (constraint.substitute substitution).mapTerms scope.term =
      (constraint.mapTerms scope.term).substitute
        (substitution.map (fun entry => (entry.1, scope.term entry.2))) := by
  cases constraint <;> simp only [Constraint.substitute,Constraint.mapTerms]
  all_goals try simp only [ScopeInstantiation.map_substituted_values,ScopeInstantiation.atomsFixed]
  all_goals try congr 1
  all_goals try
    (simp only [List.map_map,Function.comp_def]
     apply List.map_congr_left
     intro child member
     simp only [ScopeInstantiation.map_substituted_values,ScopeInstantiation.atomsFixed])
  all_goals try rfl
  case quantified binders requirements =>
    have termCommute (table : Substitution) (term : Term) :
        scope.term (term.substitute table) =
          (scope.term term).substitute
            (table.map (fun entry => (entry.1, scope.term entry.2))) :=
      ScopeInstantiation.map_substituted_values scope term table
        (ScopeInstantiation.atomsFixed scope term)
    have renamings (sourceBinders : List Binder) (seed : Identity) :
        Binder.freshRename (sourceBinders.map (fun binder =>
            { binder with defaultValue := binder.defaultValue.map scope.term })) seed =
          Binder.freshRename sourceBinders seed := by
      funext id
      simp only [Binder.freshRename,List.map_map,Function.comp_def]
    have filters (sourceBinders : List Binder) :
        List.filter (fun entry =>
            !(sourceBinders.map (fun binder =>
                { binder with defaultValue := binder.defaultValue.map scope.term })).any
              (fun binder => binder.id == entry.1))
            (substitution.map (fun entry => (entry.1, scope.term entry.2))) =
          (substitution.filter (fun entry =>
            !(sourceBinders.any (fun binder => binder.id == entry.1)))).map
            (fun entry => (entry.1, scope.term entry.2)) := by
      simp only [List.any_map,Function.comp_def]
      exact (ScopeInstantiation.substitution_filter scope substitution
        (fun id => !(sourceBinders.any (fun binder => binder.id == id)))).symm
    have freshSeed := Constraint.freshSeed_mapTerms scope
      (Constraint.quantified binders requirements) substitution
    have freshSeedUnfolded :
        (Constraint.quantified
            (binders.map (fun binder =>
              { binder with defaultValue := binder.defaultValue.map scope.term }))
            (requirements.map (Constraint.mapTerms scope.term))).freshSeed
          (substitution.map (fun entry => (entry.1, scope.term entry.2))) =
        (Constraint.quantified binders requirements).freshSeed substitution := by
      simpa only [Constraint.mapTerms] using freshSeed
    all_goals
      simp only [freshSeedUnfolded,renamings,termCommute,List.any_map,
        List.filter_map,← List.map_take,List.map_mapIdx,List.mapIdx_map,Function.comp_def,
        Option.map_map,ScopeInstantiation.renameParameters]
    all_goals
      try
        congr 1
        funext index value
        congr 1
        funext entry
        simp only [termCommute,filters,List.any_map,
          List.filter_map,← List.map_take,List.map_mapIdx,List.mapIdx_map,List.map_map,
          Function.comp_def,Option.map_map,ScopeInstantiation.renameParameters,
          ScopeInstantiation.atomsFixed]
  case quantified.e_requirements binders requirements =>
    have termCommute (table : Substitution) (term : Term) :
        scope.term (term.substitute table) =
          (scope.term term).substitute
            (table.map (fun entry => (entry.1, scope.term entry.2))) :=
      ScopeInstantiation.map_substituted_values scope term table
        (ScopeInstantiation.atomsFixed scope term)
    have renamings (sourceBinders : List Binder) (seed : Identity) :
        Binder.freshRename (sourceBinders.map (fun binder =>
            { binder with defaultValue := binder.defaultValue.map scope.term })) seed =
          Binder.freshRename sourceBinders seed := by
      funext id
      simp only [Binder.freshRename,List.map_map,Function.comp_def]
    have filters (sourceBinders : List Binder) :
        List.filter (fun entry =>
            !(sourceBinders.map (fun binder =>
                { binder with defaultValue := binder.defaultValue.map scope.term })).any
              (fun binder => binder.id == entry.1))
            (substitution.map (fun entry => (entry.1, scope.term entry.2))) =
          (substitution.filter (fun entry =>
            !(sourceBinders.any (fun binder => binder.id == entry.1)))).map
            (fun entry => (entry.1, scope.term entry.2)) := by
      simp only [List.any_map,Function.comp_def]
      exact (ScopeInstantiation.substitution_filter scope substitution
        (fun id => !(sourceBinders.any (fun binder => binder.id == id)))).symm
    have freshSeed := Constraint.freshSeed_mapTerms scope
      (Constraint.quantified binders requirements) substitution
    have freshSeedUnfolded :
        (Constraint.quantified
            (binders.map (fun binder =>
              { binder with defaultValue := binder.defaultValue.map scope.term }))
            (requirements.map (Constraint.mapTerms scope.term))).freshSeed
          (substitution.map (fun entry => (entry.1, scope.term entry.2))) =
        (Constraint.quantified binders requirements).freshSeed substitution := by
      simpa only [Constraint.mapTerms] using freshSeed
    simp only [List.attach_map,List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro requirement member
    rw [Constraint.mapTerms_substitute scope _ (Constraint.renameParameters _ requirement.val)]
    rw [Constraint.mapTerms_renameParameters scope _ requirement.val]
    simp only [freshSeedUnfolded,renamings,List.any_map,List.filter_map,Function.comp_def]
termination_by constraint.quantifierCount
decreasing_by
  simp only [Constraint.quantifierCount_renameParameters,Constraint.quantifierCount]
  have smaller := List.nat_le_sum_of_mem
    (List.mem_map_of_mem (f := Constraint.quantifierCount) requirement.property)
  omega
end Glorious.Language
