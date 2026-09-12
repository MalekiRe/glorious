import GloriousLanguage.FreshAtomTransport
import GloriousLanguage.FreshInstantiation

/-! Concrete generative inspection specializes into the caller's actual
generic substitution judgment. Kinding transport and universal argument
pullback are derived from context fields; source predicate assumptions are
discharged through their authoritative hygienic instantiations. -/
namespace Glorious.Language

theorem Entails.interpret_fresh_universe {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {constraint : Constraint} (held : Entails program source constraint)
    (specialization : FreshAtomSpecialization) (admitted : specialization.Admitted program target)
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (binders : source.binders = target.binders) (scope : source.scope = target.scope)
    (higher : target.universeLevel ≤ source.universeLevel)
    (assumptions : ∀ requirement ∈ source.assumptions,
      FreshAtomInterpretation.Holds specialization program target requirement) :
    FreshAtomInterpretation.Holds specialization program target constraint := by
  apply held.interpret_fresh valid specialization admitted targetKinded _ _ assumptions
  · intro term kind typed
    have sourceTyped : Kinding program { target with universeLevel := source.universeLevel } term kind :=
      typed.context_same_domain binders rfl scope
    exact sourceTyped.specializeFresh specialization admitted
  · intro term kind typed
    obtain ⟨sourceTyped,fixed⟩ := specialization.target_preimage admitted higher typed
    exact ⟨sourceTyped.context_same_domain binders.symm rfl scope.symm,fixed⟩

theorem FreshInstantiation.entails_iff {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {constraint : Constraint}
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (kinded : ConstraintKinded program source constraint) {arguments : List Term} {caller : Substitution}
    (opened : Instantiates source.binders arguments caller)
    (argumentsKinded : ∀ argument ∈ arguments, Kinding program target argument argument.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands)
    {level : Nat} (fresh : target.universeLevel < level) :
    FreshAtomInterpretation.Holds (FreshAtomSpecialization.ofSubstitution target.universeLevel caller) program target
      (constraint.substitute (FreshInstantiation.substitution source.binders level)) ↔
      EntailsSubstitution program target caller constraint := by
  let specialization := FreshAtomSpecialization.ofSubstitution target.universeLevel caller
  have mappedKinded : ∀ value ∈ FreshInstantiation.values source.binders level,
      Kinding program target (specialization.term value) value.kind := by
    intro value present
    have member : specialization.term value ∈ arguments := by
      rw [← FreshInstantiation.specialize_values opened fresh]
      exact List.mem_map.mpr ⟨value,present,rfl⟩
    simpa only [specialization.kind] using argumentsKinded _ member
  have interpreted := FreshAtomInterpretation.entails_instantiated specialization valid targetKinded rfl kinded
    (FreshInstantiation.instantiated opened.1 level) mappedKinded levels regions brands
    (kinded.fresh_atoms_fixed specialization levels)
  simpa only [specialization,FreshInstantiation.specialize_substitution opened fresh] using interpreted

/-- A proof checked at one fresh generative universe specializes to every
well-kinded caller instance, including duplicate or compound arguments and
nested universal requirements. Caller evidence discharges the actual source
requirements; no conclusion-shaped transport premise is assumed. -/
theorem Entails.specialize_fresh_instance {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {constraint : Constraint} {arguments : List Term} {caller : Substitution}
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (sourceKinded : ∀ requirement ∈ source.assumptions, ConstraintKinded program source requirement)
    (kinded : ConstraintKinded program source constraint)
    (opened : Instantiates source.binders arguments caller)
    (argumentsKinded : ∀ argument ∈ arguments, Kinding program target argument argument.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands)
    (assumptions : ∀ requirement ∈ source.assumptions, EntailsSubstitution program target caller requirement)
    (held : Entails program
      { target with universeLevel := target.universeLevel + 1
                    assumptions := source.assumptions.map (fun requirement => requirement.substitute
          (FreshInstantiation.substitution source.binders (target.universeLevel + 1))) }
      (constraint.substitute (FreshInstantiation.substitution source.binders (target.universeLevel + 1)))) :
    EntailsSubstitution program target caller constraint := by
  let specialization := FreshAtomSpecialization.ofSubstitution target.universeLevel caller
  have admitted := FreshInstantiation.admitted opened argumentsKinded
  have fresh : target.universeLevel < target.universeLevel + 1 := Nat.lt_succ_self _
  apply (FreshInstantiation.entails_iff valid targetKinded kinded opened argumentsKinded levels regions brands fresh).mp
  apply held.interpret_fresh_universe valid specialization admitted targetKinded rfl rfl (Nat.le_succ _)
  intro requirement member
  obtain ⟨template,present,rfl⟩ := List.mem_map.mp member
  exact (FreshInstantiation.entails_iff valid targetKinded (sourceKinded template present) opened
    argumentsKinded levels regions brands fresh).mpr (assumptions template present)

end Glorious.Language
