import GloriousLanguage.LogicalParameterCut
import GloriousLanguage.PredicateComposition
import GloriousLanguage.ClosedDefinitionalEquality

/-! The general parameter cut is consumed by actual opened predicates and
logical equalities. Hygienic nested predicate composition uses its existing
semantic theorem; declaration binder identity and raw table order are kept. -/
namespace Glorious.Language

theorem EntailsSubstitution.substitute_values {program : Program} (valid : ProgramWellFormed program)
    {template source target : Context} {constraint : Constraint} {inner : Substitution}
    (held : EntailsSubstitution program source inner constraint)
    (sourceKinded : ∀ requirement ∈ source.assumptions, ConstraintKinded program source requirement)
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (kinded : ConstraintKinded program template constraint) {values : List Term}
    (instantiated : Instantiates template.binders values inner)
    (valuesKinded : ∀ value ∈ values, Kinding program source value value.kind)
    (outer : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute outer) binder.kind)
    (firstLevels : template.universeLevel ≤ source.universeLevel)
    (firstRegions : ∀ id ∈ template.scope.regions, id ∈ source.scope.regions)
    (firstBrands : ∀ id ∈ template.scope.brands, id ∈ source.scope.brands)
    (secondLevels : source.universeLevel ≤ target.universeLevel)
    (secondRegions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (secondBrands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands)
    (assumptions : ∀ requirement ∈ source.assumptions, EntailsSubstitution program target outer requirement) :
    EntailsSubstitution program target (inner.map (fun entry => (entry.1,entry.2.substitute outer))) constraint := by
  apply (kinded.instantiate_substitute_entails valid targetKinded instantiated valuesKinded outer parameters
    firstLevels firstRegions firstBrands secondLevels secondRegions secondBrands).mp
  exact held.actual_result.substitute valid sourceKinded targetKinded
    (kinded.instantiate instantiated valuesKinded firstLevels firstRegions firstBrands).2
    outer parameters secondLevels secondRegions secondBrands assumptions

theorem Equal.substitute {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {left right : Term} {kind : Kind}
    (equal : Equal program source left right)
    (sourceKinded : ∀ requirement ∈ source.assumptions, ConstraintKinded program source requirement)
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (kinded : Kinding program source left kind) (substitution : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute substitution) binder.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands)
    (assumptions : ∀ requirement ∈ source.assumptions, EntailsSubstitution program target substitution requirement) :
    Equal program target (left.substitute substitution) (right.substitute substitution) := by
  have rightKinded := (equal.kinding_iff valid sourceKinded kind).mp kinded
  have transported := (Entails.equality equal).substitute valid sourceKinded targetKinded
    (.equal kinded rightKinded) substitution parameters levels regions brands assumptions
  exact .entailed (by simpa only [Constraint.substitute] using transported)

/-- Opening an admitted source equality into an assumption-free caller
leaves genuine definitional equality. Source requirements are discharged by
actual logical cut; they are never silently dropped from the lexical context. -/
theorem Equal.instantiate_closed {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {left right : Term} {kind : Kind}
    (equal : Equal program source left right)
    (sourceKinded : ∀ requirement ∈ source.assumptions, ConstraintKinded program source requirement)
    (closed : target.assumptions = []) (kinded : Kinding program source left kind)
    {values : List Term} {substitution : Substitution} (instantiated : Instantiates source.binders values substitution)
    (valuesKinded : ∀ value ∈ values, Kinding program target value value.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands)
    (assumptions : ∀ requirement ∈ source.assumptions, EntailsSubstitution program target substitution requirement) :
    DefinitionallyEqual program target (left.substitute substitution) (right.substitute substitution) := by
  apply (equal.substitute valid sourceKinded (fun requirement member => False.elim (by simp only [closed,List.not_mem_nil] at member))
    kinded substitution (instantiated.kinding_parameters valuesKinded) levels regions brands assumptions).closed_definitional closed

theorem DefinitionallyEqual.instantiate_closed {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {left right : Term} {kind : Kind}
    (equal : DefinitionallyEqual program source left right)
    (sourceKinded : ∀ requirement ∈ source.assumptions, ConstraintKinded program source requirement)
    (closed : target.assumptions = []) (kinded : Kinding program source left kind)
    {values : List Term} {substitution : Substitution} (instantiated : Instantiates source.binders values substitution)
    (valuesKinded : ∀ value ∈ values, Kinding program target value value.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands)
    (assumptions : ∀ requirement ∈ source.assumptions, EntailsSubstitution program target substitution requirement) :
    DefinitionallyEqual program target (left.substitute substitution) (right.substitute substitution) :=
  (Equal.definitional equal).instantiate_closed valid sourceKinded closed kinded instantiated valuesKinded
    levels regions brands assumptions

end Glorious.Language
