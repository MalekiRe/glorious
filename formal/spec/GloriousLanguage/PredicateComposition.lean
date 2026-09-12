import GloriousLanguage.LogicalPredicateInterpretation
import GloriousLanguage.InstantiationComposition

/-! Hygienic predicate composition is logical equivalence, not syntactic
identity: each opening may choose different fresh quantified binders. The
actual source kinding derivation identifies exactly which free caller
parameters may affect its meaning. -/
namespace Glorious.Language

universe u

namespace PredicateSemantics

theorem TermAlgebra.eval_kinded_congr {α : Type u} (algebra : TermAlgebra α)
    {program : Program} {source : Context} {term : Term} {kind : Kind}
    (kinded : Kinding program source term kind) {left right : Valuation α}
    (agree : ∀ binder ∈ source.binders, left binder.id binder.kind = right binder.id binder.kind) :
    algebra.eval left term = algebra.eval right term := by
  apply algebra.eval_congr
  intro id kind occurs
  obtain ⟨binder,member,sameId,sameKind⟩ := kinded.parameter_occurs occurs
  simpa only [sameId,sameKind] using agree binder member

/-- Source kinding supplies free-variable scope. A quantified binder masks
the outer entry and takes its value from the actual `Instantiates` table;
defaults do not become additional logical truth conditions. -/
theorem PredicateAlgebra.holds_kinded_congr {α : Type u} (algebra : PredicateAlgebra α)
    {program : Program} {source : Context} {constraint : Constraint}
    (kinded : ConstraintKinded program source constraint) (context : Context) (caller : Valuation α)
    {left right : Valuation α}
    (agree : ∀ binder ∈ source.binders, left binder.id binder.kind = right binder.id binder.kind) :
    algebra.Holds program context caller left constraint ↔ algebra.Holds program context caller right constraint := by
  induction kinded generalizing left right with
  | equal first second =>
    simp only [PredicateAlgebra.Holds,algebra.eval_kinded_congr first agree,algebra.eval_kinded_congr second agree]
  | outlives first second =>
    simp only [PredicateAlgebra.Holds,algebra.eval_kinded_congr first agree,algebra.eval_kinded_congr second agree]
  | typeOutlives first second =>
    simp only [PredicateAlgebra.Holds,algebra.eval_kinded_congr first agree,algebra.eval_kinded_congr second agree]
  | rowIncludes first second =>
    simp only [PredicateAlgebra.Holds,algebra.eval_kinded_congr first agree,algebra.eval_kinded_congr second agree]
  | implements _ _ arguments =>
    have same := List.map_congr_left (fun term member => algebra.eval_kinded_congr (arguments term member) agree)
    simp only [PredicateAlgebra.Holds,same]
  | use type _ => simp only [PredicateAlgebra.Holds,algebra.eval_kinded_congr type agree]
  | callable receiver arguments result effects =>
    have same := List.map_congr_left (fun term member => algebra.eval_kinded_congr (arguments term member) agree)
    simp only [PredicateAlgebra.Holds,algebra.eval_kinded_congr receiver agree,
      algebra.eval_kinded_congr result agree,algebra.eval_kinded_congr effects agree,same]
  | runsIn receiver access arguments after =>
    have same := List.map_congr_left (fun term member => algebra.eval_kinded_congr (arguments term member) agree)
    simp only [PredicateAlgebra.Holds,algebra.eval_kinded_congr receiver agree,
      algebra.eval_kinded_congr access agree,algebra.eval_kinded_congr after agree,same]
  | @quantified source binders requirements _ _ _ ih =>
    rw [PredicateAlgebra.Holds,PredicateAlgebra.Holds]
    apply forall_congr'; intro values
    apply forall_congr'; intro substitution
    apply imp_congr_right; intro instantiated
    apply imp_congr_right; intro _
    apply forall_congr'; intro requirement
    apply imp_congr_right; intro member
    apply ih requirement member
    intro binder present
    rcases List.mem_append.mp present with bound | outer
    · obtain ⟨value,_,_,found⟩ := instantiated.binder_lookup bound
      simp only [TermAlgebra.bindValuation,found,Option.map_some,Option.getD_some]
    · have inherited := agree binder (List.mem_filter.mp outer).1
      cases found : substitution.get binder.id <;>
        simp only [TermAlgebra.bindValuation,found,Option.map,inherited,Option.getD]

end PredicateSemantics

/-- Instantiating a source predicate and then substituting its caller values
is equivalent to the one actual declaration table with transformed values.
The result is valid through arbitrarily nested quantified requirements. -/
theorem ConstraintKinded.instantiate_substitute_entails {program : Program} (valid : ProgramWellFormed program)
    {source middle target : Context} {constraint : Constraint}
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (kinded : ConstraintKinded program source constraint)
    {arguments : List Term} {inner : Substitution} (instantiated : Instantiates source.binders arguments inner)
    (argumentsKinded : ∀ argument ∈ arguments, Kinding program middle argument argument.kind)
    (outer : Substitution)
    (parameters : ∀ binder ∈ middle.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute outer) binder.kind)
    (firstLevels : source.universeLevel ≤ middle.universeLevel)
    (firstRegions : ∀ id ∈ source.scope.regions, id ∈ middle.scope.regions)
    (firstBrands : ∀ id ∈ source.scope.brands, id ∈ middle.scope.brands)
    (secondLevels : middle.universeLevel ≤ target.universeLevel)
    (secondRegions : ∀ id ∈ middle.scope.regions, id ∈ target.scope.regions)
    (secondBrands : ∀ id ∈ middle.scope.brands, id ∈ target.scope.brands) :
    Entails program target ((constraint.substitute inner).substitute outer) ↔
      EntailsSubstitution program target
        (inner.map (fun entry => (entry.1,entry.2.substitute outer))) constraint := by
  let transformed : Substitution := inner.map (fun entry => (entry.1,entry.2.substitute outer))
  have mapped := instantiated.substitute_values argumentsKinded outer parameters secondLevels secondRegions secondBrands
  have transformedKinded : ∀ argument ∈ arguments.map (Term.substitute outer), Kinding program target argument argument.kind := by
    intro term member
    obtain ⟨argument,present,rfl⟩ := List.mem_map.mp member
    have typed := (argumentsKinded argument present).substitute outer parameters secondLevels secondRegions secondBrands
    rw [typed.term_kind]
    exact typed
  have direct := kinded.instantiate mapped transformedKinded (Nat.le_trans firstLevels secondLevels)
    (fun id present => secondRegions id (firstRegions id present))
    (fun id present => secondBrands id (firstBrands id present))
  have nested := (kinded.instantiate instantiated argumentsKinded firstLevels firstRegions firstBrands).2.substitute
    outer parameters secondLevels secondRegions secondBrands
  have interpretation : LogicalQuotient.Holds program target ((constraint.substitute inner).substitute outer) ↔
      LogicalQuotient.Holds program target (constraint.substitute transformed) := by
    unfold LogicalQuotient.Holds
    rw [(LogicalQuotient.algebra program target).holds_substitute,
      (LogicalQuotient.algebra program target).holds_substitute,
      (LogicalQuotient.algebra program target).holds_substitute]
    apply (LogicalQuotient.algebra program target).holds_kinded_congr kinded
    intro binder member
    obtain ⟨argument,_,_,found⟩ := instantiated.binder_lookup member
    simp only [PredicateSemantics.TermAlgebra.substituteValuation,transformed,Table.get_map_values,found,
      Option.map_some,Option.getD_some,PredicateSemantics.TermAlgebra.eval_substitute]
  constructor
  · intro held
    exact .instantiated direct.1 ((LogicalQuotient.holds_iff_entails valid targetKinded direct.2).mp
      (interpretation.mp ((LogicalQuotient.holds_iff_entails valid targetKinded nested).mpr held)))
  · intro held
    exact (LogicalQuotient.holds_iff_entails valid targetKinded nested).mp
      (interpretation.mpr ((LogicalQuotient.holds_iff_entails valid targetKinded direct.2).mpr held.actual_result))

end Glorious.Language
