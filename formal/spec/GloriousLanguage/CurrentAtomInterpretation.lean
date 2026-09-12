import GloriousLanguage.FreshAtomInterpretation
import GloriousLanguage.TermScope

/-! The caller valuation remains fixed while lexical parameters receive a
separate initial valuation. Universal arguments are pulled back through actual
kinded preimages, not assumed to inhabit the source lexical parameter scope. -/
namespace Glorious.Language

open PredicateSemantics

theorem Instantiates.pullback_values {program : Program} {source target : Context}
    {binders : List Binder} {values : List Term} {substitution : Substitution}
    (instantiated : Instantiates binders values substitution)
    (typed : ∀ value ∈ values, Kinding program target value value.kind) (map : Term → Term)
    (kinds : ∀ term, (map term).kind = term.kind)
    (preimages : ∀ term kind, Kinding program target term kind →
      ∃ original, Kinding program source original kind ∧ map original = term) :
    ∃ originalValues originalSub, Instantiates binders originalValues originalSub ∧
      (∀ value ∈ originalValues, Kinding program source value value.kind) ∧
      originalSub.map (fun entry => (entry.1,map entry.2)) = substitution := by
  classical
  let pick := fun term => if admitted : Kinding program target term term.kind then
    Classical.choose (preimages term term.kind admitted) else term
  have picked (term : Term) (admitted : Kinding program target term term.kind) :
      Kinding program source (pick term) term.kind ∧ map (pick term) = term := by
    simp only [pick,dif_pos admitted]
    exact Classical.choose_spec (preimages term term.kind admitted)
  have original := instantiated.map_values pick (fun term member => (picked term (typed term member)).1.term_kind)
  refine ⟨values.map pick,substitution.map (fun entry => (entry.1,pick entry.2)),original,?_,?_⟩
  · intro term member
    obtain ⟨value,present,rfl⟩ := List.mem_map.mp member
    have kinded := (picked value (typed value present)).1
    simpa only [kinded.term_kind] using kinded
  · have again := original.map_values map (fun term _ => kinds term)
    have valuesEqual : (values.map pick).map map = values := by
      rw [List.map_map]
      apply List.map_eq_self_of
      intro term member
      exact (picked term (typed term member)).2
    rw [valuesEqual] at again
    exact again.2.2.trans instantiated.2.2.symm

namespace FreshAtomInterpretation

def HoldsAt (specialization : FreshAtomSpecialization) (program : Program) (context : Context)
    (current : Valuation (LogicalQuotient.Class program context)) (constraint : Constraint) : Prop :=
  (algebra specialization program context).Holds program context LogicalQuotient.canonical current constraint

theorem holds_at_atomic_iff (specialization : FreshAtomSpecialization) {program : Program}
    (valid : ProgramWellFormed program) {context : Context}
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    (current : Valuation (LogicalQuotient.Class program context)) (map : Term → Term)
    (evaluated : ∀ term, (algebra specialization program context).eval current term = LogicalQuotient.ofTerm (map term))
    {constraint : Constraint} (atomic : constraint.Atomic) :
    HoldsAt specialization program context current constraint ↔ Entails program context (constraint.mapTerms map) := by
  have mappedAtomic : (constraint.mapTerms map).Atomic := by
    cases constraint <;> simp only [Constraint.Atomic,Constraint.mapTerms] at atomic ⊢
  apply Iff.trans _ (LogicalQuotient.holds_atomic valid contextKinded mappedAtomic)
  have evaluation := funext evaluated
  have canonical : (LogicalQuotient.algebra program context).eval LogicalQuotient.canonical = LogicalQuotient.ofTerm :=
    funext LogicalQuotient.eval_canonical
  cases constraint <;> simp only [Constraint.Atomic] at atomic
  all_goals try contradiction
  all_goals unfold HoldsAt LogicalQuotient.Holds
  all_goals simp only [Constraint.mapTerms,PredicateAlgebra.Holds,evaluation,canonical,List.map_map,Function.comp_def]
  all_goals rfl

theorem substitute_bind_at (specialization : FreshAtomSpecialization) {program : Program} {context : Context}
    (admitted : specialization.Admitted program context)
    (current : Valuation (LogicalQuotient.Class program context)) (map : Term → Term)
    (evaluated : ∀ term, (algebra specialization program context).eval current term = LogicalQuotient.ofTerm (map term))
    {binders : List Binder} {values : List Term} {substitution : Substitution}
    (instantiated : Instantiates binders values substitution)
    (typed : ∀ value ∈ values, Kinding program context (map value) value.kind) :
    (algebra specialization program context).substituteValuation current substitution =
      (algebra specialization program context).bindValuation LogicalQuotient.canonical current
        (substitution.map (fun entry => (entry.1,map entry.2))) := by
  funext id kind
  simp only [TermAlgebra.substituteValuation,TermAlgebra.bindValuation,Table.get_map_values,Option.map_map,Function.comp_def]
  cases found : substitution.get id <;> simp only [Option.map,Option.getD]
  case some value =>
    rw [evaluated,eval_canonical,specialization.fixed admitted.1 (typed value (instantiated.argument_of_get found))]

theorem quantified_instance_at (specialization : FreshAtomSpecialization) {program : Program} {context : Context}
    (admitted : specialization.Admitted program context)
    (current : Valuation (LogicalQuotient.Class program context)) (map : Term → Term)
    (kinds : ∀ term, (map term).kind = term.kind)
    (evaluated : ∀ term, (algebra specialization program context).eval current term = LogicalQuotient.ofTerm (map term))
    {binders : List Binder} {requirements : List Constraint} {values : List Term} {substitution : Substitution}
    {requirement result : Constraint} (held : HoldsAt specialization program context current (.quantified binders requirements))
    (instantiated : Instantiates binders values substitution)
    (typed : ∀ value ∈ values, Kinding program context (map value) value.kind)
    (member : requirement ∈ requirements) (graph : SubstituteConstraint substitution requirement result) :
    HoldsAt specialization program context current result := by
  unfold HoldsAt at held ⊢
  rw [graph.2,(algebra specialization program context).holds_substitute,
    substitute_bind_at specialization admitted current map evaluated instantiated typed]
  rw [PredicateAlgebra.Holds] at held
  apply held (values.map map) (substitution.map (fun entry => (entry.1,map entry.2)))
    (instantiated.map_values map (fun value _ => kinds value)) _ requirement member
  intro value present
  obtain ⟨original,inside,rfl⟩ := List.mem_map.mp present
  simpa only [kinds] using typed original inside

theorem quantified_at (specialization : FreshAtomSpecialization) {program : Program} {source target : Context}
    (admitted : specialization.Admitted program target)
    (current : Valuation (LogicalQuotient.Class program target)) (map : Term → Term)
    (kinds : ∀ term, (map term).kind = term.kind)
    (evaluated : ∀ term, (algebra specialization program target).eval current term = LogicalQuotient.ofTerm (map term))
    (forward : ∀ term kind, Kinding program source term kind → Kinding program target (map term) kind)
    (preimages : ∀ term kind, Kinding program target term kind →
      ∃ original, Kinding program source original kind ∧ map original = term)
    {binders : List Binder} {requirements : List Constraint}
    (instances : ∀ values substitution, Instantiates binders values substitution →
      (∀ value ∈ values, Kinding program source value value.kind) → ∀ requirement ∈ requirements,
        HoldsAt specialization program target current (requirement.substitute substitution)) :
    HoldsAt specialization program target current (.quantified binders requirements) := by
  unfold HoldsAt
  rw [PredicateAlgebra.Holds]
  intro values substitution instantiated typed requirement member
  obtain ⟨originalValues,originalSub,original,originalKinded,mapped⟩ :=
    instantiated.pullback_values typed map kinds preimages
  have held := instances originalValues originalSub original originalKinded requirement member
  unfold HoldsAt at held
  rw [(algebra specialization program target).holds_substitute,
    substitute_bind_at specialization admitted current map evaluated original
      (fun value present => forward value value.kind (originalKinded value present)),mapped] at held
  exact held

theorem holds_at_instantiated (specialization : FreshAtomSpecialization) {program : Program} {source target : Context}
    (level : target.universeLevel = specialization.cutoff)
    (current : Valuation (LogicalQuotient.Class program target)) (map : Term → Term)
    (evaluated : ∀ term, (algebra specialization program target).eval current term = LogicalQuotient.ofTerm (map term))
    {constraint : Constraint} (kinded : ConstraintKinded program source constraint)
    {values : List Term} {substitution : Substitution} (instantiated : Instantiates source.binders values substitution)
    (fixed : ∀ term ∈ constraint.terms, term.AtomsFixed specialization.term) :
    HoldsAt specialization program target current (constraint.substitute substitution) ↔
      LogicalQuotient.Holds program target (constraint.substitute (substitution.map (fun entry => (entry.1,map entry.2)))) := by
  unfold HoldsAt LogicalQuotient.Holds
  rw [(algebra specialization program target).holds_substitute,(LogicalQuotient.algebra program target).holds_substitute,
    holds_fixed specialization level constraint fixed]
  apply (LogicalQuotient.algebra program target).holds_kinded_congr kinded target LogicalQuotient.canonical
  intro binder member
  obtain ⟨value,_,_,found⟩ := instantiated.binder_lookup member
  simp only [TermAlgebra.substituteValuation,Table.get_map_values,found,Option.map,Option.getD,
    evaluated,LogicalQuotient.eval_canonical]

theorem entails_at_instantiated (specialization : FreshAtomSpecialization) {program : Program}
    (valid : ProgramWellFormed program) {source target : Context}
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (level : target.universeLevel = specialization.cutoff)
    (current : Valuation (LogicalQuotient.Class program target)) (map : Term → Term)
    (kinds : ∀ term, (map term).kind = term.kind)
    (evaluated : ∀ term, (algebra specialization program target).eval current term = LogicalQuotient.ofTerm (map term))
    {constraint : Constraint} (kinded : ConstraintKinded program source constraint)
    {values : List Term} {substitution : Substitution} (instantiated : Instantiates source.binders values substitution)
    (valuesKinded : ∀ value ∈ values, Kinding program target (map value) value.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands)
    (fixed : ∀ term ∈ constraint.terms, term.AtomsFixed specialization.term) :
    HoldsAt specialization program target current (constraint.substitute substitution) ↔
      EntailsSubstitution program target (substitution.map (fun entry => (entry.1,map entry.2))) constraint := by
  have mapped := instantiated.map_values map (fun term _ => kinds term)
  obtain ⟨graph,resultKinded⟩ := kinded.instantiate mapped (fun value present => by
    obtain ⟨original,member,rfl⟩ := List.mem_map.mp present
    simpa only [kinds] using valuesKinded original member) levels regions brands
  rw [holds_at_instantiated specialization level current map evaluated kinded instantiated fixed,
    LogicalQuotient.holds_iff_entails valid targetKinded resultKinded]
  exact ⟨EntailsSubstitution.instantiated graph,EntailsSubstitution.actual_result⟩

end FreshAtomInterpretation
end Glorious.Language
