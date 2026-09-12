import GloriousLanguage.FreshAtomSpecialization

/-! Fresh atom replacements are interpreted with the fixed caller valuation.
Nested lexical quantifiers continue to use the existing hygienic predicate
interpreter, so a replacement's caller parameters cannot become captured. -/
namespace Glorious.Language

open PredicateSemantics

namespace FreshAtomInterpretation

noncomputable def node (specialization : FreshAtomSpecialization) (program : Program) (context : Context)
    (term : Term) (children : List (LogicalQuotient.Class program context)) : LogicalQuotient.Class program context :=
  match term.mapChildren (fun _ => .unit) with
  | .rigid id kind level => LogicalQuotient.ofTerm (specialization.term (.rigid id kind level))
  | .variable id kind level => LogicalQuotient.ofTerm (specialization.term (.variable id kind level))
  | head => (LogicalQuotient.algebra program context).node head children

noncomputable def algebra (specialization : FreshAtomSpecialization) (program : Program) (context : Context) :
    PredicateAlgebra (LogicalQuotient.Class program context) :=
  { LogicalQuotient.algebra program context with
    node := node specialization program context
    sameHead := by
      intro left right same children
      unfold node
      rw [same] }

def Holds (specialization : FreshAtomSpecialization) (program : Program) (context : Context) (constraint : Constraint) : Prop :=
  (algebra specialization program context).Holds program context
    LogicalQuotient.canonical LogicalQuotient.canonical constraint

private theorem node_ordinary (specialization : FreshAtomSpecialization) (program : Program) (context : Context)
    (term : Term) (children : List (LogicalQuotient.Class program context))
    (notRigid : ∀ id kind level, term ≠ .rigid id kind level)
    (notVariable : ∀ id kind level, term ≠ .variable id kind level) :
    node specialization program context term children = (LogicalQuotient.algebra program context).node term children := by
  have ordinary := ((LogicalQuotient.algebra program context).sameHead
    (Term.sameHead_mapChildren term (fun _ => .unit)) children).symm
  cases term <;> simp only [node,Term.mapChildren] at ordinary ⊢
  case rigid id kind level => exact False.elim (notRigid id kind level rfl)
  case «variable» id kind level => exact False.elim (notVariable id kind level rfl)
  all_goals exact ordinary

private theorem logical_node {program : Program} {context : Context} (term : Term)
    (notParameter : ∀ id kind, term ≠ .parameter id kind) :
    (LogicalQuotient.algebra program context).node term (term.children.map LogicalQuotient.ofTerm) = LogicalQuotient.ofTerm term := by
  have evaluated := LogicalQuotient.eval_canonical (program := program) (context := context) term
  rw [(LogicalQuotient.algebra program context).eval_node _ notParameter] at evaluated
  have canonical : (LogicalQuotient.algebra program context).eval LogicalQuotient.canonical = LogicalQuotient.ofTerm :=
    funext LogicalQuotient.eval_canonical
  rw [canonical] at evaluated
  exact evaluated

theorem eval_canonical (specialization : FreshAtomSpecialization) {program : Program} {context : Context} (term : Term) :
    (algebra specialization program context).eval LogicalQuotient.canonical term =
      LogicalQuotient.ofTerm (specialization.term term) := by
  by_cases parameter : ∃ id kind, term = .parameter id kind
  · obtain ⟨id,kind,rfl⟩ := parameter
    simp only [TermAlgebra.eval_parameter,FreshAtomSpecialization.term,LogicalQuotient.canonical]
  · have notParameter : ∀ id kind, term ≠ .parameter id kind := fun id kind same => parameter ⟨id,kind,same⟩
    rw [(algebra specialization program context).eval_node _ notParameter]
    have children : term.children.map ((algebra specialization program context).eval LogicalQuotient.canonical) =
        term.children.map (fun child => LogicalQuotient.ofTerm (specialization.term child)) := by
      apply List.map_congr_left
      intro child _
      exact FreshAtomInterpretation.eval_canonical specialization child
    rw [children]
    change node specialization program context term _ = _
    cases term
    case parameter id kind => exact False.elim (notParameter id kind rfl)
    case rigid => simp only [node,Term.mapChildren]
    case «variable» => simp only [node,Term.mapChildren]
    case runtimeRegion id =>
      simp only [node,Term.mapChildren,FreshAtomSpecialization.term,Term.children,List.map_nil]
      exact logical_node (.runtimeRegion id) notParameter
    all_goals rw [node_ordinary specialization program context _ _ (by intros; simp) (by intros; simp)]
    all_goals rw [specialization.shape]
    all_goals
      have mapped := logical_node (program := program) (context := context) (_ : Term)
        (Term.mapChildren_ne_parameter notParameter specialization.term)
      rw [Term.mapChildren_children,List.map_map] at mapped
      rw [← (LogicalQuotient.algebra program context).sameHead (Term.sameHead_mapChildren _ specialization.term)] at mapped
      exact mapped
termination_by term
decreasing_by exact Term.child_sizeOf ‹_ ∈ term.children›

theorem eval_fixed (specialization : FreshAtomSpecialization) {program : Program} {context : Context}
    (current : Valuation (LogicalQuotient.Class program context)) (term : Term)
    (fixed : term.AtomsFixed specialization.term) :
    (algebra specialization program context).eval current term = (LogicalQuotient.algebra program context).eval current term := by
  by_cases parameter : ∃ id kind, term = .parameter id kind
  · obtain ⟨id,kind,rfl⟩ := parameter
    simp only [TermAlgebra.eval_parameter]
  · have notParameter : ∀ id kind, term ≠ .parameter id kind := fun id kind same => parameter ⟨id,kind,same⟩
    rw [(algebra specialization program context).eval_node _ notParameter,
      (LogicalQuotient.algebra program context).eval_node _ notParameter]
    have children : term.children.map ((algebra specialization program context).eval current) =
        term.children.map ((LogicalQuotient.algebra program context).eval current) := by
      apply List.map_congr_left
      intro child member
      exact eval_fixed specialization current child (fixed.child member)
    rw [children]
    change node specialization program context term _ = _
    cases term
    case parameter id kind => exact False.elim (notParameter id kind rfl)
    case rigid id kind level =>
      simp only [node,Term.mapChildren,Term.children,List.map_nil]
      rw [fixed _ .here]
      exact (logical_node (.rigid id kind level) notParameter).symm
    case «variable» id kind level =>
      simp only [node,Term.mapChildren,Term.children,List.map_nil]
      rw [fixed _ .here]
      exact (logical_node (.variable id kind level) notParameter).symm
    all_goals exact node_ordinary specialization program context _ _ (by intros; simp) (by intros; simp)
termination_by term
decreasing_by exact Term.child_sizeOf ‹_ ∈ term.children›

theorem bindValuation_fixed (specialization : FreshAtomSpecialization) {program : Program} {context : Context}
    (level : context.universeLevel = specialization.cutoff)
    (current : Valuation (LogicalQuotient.Class program context)) {binders : List Binder} {values : List Term}
    {substitution : Substitution} (instantiated : Instantiates binders values substitution)
    (kinded : ∀ value ∈ values, Kinding program context value value.kind) :
    (algebra specialization program context).bindValuation LogicalQuotient.canonical current substitution =
      (LogicalQuotient.algebra program context).bindValuation LogicalQuotient.canonical current substitution := by
  funext id kind
  unfold TermAlgebra.bindValuation
  cases found : substitution.get id with
  | none => rfl
  | some value =>
    have member : value ∈ values := instantiated.argument_of_get found
    simp only [Option.map,Option.getD,eval_canonical,LogicalQuotient.eval_canonical,
      specialization.fixed level (kinded value member)]

theorem holds_fixed (specialization : FreshAtomSpecialization) {program : Program} {context : Context}
    (level : context.universeLevel = specialization.cutoff) (constraint : Constraint)
    (fixed : ∀ term ∈ constraint.terms, term.AtomsFixed specialization.term)
    (current : Valuation (LogicalQuotient.Class program context)) :
    (algebra specialization program context).Holds program context LogicalQuotient.canonical current constraint ↔
      (LogicalQuotient.algebra program context).Holds program context LogicalQuotient.canonical current constraint := by
  have terms : ∀ term ∈ constraint.terms,
      (algebra specialization program context).eval current term = (LogicalQuotient.algebra program context).eval current term :=
    fun term member => eval_fixed specialization current term (fixed term member)
  cases constraint <;> rw [PredicateAlgebra.Holds,PredicateAlgebra.Holds]
  all_goals simp only [Constraint.terms] at terms fixed
  case equal left right => rw [terms left (by simp),terms right (by simp)]
  case outlives long short => rw [terms long (by simp),terms short (by simp)]; rfl
  case typeOutlives type region => rw [terms type (by simp),terms region (by simp)]; rfl
  case rowIncludes allowed required => rw [terms allowed (by simp),terms required (by simp)]; rfl
  case use type quantity => rw [terms type (by simp)]; rfl
  case implements trait arguments negative =>
    have argumentsEqual := List.map_congr_left (fun term member => terms term member)
    rw [argumentsEqual]
    rfl
  case callable receiver arguments result effects unsafeAllowed =>
    have argumentsEqual := List.map_congr_left (l := arguments) (fun term member => terms term (by simp [member]))
    rw [argumentsEqual,terms _ (by simp),terms _ (by simp),terms _ (by simp)]
    rfl
  case runsIn receiver access arguments after unsafeAllowed =>
    have argumentsEqual := List.map_congr_left (l := arguments) (fun term member => terms term (by simp [member]))
    rw [argumentsEqual,terms _ (by simp),terms _ (by simp),terms _ (by simp)]
    rfl
  case quantified binders requirements =>
    constructor <;> intro held values substitution instantiated kinded requirement member
    · have nested := held values substitution instantiated kinded requirement member
      rw [bindValuation_fixed specialization level current instantiated kinded] at nested
      apply (holds_fixed specialization level requirement (fun term present => fixed term
        (List.mem_append_right _ (List.mem_flatMap.mpr ⟨requirement,member,present⟩))) _).mp nested
    · apply (holds_fixed specialization level requirement (fun term present => fixed term
        (List.mem_append_right _ (List.mem_flatMap.mpr ⟨requirement,member,present⟩))) _).mpr
      rw [bindValuation_fixed specialization level current instantiated kinded]
      exact held values substitution instantiated kinded requirement member
termination_by constraint

theorem holds_instantiated (specialization : FreshAtomSpecialization) {program : Program} {context : Context}
    (level : context.universeLevel = specialization.cutoff) (constraint : Constraint) (substitution : Substitution)
    (fixed : ∀ term ∈ constraint.terms, term.AtomsFixed specialization.term) :
    Holds specialization program context (constraint.substitute substitution) ↔
      LogicalQuotient.Holds program context
        (constraint.substitute (substitution.map (fun entry => (entry.1,specialization.term entry.2)))) := by
  unfold Holds LogicalQuotient.Holds
  rw [(algebra specialization program context).holds_substitute,
    (LogicalQuotient.algebra program context).holds_substitute]
  have valuations : (algebra specialization program context).substituteValuation LogicalQuotient.canonical substitution =
      (LogicalQuotient.algebra program context).substituteValuation LogicalQuotient.canonical
        (substitution.map (fun entry => (entry.1,specialization.term entry.2))) := by
    funext id kind
    simp only [TermAlgebra.substituteValuation,Table.get_map_values,Option.map_map,Function.comp_def]
    cases found : substitution.get id <;> simp only [Option.map,Option.getD]
    rw [eval_canonical,LogicalQuotient.eval_canonical]
  rw [valuations]
  exact holds_fixed specialization level constraint fixed _

theorem holds_atomic_iff (specialization : FreshAtomSpecialization) {program : Program} (valid : ProgramWellFormed program)
    {context : Context} (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    {constraint : Constraint} (atomic : constraint.Atomic) :
    Holds specialization program context constraint ↔ Entails program context (constraint.mapTerms specialization.term) := by
  have mappedAtomic : (constraint.mapTerms specialization.term).Atomic := by
    cases constraint <;> simp only [Constraint.Atomic,Constraint.mapTerms] at atomic ⊢
  have base := LogicalQuotient.holds_atomic valid contextKinded mappedAtomic
  apply Iff.trans _ base
  have evaluated : (algebra specialization program context).eval LogicalQuotient.canonical =
      (fun term => LogicalQuotient.ofTerm (specialization.term term)) := funext (eval_canonical specialization)
  have canonical : (LogicalQuotient.algebra program context).eval LogicalQuotient.canonical = LogicalQuotient.ofTerm :=
    funext LogicalQuotient.eval_canonical
  cases constraint <;> simp only [Constraint.Atomic] at atomic
  all_goals try contradiction
  all_goals unfold Holds LogicalQuotient.Holds
  all_goals simp only [Constraint.mapTerms,PredicateAlgebra.Holds,evaluated,canonical,List.map_map,Function.comp_def]
  all_goals rfl

/-- Declaration requirements cross back to the actual entailment judgment
through their existing ordered instantiation and kinding producer, including
every nested quantified requirement. -/
theorem entails_instantiated (specialization : FreshAtomSpecialization) {program : Program}
    (valid : ProgramWellFormed program) {source target : Context}
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (level : target.universeLevel = specialization.cutoff) {constraint : Constraint}
    (kinded : ConstraintKinded program source constraint) {values : List Term} {substitution : Substitution}
    (instantiated : Instantiates source.binders values substitution)
    (valuesKinded : ∀ value ∈ values, Kinding program target (specialization.term value) value.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands)
    (fixed : ∀ term ∈ constraint.terms, term.AtomsFixed specialization.term) :
    Holds specialization program target (constraint.substitute substitution) ↔
      EntailsSubstitution program target (substitution.map (fun entry => (entry.1,specialization.term entry.2))) constraint := by
  have mapped := instantiated.map_values specialization.term (fun value _ => specialization.kind value)
  have mappedKinded : ∀ value ∈ values.map specialization.term, Kinding program target value value.kind := by
    intro value present
    obtain ⟨original,member,rfl⟩ := List.mem_map.mp present
    simpa only [specialization.kind] using valuesKinded original member
  obtain ⟨graph,resultKinded⟩ := kinded.instantiate mapped mappedKinded levels regions brands
  rw [holds_instantiated specialization level constraint substitution fixed,
    LogicalQuotient.holds_iff_entails valid targetKinded resultKinded]
  exact ⟨EntailsSubstitution.instantiated graph,EntailsSubstitution.actual_result⟩

theorem holds_mapped_substitution (specialization : FreshAtomSpecialization) {program : Program} {context : Context}
    (admitted : specialization.Admitted program context) (constraint : Constraint) (substitution : Substitution) :
    Holds specialization program context (constraint.substitute substitution) ↔
      Holds specialization program context
        (constraint.substitute (substitution.map (fun entry => (entry.1,specialization.term entry.2)))) := by
  unfold Holds
  rw [(algebra specialization program context).holds_substitute,
    (algebra specialization program context).holds_substitute]
  apply (algebra specialization program context).holds_congr_valuation
  intro id _ kind
  simp only [TermAlgebra.substituteValuation,Table.get_map_values,Option.map_map,Function.comp_def]
  cases found : substitution.get id <;> simp only [Option.map,Option.getD]
  rw [eval_canonical,eval_canonical,specialization.idempotent admitted]

/-- Universal elimination maps the actual source arguments. The existing
interpreter identifies the source and mapped instantiation valuations by
derived idempotence, so no new hygienic graph is assumed or reconstructed. -/
theorem quantified_instance (specialization : FreshAtomSpecialization) {program : Program} {context : Context}
    (admitted : specialization.Admitted program context) {binders : List Binder} {requirements : List Constraint}
    {values : List Term} {substitution : Substitution} {requirement result : Constraint}
    (held : Holds specialization program context (.quantified binders requirements))
    (instantiated : Instantiates binders values substitution)
    (kinded : ∀ value ∈ values, Kinding program context (specialization.term value) value.kind)
    (member : requirement ∈ requirements) (graph : SubstituteConstraint substitution requirement result) :
    Holds specialization program context result := by
  rw [graph.2]
  apply (holds_mapped_substitution specialization admitted requirement substitution).mpr
  unfold Holds at held ⊢
  rw [(algebra specialization program context).holds_substitute]
  rw [PredicateAlgebra.Holds] at held
  apply held (values.map specialization.term) (substitution.map (fun entry => (entry.1,specialization.term entry.2)))
    (instantiated.map_values specialization.term (fun value _ => specialization.kind value)) _ requirement member
  intro value present
  obtain ⟨original,inside,rfl⟩ := List.mem_map.mp present
  simpa only [specialization.kind] using kinded original inside

end FreshAtomInterpretation
end Glorious.Language
