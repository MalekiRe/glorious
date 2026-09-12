import GloriousLanguage.LogicalPredicateCongruence
import GloriousLanguage.QuotientInterpretation

/-! The canonical interpretation of an admitted predicate is exactly its
actual logical entailment. Atomic meanings use the real entailment judgment;
quantifier meanings use its same fixed kinding domain and hygienic graph. -/
namespace Glorious.Language

namespace LogicalQuotient

def setoid (program : Program) (context : Context) : Setoid Term where
  r := Equal program context
  iseqv := ⟨fun _ => .refl,fun equal => .symm equal,fun first second => .trans first second⟩

abbrev Class (program : Program) (context : Context) := Quotient (setoid program context)

def ofTerm {program : Program} {context : Context} (term : Term) : Class program context := Quotient.mk _ term

theorem ofTerm_eq {program : Program} {context : Context} {left right : Term} :
    (ofTerm left : Class program context) = ofTerm right ↔ Equal program context left right :=
  ⟨Quotient.exact,fun equal => Quotient.sound equal⟩

noncomputable abbrev representative {program : Program} {context : Context} (value : Class program context) : Term :=
  PredicateSemantics.TermQuotient.representative value

theorem representative_equal {program : Program} {context : Context} (term : Term) :
    Equal program context term (representative (ofTerm term : Class program context)) := by
  apply ofTerm_eq.mp
  exact (PredicateSemantics.TermQuotient.representative_eq (ofTerm term)).symm

noncomputable def algebra (program : Program) (context : Context) : PredicateSemantics.PredicateAlgebra (Class program context) where
  toTermAlgebra := (PredicateSemantics.TermQuotient.algebra (setoid program context)
    (fun same children => Equal.congr same children)).toTermAlgebra
  outlives := fun long short => Entails program context (.outlives (representative long) (representative short))
  typeOutlives := fun type region => Entails program context (.typeOutlives (representative type) (representative region))
  rows := fun allowed required => Entails program context (.rowIncludes (representative allowed) (representative required))
  implements := fun trait arguments negative => Entails program context (.implements trait (arguments.map representative) negative)
  use := fun type quantity => Entails program context (.use (representative type) quantity)
  callable := fun receiver arguments result effects unsafeAllowed => Entails program context
    (.callable (representative receiver) (arguments.map representative) (representative result) (representative effects) unsafeAllowed)
  runsIn := fun receiver access arguments after unsafeAllowed => Entails program context
    (.runsIn (representative receiver) (representative access) (arguments.map representative) (representative after) unsafeAllowed)

def canonical {program : Program} {context : Context} : PredicateSemantics.Valuation (Class program context) :=
  fun id kind => ofTerm (.parameter id kind)

theorem eval_canonical {program : Program} {context : Context} (term : Term) :
    (algebra program context).eval canonical term = ofTerm term :=
  PredicateSemantics.TermQuotient.eval_canonical (setoid := setoid program context)
    (fun same children => Equal.congr same children) term

def Holds (program : Program) (context : Context) (constraint : Constraint) : Prop :=
  (algebra program context).Holds program context canonical canonical constraint

theorem holds_atomic {program : Program} (valid : ProgramWellFormed program)
    {context : Context} (contextKinded : ∀ constraint ∈ context.assumptions, ConstraintKinded program context constraint)
    {constraint : Constraint} (atomic : constraint.Atomic) :
    Holds program context constraint ↔ Entails program context constraint := by
  have converted := (Entails.congr_atomic_map_iff valid contextKinded atomic
    (fun term => representative (ofTerm term : Class program context))
    (fun term _ => representative_equal term)).symm
  have evalFunction : (algebra program context).eval canonical = (ofTerm : Term → Class program context) :=
    funext eval_canonical
  cases constraint <;> simp only [Constraint.Atomic] at atomic
  all_goals try contradiction
  all_goals unfold Holds
  all_goals rw [PredicateSemantics.PredicateAlgebra.Holds]
  all_goals rw [evalFunction]
  case equal left right =>
    rw [ofTerm_eq]
    exact ⟨Entails.equality,Equal.entailed⟩
  all_goals simpa only [algebra,Constraint.mapTerms,List.map_map,Function.comp_def] using converted

/-- This equivalence includes every nested universal predicate. It consumes
the real admission graph to instantiate each requirement, and so cannot turn
a malformed or missing instantiation into logical evidence. -/
theorem holds_iff_entails {program : Program} (valid : ProgramWellFormed program)
    {context : Context} (contextKinded : ∀ constraint ∈ context.assumptions, ConstraintKinded program context constraint)
    {constraint : Constraint} (kinded : ConstraintKinded program context constraint) :
    Holds program context constraint ↔ Entails program context constraint := by
  by_cases atomic : constraint.Atomic
  · exact holds_atomic valid contextKinded atomic
  · cases constraint <;> simp only [Constraint.Atomic] at atomic
    all_goals try contradiction
    case quantified binders requirements =>
      constructor
      · intro held
        apply Entails.quantified
        intro values substitution instantiated arguments requirement member
        obtain ⟨graph,requirementKinded⟩ := kinded.quantified_instance instantiated arguments member
        refine .instantiated graph ?_
        apply (holds_iff_entails valid contextKinded requirementKinded).mp
        exact (algebra program context).holds_quantifiedInstance program context canonical
          held instantiated arguments member graph
      · intro held
        apply (algebra program context).holds_quantified program context canonical
        intro values substitution instantiated arguments requirement member
        obtain ⟨graph,requirementKinded⟩ := kinded.quantified_instance instantiated arguments member
        apply (holds_iff_entails valid contextKinded requirementKinded).mpr
        exact .quantifiedInstance held instantiated arguments member graph
termination_by constraint.quantifierCount
decreasing_by
  all_goals
    subst constraint
    simp only [Constraint.quantifierCount_substitute,Constraint.quantifierCount]
    have smaller := List.nat_le_sum_of_mem (List.mem_map_of_mem (f := Constraint.quantifierCount) member)
    omega

end LogicalQuotient
end Glorious.Language
