import GloriousLanguage.DefinitionalSeparation
import GloriousLanguage.CapabilityModels

/-! Closed capability evidence has an actual structural origin. Finite
logical/expansion proofs expose one local equation, while its recursive
dependencies retain their original coinductive evidence. Conversion-safe
inversion consumes ordinary Church–Rosser, not a raw syntax equation oracle. -/
namespace Glorious.Language

theorem CapabilityEquation.structural_head {program : Program} {assignment : Term → Option Principal}
    {type : Term} {principal : Principal} (equation : CapabilityEquation program assignment type principal) :
    type.StructuralHead := by
  cases equation <;> trivial

/-- A genuine local structural equation, with actual evidence for every
dependency consulted by its original assignment. This is an inversion
product of the existing producer, not a second capability definition. -/
def CapabilityStructuralOrigin (program : Program) (context : Context) (type : Term) (principal : Principal) : Prop :=
  ∃ exposed supported assignment, DefinitionallyEqual program context type exposed ∧
    principal.Restricts supported ∧ CapabilityEquation program assignment exposed supported ∧
    ∀ dependency claimed, assignment dependency = some claimed → CapabilityEvidence program context dependency claimed

theorem CapabilityStructuralOrigin.restrict {program : Program} {context : Context} {type : Term}
    {first last : Principal} (origin : CapabilityStructuralOrigin program context type last)
    (restriction : first.Restricts last) : CapabilityStructuralOrigin program context type first := by
  obtain ⟨exposed,supported,assignment,equal,ordered,equation,leaves⟩ := origin
  exact ⟨exposed,supported,assignment,equal,restriction.trans ordered,equation,leaves⟩

theorem CapabilityStructuralOrigin.convert {program : Program} {context : Context} {before after : Term}
    {principal : Principal} (origin : CapabilityStructuralOrigin program context before principal)
    (equal : DefinitionallyEqual program context before after) : CapabilityStructuralOrigin program context after principal := by
  obtain ⟨exposed,supported,assignment,original,ordered,equation,leaves⟩ := origin
  exact ⟨exposed,supported,assignment,equal.symm.trans original,ordered,equation,leaves⟩

namespace CapabilityOriginInterpretation

noncomputable def algebra (program : Program) (context : Context) :
    PredicateSemantics.PredicateAlgebra (DefinitionalQuotient.Class program context) where
  toTermAlgebra := (DefinitionalQuotient.algebra program context).toTermAlgebra
  outlives := fun _ _ => True
  typeOutlives := fun _ _ => True
  rows := fun _ _ => True
  implements := fun _ _ _ => True
  use := fun value quantity => ∃ type principal, DefinitionalQuotient.ofTerm type = value ∧
    CapabilityStructuralOrigin program context type principal ∧ quantity.Request principal
  callable := fun _ _ _ _ _ => True
  runsIn := fun _ _ _ _ _ => True

theorem eval_canonical {program : Program} {context : Context} (term : Term) :
    (algebra program context).eval DefinitionalQuotient.canonical term = DefinitionalQuotient.ofTerm term :=
  DefinitionalQuotient.eval_canonical term

def Holds (program : Program) (context : Context) (constraint : Constraint) : Prop :=
  (algebra program context).Holds program context DefinitionalQuotient.canonical DefinitionalQuotient.canonical constraint

theorem holds_equal {program : Program} {context : Context} {left right : Term} :
    Holds program context (.equal left right) ↔ DefinitionallyEqual program context left right := by
  unfold Holds PredicateSemantics.PredicateAlgebra.Holds
  rw [eval_canonical,eval_canonical,DefinitionalQuotient.ofTerm_eq]

theorem holds_use {program : Program} {context : Context} {type : Term} {quantity : Quantity} :
    Holds program context (.use type quantity) ↔
      ∃ principal, CapabilityStructuralOrigin program context type principal ∧ quantity.Request principal := by
  unfold Holds PredicateSemantics.PredicateAlgebra.Holds
  rw [eval_canonical]
  change (∃ source principal, DefinitionalQuotient.ofTerm source = (DefinitionalQuotient.ofTerm type :
    DefinitionalQuotient.Class program context) ∧ CapabilityStructuralOrigin program context source principal ∧
      quantity.Request principal) ↔ _
  constructor
  · rintro ⟨source,principal,equal,origin,request⟩
    exact ⟨principal,origin.convert (DefinitionalQuotient.ofTerm_eq.mp equal),request⟩
  · rintro ⟨principal,origin,request⟩
    exact ⟨type,principal,rfl,origin,request⟩

end CapabilityOriginInterpretation

/-- Every closed logical or coinductive permission eventually exposes a
structural equation. Transparent expansion remains finite in this induction;
recursive fields retain their actual whole-family evidence. -/
theorem CapabilityEvidence.closed_origin {program : Program} {context : Context} {type : Term} {principal : Principal}
    (evidence : CapabilityEvidence program context type principal) (closed : context.assumptions = []) :
    CapabilityStructuralOrigin program context type principal := by
  apply CapabilityEvidence.rec
    (motive_1 := fun context type principal _ => context.assumptions = [] →
      CapabilityStructuralOrigin program context type principal)
    (motive_2 := fun context assignment type principal _ => context.assumptions = [] →
      (∀ dependency claimed, assignment dependency = some claimed → CapabilityEvidence program context dependency claimed) →
      CapabilityStructuralOrigin program context type principal)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ => True)
    (motive_8 := fun context constraint _ => context.assumptions = [] → CapabilityOriginInterpretation.Holds program context constraint)
    (motive_9 := fun context substitution constraint _ => context.assumptions = [] →
      CapabilityOriginInterpretation.Holds program context (constraint.substitute substitution))
    (motive_10 := fun _ _ _ _ => True)
    (motive_11 := fun _ _ _ _ => True)
    (motive_12 := fun _ _ _ _ => True)
    (motive_13 := fun _ _ _ _ _ => True)
    (motive_14 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_15 := fun _ _ _ _ _ _ _ => True)
    (motive_16 := fun _ _ _ _ _ _ => True)
    <;> try assumption
  all_goals intros
  all_goals try exact True.intro
  all_goals try {
    rename_i member closed
    rw [closed] at member
    exact False.elim (List.not_mem_nil member) }
  case structural _ _ _ assignment found unfolded origins closed =>
    exact origins _ _ found closed (fun dependency claimed selected => .structural selected unfolded)
  case logical _ _ _ _ _ _ restriction held closed =>
    obtain ⟨supported,origin,requested⟩ := CapabilityOriginInterpretation.holds_use.mp (held closed)
    exact origin.restrict (restriction supported requested)
  case equal _ _ _ _ equal _ _ origin closed =>
    exact (origin closed).convert (equal.closed_definitional closed)
  case equation _ _ type _ supported restriction equation closed leaves =>
    exact ⟨type,supported,_,.refl,restriction,equation,leaves⟩
  case evidence _ _ _ _ _ restriction _ origin closed leaves => exact (origin closed).restrict restriction
  case expansion _ _ _ _ _ reduced _ _ origin closed leaves =>
    exact (origin closed leaves).convert (DefinitionallyEqual.step reduced).symm
  case congrSubstitution context _ _ _ _ _ equal before after _ _ previous closed =>
    exact ((CapabilityOriginInterpretation.algebra program context).holds_substitution_congr program context
      DefinitionalQuotient.canonical DefinitionalQuotient.canonical
      (fun id kind => by
        rw [CapabilityOriginInterpretation.eval_canonical,CapabilityOriginInterpretation.eval_canonical]
        exact DefinitionalQuotient.ofTerm_eq.mpr ((equal id kind).closed_definitional closed)) before after).mp (previous closed)
  case equality _ _ _ equal _ closed => exact CapabilityOriginInterpretation.holds_equal.mpr (equal.closed_definitional closed)
  case use _ _ _ _ _ requested origin closed =>
    exact CapabilityOriginInterpretation.holds_use.mpr ⟨_,origin closed,requested⟩
  case quantified context _ _ _ instances closed =>
    exact (CapabilityOriginInterpretation.algebra program context).holds_quantified program context DefinitionalQuotient.canonical
      (fun values substitution instantiated kinded requirement member =>
        instances values substitution instantiated kinded requirement member closed)
  case quantifiedInstance context _ _ _ _ _ _ _ instantiated kinded member graph held closed =>
    exact (CapabilityOriginInterpretation.algebra program context).holds_quantifiedInstance program context DefinitionalQuotient.canonical
      (held closed) instantiated kinded member graph
  case instantiated _ _ _ _ graph _ held closed =>
    rw [← graph.2]
    exact held closed
  all_goals simp only [CapabilityOriginInterpretation.Holds,PredicateSemantics.PredicateAlgebra.Holds,
    CapabilityOriginInterpretation.algebra]

theorem CapabilityEvidence.closed_structural {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {type : Term} {principal : Principal} (evidence : CapabilityEvidence program context type principal)
    (closed : context.assumptions = []) (structural : type.StructuralHead) :
    ∃ exposed supported assignment, SameHead type exposed ∧
      ListRel (DefinitionallyEqual program context) type.children exposed.children ∧ principal.Restricts supported ∧
      CapabilityEquation program assignment exposed supported ∧
      ∀ dependency claimed, assignment dependency = some claimed → CapabilityEvidence program context dependency claimed := by
  obtain ⟨exposed,supported,assignment,equal,ordered,equation,leaves⟩ := evidence.closed_origin closed
  obtain ⟨head,children⟩ := equal.structural_decomposition valid
    (fun _ member => by rw [closed] at member; cases member) structural equation.structural_head
  exact ⟨exposed,supported,assignment,head,children,ordered,equation,leaves⟩

theorem CapabilityEvidence.closed_unique_restriction {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {region type : Term} {principal : Principal}
    (evidence : CapabilityEvidence program context (.reference .unique region type) principal)
    (closed : context.assumptions = []) : principal.Restricts .affine := by
  obtain ⟨_,_,_,head,_,ordered,equation,_⟩ := evidence.closed_structural valid closed True.intro
  cases equation <;> simp only [SameHead,Term.mapChildren] at head <;> try contradiction
  all_goals try { cases head }
  exact ordered

/-- A copied reference can only be a shared handle, even if its permission
was obtained through logical conversion or recursive capability evidence. -/
theorem PrincipalOf.reference_copy_shared {program : Program} (valid : ProgramWellFormed program)
    {mode : Mutability} {region type : Term}
    (capability : PrincipalOf program (.reference mode region type) .duplicable) : mode = .shared := by
  cases mode with
  | shared => rfl
  | unique =>
    obtain ⟨context,closed,evidence⟩ := capability.1
    have bound := evidence.closed_unique_restriction valid closed
    have impossible : 2 ≤ 1 := bound 2 True.intro
    omega

end Glorious.Language
