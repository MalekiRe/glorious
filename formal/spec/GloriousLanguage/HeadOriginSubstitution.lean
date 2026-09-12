import GloriousLanguage.DefinitionalSubstitution
import GloriousLanguage.HeadInspectionInstantiation

/-! Admitted finite source origins construct actual caller matching evidence
under arbitrary lawful instantiation, including source aliases and associated
expansions. Caller query conversions use genuine definitional substitution;
lexical source reductions remain the original source derivations. -/
namespace Glorious.Language

theorem InfersHeadParameter.map_substitute {program : Program} (valid : ProgramWellFormed program)
    {sourceContext source target : Context} {binder : Binder} {template query value : Term}
    (inferred : InfersHeadParameter program sourceContext source binder template query value)
    (sourceKinded : ∀ requirement ∈ source.assumptions, ConstraintKinded program source requirement)
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (outer : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute outer) binder.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands)
    (assumptions : ∀ requirement ∈ source.assumptions, EntailsSubstitution program target outer requirement) :
    InfersHeadParameter program sourceContext target binder template
      (SubstitutionAtomModel.term outer query) (SubstitutionAtomModel.term outer value) := by
  let map := SubstitutionAtomModel.term outer
  have shape : AtomHomomorphism map := SubstitutionAtomModel.shape outer
  have transported : source = source →
      InfersHeadParameter program sourceContext target binder template (map query) (map value) := by
    apply InfersHeadParameter.rec
      (motive_1 := fun _ _ _ _ => True)
      (motive_2 := fun _ _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ _ => True)
      (motive_5 := fun _ _ _ _ => True)
      (motive_6 := fun _ _ _ _ => True)
      (motive_7 := fun _ _ _ _ => True)
      (motive_8 := fun _ _ _ => True)
      (motive_9 := fun _ _ _ _ => True)
      (motive_10 := fun _ _ _ _ => True)
      (motive_11 := fun _ _ _ _ => True)
      (motive_12 := fun _ _ _ _ => True)
      (motive_13 := fun _ _ _ _ _ => True)
      (motive_14 := fun _ _ _ _ _ _ _ _ _ => True)
      (motive_15 := fun sourceContext context binder template query value _ => context = source →
        InfersHeadParameter program sourceContext target binder template (map query) (map value))
      (motive_16 := fun _ _ _ _ _ _ => True)
      <;> try assumption
    all_goals intros
    all_goals try exact True.intro
    case parameter _ _ _ _ kind sameContext =>
      cases sameContext
      exact .parameter ((SubstitutionAtomModel.kind outer _).trans kind)
    case child _ _ _ _ _ _ _ _ _ structural same sourceAt queryAt _ ih sameContext =>
      cases sameContext
      obtain ⟨mappedHead,mappedChildren⟩ := shape.child_head same (List.mem_of_getElem? queryAt)
      exact .child structural mappedHead sourceAt
        (by rw [mappedChildren,List.getElem?_map,queryAt]; rfl) (ih rfl)
    case sourceReduction _ _ _ _ _ _ _ reduced _ _ ih sameContext =>
      cases sameContext
      exact .sourceReduction reduced (ih rfl)
    case queryConversion _ _ _ _ _ _ _ equal _ _ ih sameContext =>
      cases sameContext
      exact .queryConversion (equal.map_substitute valid sourceKinded targetKinded outer parameters
        levels regions brands assumptions) (ih rfl)
  exact transported rfl

theorem InfersHeadArgument.map_substitute {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {implementation : ImplDefinition} {arguments : List Term} {binder : Binder} {value : Term}
    (inferred : InfersHeadArgument program source implementation arguments binder value)
    (sourceKinded : ∀ requirement ∈ source.assumptions, ConstraintKinded program source requirement)
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (outer : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute outer) binder.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands)
    (assumptions : ∀ requirement ∈ source.assumptions, EntailsSubstitution program target outer requirement) :
    InfersHeadArgument program target implementation (arguments.map (SubstitutionAtomModel.term outer))
      binder (SubstitutionAtomModel.term outer value) := by
  cases inferred with
  | argument sourceAt queryAt origin =>
    exact .argument sourceAt (by rw [List.getElem?_map,queryAt]; rfl)
      (origin.map_substitute valid sourceKinded targetKinded outer parameters levels regions brands assumptions)

/-- Every source-admitted determining origin is instantiated in the caller
through paired positive inspection. No second origin search or completeness
hypothesis is requested: actual admission supplies the finite source proof. -/
theorem ProgramWellFormed.implementation_instantiated_origins {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {implementation : ImplDefinition} {values : List Term} {substitution : Substitution}
    (declared : Definition.implementation implementation ∈ program.declarations)
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    (instantiated : Instantiates implementation.generics values substitution)
    (valuesKinded : ∀ value ∈ values, Kinding program context value value.kind)
    (requirements : ∀ requirement ∈ implementation.requirements,
      EntailsSubstitution program context substitution requirement) :
    ∀ (index : Nat) binder value, implementation.generics[index]? = some binder → values[index]? = some value →
      InfersHeadArgument program context implementation (implementation.arguments.map (Term.substitute substitution)) binder value :=
  valid.implementation_inspected_origins declared contextKinded instantiated valuesKinded requirements

/-- Matching the actual instantiated head of any admitted implementation is
constructible, including heads whose determining positions need source
expansion. Requirements discharge that source proof in the real caller. -/
theorem MatchesImplHead.of_admitted_instantiation {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {implementation : ImplDefinition} {values : List Term} {substitution : Substitution}
    (declared : Definition.implementation implementation ∈ program.declarations)
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    (instantiated : Instantiates implementation.generics values substitution)
    (valuesKinded : ∀ value ∈ values, Kinding program context value value.kind)
    (requirements : ∀ requirement ∈ implementation.requirements,
      EntailsSubstitution program context substitution requirement) :
    MatchesImplHead program context implementation (implementation.arguments.map (Term.substitute substitution)) substitution :=
  .instantiated valid declared instantiated valuesKinded
    (valid.implementation_instantiated_origins declared contextKinded instantiated valuesKinded requirements)

/-- End-to-end declared selection now constructs its finite generic origins
from source admission. The caller supplies only actual argument kinding, head
convertibility and instantiated requirements, not a second inference proof. -/
theorem SelectsImpl.of_admitted_head {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {implementation : ImplDefinition} {values arguments : List Term} {substitution : Substitution}
    (declared : Definition.implementation implementation ∈ program.declarations)
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    (instantiated : Instantiates implementation.generics values substitution)
    (valuesKinded : ∀ value ∈ values, Kinding program context value value.kind)
    (equal : ListRel (DefinitionallyEqual program context)
      (implementation.arguments.map (Term.substitute substitution)) arguments)
    (requirements : ∀ requirement ∈ implementation.requirements,
      EntailsSubstitution program context substitution requirement) :
    SelectsImpl program context implementation.trait arguments implementation.negative implementation substitution :=
  .selected declared rfl rfl
    ((MatchesImplHead.of_admitted_instantiation valid declared contextKinded instantiated valuesKinded requirements).congr_query equal)
    requirements

end Glorious.Language
