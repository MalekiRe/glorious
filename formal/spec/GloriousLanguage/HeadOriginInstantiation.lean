import GloriousLanguage.HeadOriginDecomposition
import GloriousLanguage.PositiveSubstitution

/-! Finite generic-origin expansions remain actual positive reductions after
caller instantiation. The original source reduction and whole-query conversion
are retained: neither is replaced by an unranked coherence witness or by an
assumed common reduct. -/
namespace Glorious.Language

theorem InfersHeadParameter.instantiate_decompose {program : Program} (valid : ProgramWellFormed program)
    {source context : Context} {binder : Binder} {template query value : Term} {kind : Kind}
    (inferred : InfersHeadParameter program source context binder template query value)
    (sourceKinded : ∀ requirement ∈ source.assumptions, ConstraintKinded program source requirement)
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    (templateKinded : Kinding program source template kind)
    {values : List Term} {substitution : Substitution}
    (instantiated : Instantiates source.binders values substitution)
    (valuesKinded : ∀ value ∈ values, Kinding program context value value.kind)
    (levels : source.universeLevel ≤ context.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ context.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ context.scope.brands)
    (requirements : ∀ requirement ∈ source.assumptions, EntailsSubstitution program context substitution requirement) :
    ∃ expanded converted,
      DefinitionalReduction program source template expanded ∧
      DefinitionalReduction program context (template.substitute substitution) (expanded.substitute substitution) ∧
      DefinitionallyEqual program context query converted ∧ StructuralHeadOrigin binder expanded converted value := by
  obtain ⟨expanded,converted,reduced,equal,path⟩ := inferred.decompose
  exact ⟨expanded,converted,reduced,reduced.instantiate valid sourceKinded contextKinded templateKinded
    instantiated valuesKinded levels regions brands requirements,equal,path⟩

/-- Actual implementation admission provides the kind of the source head;
actual selected requirements discharge the source expansion's assumptions. -/
theorem InfersHeadArgument.instantiate_decompose {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {implementation : ImplDefinition} {arguments : List Term} {binder : Binder} {value : Term}
    (inferred : InfersHeadArgument program context implementation arguments binder value)
    (declared : Definition.implementation implementation ∈ program.declarations)
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    {values : List Term} {substitution : Substitution}
    (instantiated : Instantiates implementation.generics values substitution)
    (valuesKinded : ∀ value ∈ values, Kinding program context value value.kind)
    (requirements : ∀ requirement ∈ implementation.requirements,
      EntailsSubstitution program context substitution requirement) :
    ∃ (index : Nat) (template query expanded converted : Term),
      implementation.arguments[index]? = some template ∧ arguments[index]? = some query ∧
      DefinitionalReduction program implementation.context template expanded ∧
      DefinitionalReduction program context (template.substitute substitution) (expanded.substitute substitution) ∧
      DefinitionallyEqual program context query converted ∧ StructuralHeadOrigin binder expanded converted value := by
  obtain ⟨_,_,_,_,_,_,_,signature,_⟩ := (valid.2.2.2.2.1 _ declared).2.1
  obtain ⟨_,_,_,_,headKinded,_,_⟩ := signature
  cases inferred with
  | argument sourceAt queryAt origin =>
    obtain ⟨expanded,converted,reduced,specialized,equal,path⟩ := origin.instantiate_decompose valid
      (valid.implementation_requirements declared) contextKinded
      (headKinded _ (List.mem_of_getElem? sourceAt)).1 instantiated valuesKinded (Nat.zero_le _)
      (fun _ present => False.elim (List.not_mem_nil present))
      (fun _ present => False.elim (List.not_mem_nil present)) requirements
    exact ⟨_,_,_,expanded,converted,sourceAt,queryAt,reduced,specialized,equal,path⟩

/-- For either actual selected raw table, every inferred binding of the other
table has a caller-instantiated positive source expansion. Coherence is used
only to identify the declaration, never to supply a conversion proof between
the inferred values. All determining evidence remains visible in the result. -/
theorem SelectsImpl.binding_origin_specialized {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {trait : DeclId} {arguments : List Term} {firstNegative secondNegative : Bool}
    {first second : ImplDefinition} {firstSub secondSub : Substitution}
    (left : SelectsImpl program context trait arguments firstNegative first firstSub)
    (right : SelectsImpl program context trait arguments secondNegative second secondSub)
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    {binder : Binder} {value : Term} (member : binder ∈ first.generics)
    (found : firstSub.get binder.id = some value) :
    ∃ (index : Nat) (template query expanded converted : Term),
      first.arguments[index]? = some template ∧ arguments[index]? = some query ∧
      DefinitionalReduction program first.context template expanded ∧
      DefinitionalReduction program context (template.substitute secondSub) (expanded.substitute secondSub) ∧
      DefinitionallyEqual program context query converted ∧ StructuralHeadOrigin binder expanded converted value := by
  obtain rfl := left.implementation_unique valid right
  have declared := left.declaration
  cases left with
  | selected _ _ _ matched _ =>
    cases right with
    | selected _ _ _ otherMatched requirements =>
      cases otherMatched with
      | inferred instantiated kinded _ _ _ _ =>
        exact (matched.binding_origin member found).instantiate_decompose valid declared contextKinded
          instantiated kinded requirements

end Glorious.Language
