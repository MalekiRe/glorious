import GloriousLanguage.PositiveSubstitution

/-! Genuine definitional conversion, including in an assumption-bearing
caller, is preserved by lawful instantiation. This proof uses only conversion
closure and the proved positive root transport; it does not reconstruct
implementation selection or reinterpret conversion as assumed equality. -/
namespace Glorious.Language

theorem DefinitionallyEqual.map_substitute {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {left right : Term} (equal : DefinitionallyEqual program source left right)
    (sourceKinded : ∀ requirement ∈ source.assumptions, ConstraintKinded program source requirement)
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (outer : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute outer) binder.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands)
    (assumptions : ∀ requirement ∈ source.assumptions, EntailsSubstitution program target outer requirement) :
    DefinitionallyEqual program target (SubstitutionAtomModel.term outer left) (SubstitutionAtomModel.term outer right) := by
  let map := SubstitutionAtomModel.term outer
  have shape : AtomHomomorphism map := SubstitutionAtomModel.shape outer
  have transported : source = source → DefinitionallyEqual program target (map left) (map right) := by
    apply DefinitionallyEqual.rec
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
      (motive_11 := fun context left right _ => context = source →
        DefinitionallyEqual program target (map left) (map right))
      (motive_12 := fun _ _ _ _ => True)
      (motive_13 := fun _ _ _ _ _ => True)
      (motive_14 := fun _ _ _ _ _ _ _ _ _ => True)
      (motive_15 := fun _ _ _ _ _ _ _ => True)
      (motive_16 := fun _ _ _ _ _ _ => True)
      <;> try assumption
    all_goals intros
    all_goals try exact True.intro
    case refl _ _ sameContext => cases sameContext; exact .refl
    case symm _ _ _ _ ih sameContext => cases sameContext; exact .symm (ih rfl)
    case trans _ _ _ _ _ _ first second sameContext =>
      cases sameContext
      exact .trans (first rfl) (second rfl)
    case congrChildren _ _ _ same _ children sameContext =>
      cases sameContext
      exact shape.congr_relation (fun _ => .refl) DefinitionallyEqual.congr same
        (ListRel.of_at same.children_length (fun index first second leftAt rightAt =>
          children index first second leftAt rightAt rfl))
    case step _ _ _ stepped _ sameContext =>
      cases sameContext
      exact .step (stepped.map_substitute valid sourceKinded targetKinded
        outer parameters levels regions brands assumptions)
    case row _ _ _ equivalent sameContext =>
      cases sameContext
      exact .row (equivalent.map_atoms map shape)
  exact transported rfl

/-- Both endpoints use the language's actual simultaneous substitution;
right-endpoint kinding follows from the original conversion derivation. -/
theorem DefinitionallyEqual.substitute {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {left right : Term} {kind : Kind}
    (equal : DefinitionallyEqual program source left right)
    (sourceKinded : ∀ requirement ∈ source.assumptions, ConstraintKinded program source requirement)
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (kinded : Kinding program source left kind) (outer : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute outer) binder.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands)
    (assumptions : ∀ requirement ∈ source.assumptions, EntailsSubstitution program target outer requirement) :
    DefinitionallyEqual program target (left.substitute outer) (right.substitute outer) := by
  have transported := equal.map_substitute valid sourceKinded targetKinded outer parameters levels regions brands assumptions
  rw [SubstitutionAtomModel.kinded_eq kinded outer parameters,
    SubstitutionAtomModel.kinded_eq ((equal.kinding_iff valid kind).mp kinded) outer parameters] at transported
  exact transported

theorem DefinitionallyEqual.instantiate {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {left right : Term} {kind : Kind}
    (equal : DefinitionallyEqual program source left right)
    (sourceKinded : ∀ requirement ∈ source.assumptions, ConstraintKinded program source requirement)
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (kinded : Kinding program source left kind) {values : List Term} {substitution : Substitution}
    (instantiated : Instantiates source.binders values substitution)
    (valuesKinded : ∀ value ∈ values, Kinding program target value value.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands)
    (assumptions : ∀ requirement ∈ source.assumptions, EntailsSubstitution program target substitution requirement) :
    DefinitionallyEqual program target (left.substitute substitution) (right.substitute substitution) :=
  equal.substitute valid sourceKinded targetKinded kinded substitution (instantiated.kinding_parameters valuesKinded)
    levels regions brands assumptions

end Glorious.Language
