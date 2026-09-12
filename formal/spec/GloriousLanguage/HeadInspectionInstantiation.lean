import GloriousLanguage.HeadInspection
import GloriousLanguage.PositiveSubstitution

/-! The well-founded source-inspection evidence is consumed by actual caller
inference. The chosen source expansion is replayed positively in the caller;
no arbitrary source-query conversion remains in this constructed origin. -/
namespace Glorious.Language

private def InspectedAtBetween (program : Program) (context : Context) (level : Nat) (left right : Term) : Prop :=
  ∃ reduced : DefinitionalReduction program context left right, HeadInspectionReductionAt program level reduced

private theorem InspectedAtBetween.reflexive (program : Program) (context : Context) (level : Nat) (term : Term) :
    InspectedAtBetween program context level term term := ⟨.refl,.refl⟩

private theorem InspectedAtBetween.congr {program : Program} {context : Context} {level : Nat} {left right : Term}
    (same : SameHead left right)
    (children : ListRel (InspectedAtBetween program context level) left.children right.children) :
    InspectedAtBetween program context level left right := by
  classical
  let reductions := fun index first second (leftAt : left.children[index]? = some first)
      (rightAt : right.children[index]? = some second) => Classical.choose (children.at leftAt rightAt)
  exact ⟨.congrChildren same reductions,.congrChildren (same := same) (children := reductions)
    (fun _ _ _ leftAt rightAt => Classical.choose_spec (children.at leftAt rightAt))⟩

/-- Caller replay preserves the same finite source-inspection bound. This
induction consumes the certificate, not a supposed syntactic size of a proof
in `Prop`; each root is transported by the existing semantic producer. -/
theorem HeadInspectionReductionAt.map_substitute {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {left right : Term} {reduced : DefinitionalReduction program source left right}
    {level : Nat} (certificate : HeadInspectionReductionAt program level reduced)
    (sourceKinded : ∀ requirement ∈ source.assumptions, ConstraintKinded program source requirement)
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (outer : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute outer) binder.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands)
    (assumptions : ∀ requirement ∈ source.assumptions, EntailsSubstitution program target outer requirement) :
    ∃ mapped : DefinitionalReduction program target (SubstitutionAtomModel.term outer left) (SubstitutionAtomModel.term outer right),
      HeadInspectionReductionAt program level mapped := by
  let map := SubstitutionAtomModel.term outer
  have shape : AtomHomomorphism map := SubstitutionAtomModel.shape outer
  have transported : source = source → InspectedAtBetween program target level (map left) (map right) := by
    apply HeadInspectionReductionAt.rec
      (motive_1 := fun _ _ _ => True)
      (motive_2 := fun _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ _ _ => True)
      (motive_4 := fun level context left right _ _ => context = source →
        InspectedAtBetween program target level (map left) (map right))
      <;> try assumption
    all_goals intros
    all_goals try exact True.intro
    case refl _ _ _ sameContext => cases sameContext; exact ⟨.refl,.refl⟩
    case step level _ _ _ stepped inspected _ sameContext =>
      cases sameContext
      obtain ⟨mapped,preserved⟩ := stepped.map_substitute_inspected valid sourceKinded targetKinded
        outer parameters levels regions brands assumptions
      exact ⟨.step mapped,.step (stepped := mapped) (preserved level inspected)⟩
    case trans _ _ _ _ _ _ _ _ _ first second sameContext =>
      cases sameContext
      obtain ⟨first,firstInspected⟩ := first rfl
      obtain ⟨second,secondInspected⟩ := second rfl
      exact ⟨first.trans second,.trans (first := first) (second := second) firstInspected secondInspected⟩
    case congrChildren level _ _ _ same _ _ children sameContext =>
      cases sameContext
      exact shape.congr_relation (InspectedAtBetween.reflexive program target level) InspectedAtBetween.congr same
        (ListRel.of_at same.children_length (fun index first second leftAt rightAt =>
          children index first second leftAt rightAt rfl))
    case row _ _ _ _ equivalent sameContext =>
      cases sameContext
      exact ⟨.row (equivalent.map_atoms map shape),.row (equivalent := equivalent.map_atoms map shape)⟩
  exact transported rfl

theorem HeadInspectionReductionAt.instantiate {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {left right : Term} {kind : Kind}
    {reduced : DefinitionalReduction program source left right}
    {level : Nat} (certificate : HeadInspectionReductionAt program level reduced)
    (sourceKinded : ∀ requirement ∈ source.assumptions, ConstraintKinded program source requirement)
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (kinded : Kinding program source left kind) {values : List Term} {substitution : Substitution}
    (instantiated : Instantiates source.binders values substitution)
    (valuesKinded : ∀ value ∈ values, Kinding program target value value.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands)
    (assumptions : ∀ requirement ∈ source.assumptions, EntailsSubstitution program target substitution requirement) :
    ∃ mapped : DefinitionalReduction program target (left.substitute substitution) (right.substitute substitution),
      HeadInspectionReductionAt program level mapped := by
  have parameters := instantiated.kinding_parameters valuesKinded
  have transported := certificate.map_substitute valid sourceKinded targetKinded substitution parameters levels regions brands assumptions
  rw [SubstitutionAtomModel.kinded_eq kinded substitution parameters,
    SubstitutionAtomModel.kinded_eq (reduced.kinding valid kinded) substitution parameters] at transported
  exact transported

/-- A structural path in the source instantiates at that same ordered path.
Unvisited subterms may be opaque projections or aliases. -/
theorem StructuralHeadOrigin.instantiate_source {binder : Binder} {template query value : Term}
    (origin : StructuralHeadOrigin binder template query value) (substitution : Substitution)
    (kind : ((substitution.get binder.id).getD (.parameter binder.id binder.kind)).kind = binder.kind) :
    StructuralHeadOrigin binder template (template.substitute substitution)
      ((substitution.get binder.id).getD (.parameter binder.id binder.kind)) := by
  induction origin with
  | parameter => simpa only [Term.substitute] using StructuralHeadOrigin.parameter kind
  | @child template _ _ _ _ index structural _ sourceAt _ _ ih =>
    have notParameter : ∀ id kind, template ≠ .parameter id kind := by
      intro id kind equal
      subst template
      simp [Term.children] at sourceAt
    exact .child structural (Term.substitute_head notParameter substitution).symm sourceAt
      (by rw [Term.substitute_children notParameter,List.getElem?_map,sourceAt]; rfl) ih

/-- All source-inspection fields are derived from admission. Both positive
edges and the exact structural caller lookup remain visible to consumers. -/
theorem ProgramWellFormed.implementation_positive_origins {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {implementation : ImplDefinition} {values : List Term} {substitution : Substitution}
    (declared : Definition.implementation implementation ∈ program.declarations)
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    (instantiated : Instantiates implementation.generics values substitution)
    (valuesKinded : ∀ value ∈ values, Kinding program context value value.kind)
    (requirements : ∀ requirement ∈ implementation.requirements,
      EntailsSubstitution program context substitution requirement) :
    ∀ (index : Nat) binder value, implementation.generics[index]? = some binder → values[index]? = some value →
      ∃ (position : Nat) (template expanded : Term)
        (sourceReduced : DefinitionalReduction program implementation.context template expanded)
        (callerReduced : DefinitionalReduction program context (template.substitute substitution) (expanded.substitute substitution)),
        implementation.arguments[position]? = some template ∧
          HeadInspectionReductionAt program (valid.implementation_inspected declared).level sourceReduced ∧
          HeadInspectionReductionAt program (valid.implementation_inspected declared).level callerReduced ∧
          StructuralHeadOrigin binder expanded (expanded.substitute substitution) value := by
  obtain ⟨_,_,_,_,_,_,_,signature,_⟩ := (valid.2.2.2.2.1 _ declared).2.1
  obtain ⟨_,_,_,_,headKinded,_,_⟩ := signature
  intro index binder value binderAt valueAt
  obtain ⟨position,template,expanded,reduced,sourceAt,certificate,path⟩ :=
    (valid.implementation_inspected declared).minimum_source_exposure (List.mem_of_getElem? binderAt)
  have lookup := instantiated.binder_lookup_at binderAt valueAt
  have actualKind := (instantiated.2.1.at binderAt valueAt).symm
  have specializedPath := path.instantiate_source substitution (by simpa only [lookup,Option.getD_some] using actualKind)
  rw [lookup] at specializedPath
  obtain ⟨callerReduced,callerCertificate⟩ :=
    certificate.instantiate valid (valid.implementation_requirements declared) contextKinded
      (headKinded template (List.mem_of_getElem? sourceAt)).1 instantiated valuesKinded (Nat.zero_le _)
      (fun _ absent => False.elim (List.not_mem_nil absent))
      (fun _ absent => False.elim (List.not_mem_nil absent)) requirements
  exact ⟨position,template,expanded,reduced,callerReduced,sourceAt,certificate,callerCertificate,specializedPath⟩

/-- Source and query expose the determining position by paired positive
expansion. This is an actual existing `InfersHeadArgument` derivation. -/
theorem ProgramWellFormed.implementation_inspected_origins {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {implementation : ImplDefinition} {values : List Term} {substitution : Substitution}
    (declared : Definition.implementation implementation ∈ program.declarations)
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    (instantiated : Instantiates implementation.generics values substitution)
    (valuesKinded : ∀ value ∈ values, Kinding program context value value.kind)
    (requirements : ∀ requirement ∈ implementation.requirements,
      EntailsSubstitution program context substitution requirement) :
    ∀ (index : Nat) binder value, implementation.generics[index]? = some binder → values[index]? = some value →
      InfersHeadArgument program context implementation (implementation.arguments.map (Term.substitute substitution)) binder value := by
  intro index binder value binderAt valueAt
  obtain ⟨position,template,expanded,reduced,callerReduced,sourceAt,_,_,path⟩ :=
    valid.implementation_positive_origins declared contextKinded instantiated valuesKinded requirements
      index binder value binderAt valueAt
  exact .argument sourceAt (by rw [List.getElem?_map,sourceAt]; rfl)
    (.sourceReduction reduced (.queryConversion callerReduced.equal path.infers))

end Glorious.Language
