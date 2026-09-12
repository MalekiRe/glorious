import GloriousLanguage.InspectionCompletion

/-! Ordinary definitional conversion has actual positive common reducts.
Complete finite source inspection supplies the induction, while canonical
parallel confluence joins its real query and body developments. No global
termination, constructor-injectivity oracle, or simulation premise is used. -/
namespace Glorious.Language

private theorem SelectsImpl.earlier_source_joins {program : Program} (valid : ProgramWellFormed program)
    {bound : Nat}
    (earlier : ∀ level, level < bound → ∀ (context : Context) (left right : Term)
      (equal : DefinitionallyEqual program context left right), FullHeadInspectionEqualityAt program level equal →
      (∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement) →
      InspectionJoinable program valid context left right)
    {context : Context} {trait : DeclId} {arguments : List Term} {negative : Bool}
    {implementation : ImplDefinition} {substitution : Substitution} {sourceLevel : Nat}
    (selected : SelectsImpl program context trait arguments negative implementation substitution)
    (source : FullImplementationInspectionAt program sourceLevel implementation) (lower : sourceLevel < bound)
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement) :
    ∀ binder (member : binder ∈ implementation.generics),
      InspectionJoinable program valid context
        (((valid.implementation_inspected selected.declaration).path binder member).template.substitute substitution)
        (((valid.implementation_inspected selected.declaration).path binder member).expanded.substitute substitution) := by
  let inspected := valid.implementation_inspected selected.declaration
  have minimumLower : inspected.level < bound := Nat.lt_of_le_of_lt (inspected.level_le source) lower
  obtain ⟨values,instantiated,kinded⟩ := selected.instantiates
  have requirements : ∀ requirement ∈ implementation.requirements, EntailsSubstitution program context substitution requirement := by
    cases selected with
    | selected _ _ _ _ requirements => exact requirements
  intro binder member
  obtain ⟨replay,certificate⟩ := (inspected.path binder member).caller_replay valid selected.declaration
    contextKinded instantiated kinded requirements
  exact earlier inspected.level minimumLower context _ _ replay.equal certificate.equal contextKinded

/-- Every complete finite equality certificate has a canonical common
reduct. Recursive source replay descends through the single full minimum;
actual query conversions are handled by the certificate's own induction. -/
theorem FullHeadInspectionEqualityAt.complete {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Term} {equal : DefinitionallyEqual program context left right} {level : Nat}
    (certificate : FullHeadInspectionEqualityAt program level equal)
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement) :
    InspectionJoinable program valid context left right := by
  have complete : ∀ level, ∀ (context : Context) (left right : Term) (equal : DefinitionallyEqual program context left right),
      FullHeadInspectionEqualityAt program level equal →
      (∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement) →
      InspectionJoinable program valid context left right := by
    intro bound
    induction bound using Nat.strongRecOn with
    | ind bound earlier =>
      intro context left right equal certificate contextKinded
      have result : bound ≤ bound →
          (∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement) →
          InspectionJoinable program valid context left right := by
        apply FullHeadInspectionEqualityAt.rec
          (motive_1 := fun _ _ _ => True)
          (motive_2 := fun _ _ _ _ => True)
          (motive_3 := fun level context left right _ _ => level ≤ bound →
            (∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement) →
            InspectionJoinable program valid context left right)
          (motive_4 := fun level context left right _ _ => level ≤ bound →
            (∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement) →
            InspectionJoinable program valid context left right)
          (motive_5 := fun _ _ _ _ _ _ => True)
          <;> try assumption
        all_goals intros
        all_goals try exact True.intro
        case alias =>
          refine ⟨_,InspectionReduction.root (PathInspectedStep.alias (found := by assumption)
            (instantiated := by assumption) (kinded := by assumption) (substituted := by assumption)),.refl⟩
        case projection =>
          rename_i sourceLevel rootLevel context trait member owners items associated ownerSub itemSub implementation implSub body value
            domain selected present graph _ source lower _ _ queries higher kinded
          have sourceJoins := selected.earlier_source_joins valid earlier source (Nat.lt_of_lt_of_le lower higher) kinded
          have lengths : (implementation.arguments.map (Term.substitute implSub)).length = owners.length := by
            cases selected with
            | selected _ _ _ matched _ =>
              cases matched with
              | inferred _ _ substituted lengths _ _ => simpa only [List.length_map] using substituted.length_eq.trans lengths
          exact DefinitionalStep.override_complete valid domain selected present graph
            (valid.implementation_inspected selected.declaration) kinded
            (ListRel.of_at lengths (fun index first second firstAt secondAt => queries index first second firstAt secondAt higher kinded))
            sourceJoins
        case defaultProjection =>
          rename_i sourceLevel rootLevel context trait member owners items associated ownerSub itemSub implementation implSub body value
            domain selected absent default graph _ source lower _ _ queries higher kinded
          have sourceJoins := selected.earlier_source_joins valid earlier source (Nat.lt_of_lt_of_le lower higher) kinded
          have lengths : (implementation.arguments.map (Term.substitute implSub)).length = owners.length := by
            cases selected with
            | selected _ _ _ matched _ =>
              cases matched with
              | inferred _ _ substituted lengths _ _ => simpa only [List.length_map] using substituted.length_eq.trans lengths
          exact DefinitionalStep.default_complete valid domain selected absent default graph
            (valid.implementation_inspected selected.declaration) kinded
            (ListRel.of_at lengths (fun index first second firstAt secondAt => queries index first second firstAt secondAt higher kinded))
            sourceJoins
        case refl => exact .refl _
        case symm _ _ _ _ _ _ ih higher kinded => exact (ih higher kinded).symm
        case trans _ _ _ _ _ _ _ _ _ first second higher kinded => exact (first higher kinded).trans kinded (second higher kinded)
        case congrChildren _ _ _ _ same _ _ children higher kinded =>
          exact InspectionJoinable.congr same (ListRel.of_at same.children_length
            (fun index first second firstAt secondAt => children index first second firstAt secondAt higher kinded))
        case step _ _ _ _ _ _ root higher kinded => exact root higher kinded
        case row _ _ _ _ equivalent _ _ => exact ⟨_,InspectionReduction.row equivalent,.refl⟩
      exact result (Nat.le_refl _) contextKinded
  exact complete level context left right equal certificate contextKinded

/-- This is derived simulation for the ordinary authoritative equality
judgment, including its actual admitted projection/query derivations. -/
theorem DefinitionallyEqual.inspection_joinable {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Term} (equal : DefinitionallyEqual program context left right)
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement) :
    InspectionJoinable program valid context left right := by
  obtain ⟨_,certificate⟩ := equal.full_inspected
  exact certificate.complete valid contextKinded

/-- Church–Rosser for ordinary definitional conversion: the common term and
both positive reductions are actual witnesses in the original language. -/
theorem DefinitionallyEqual.joinable {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Term} (equal : DefinitionallyEqual program context left right)
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement) :
    DefinitionallyJoinable program context left right := (equal.inspection_joinable valid contextKinded).positive

theorem DefinitionalReduction.confluence {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {source left right : Term}
    (first : DefinitionalReduction program context source left) (second : DefinitionalReduction program context source right)
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement) :
    DefinitionallyJoinable program context left right := (first.equal.symm.trans second.equal).joinable valid contextKinded

end Glorious.Language
