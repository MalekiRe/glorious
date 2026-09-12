import GloriousLanguage.FullHeadInspection

/-! One authoritative full-source inspection minimum. The finite producer
retains actual head-query conversions; legacy weak evidence is obtained only
by erasing that full certificate at the same minimum. Logical requirements
are not declaration-expansion dependencies. -/
namespace Glorious.Language

abbrev ImplementationInspected := FullImplementationInspected

def HeadInspectionOrigin (program : Program) (implementation : ImplDefinition) (binder : Binder) : Prop :=
  ∃ level, HeadInspectionOriginAt program level implementation binder

def HeadInspectionStep (program : Program) {context : Context} {left right : Term}
    (stepped : DefinitionalStep program context left right) : Prop :=
  ∃ level, HeadInspectionStepAt program level stepped

def HeadInspectionReduction (program : Program) {context : Context} {left right : Term}
    (reduced : DefinitionalReduction program context left right) : Prop :=
  ∃ level, HeadInspectionReductionAt program level reduced

private theorem exists_least_nat {predicate : Nat → Prop} (available : ∃ level, predicate level) :
    ∃ level, predicate level ∧ ∀ other, predicate other → level ≤ other := by
  classical
  have least : ∀ level, predicate level → ∃ first, predicate first ∧ ∀ other, predicate other → first ≤ other := by
    intro level
    induction level using Nat.strongRecOn with
    | ind level ih =>
      intro present
      by_cases earlier : ∃ first, first < level ∧ predicate first
      · obtain ⟨first,lower,present⟩ := earlier
        exact ih first lower present
      · refine ⟨level,present,?_⟩
        intro other found
        by_cases higher : level ≤ other
        · exact higher
        · exact False.elim (earlier ⟨other,by omega,found⟩)
  obtain ⟨level,present⟩ := available
  exact least level present

/-- The minimum is taken over a whole implementation inspection, so all
generic exposures live in the same source context at one common level. -/
noncomputable def ImplementationInspected.level {program : Program} {implementation : ImplDefinition}
    (inspected : ImplementationInspected program implementation) : Nat := by
  classical
  exact Classical.choose (exists_least_nat inspected)

theorem ImplementationInspected.full_minimum {program : Program} {implementation : ImplDefinition}
    (inspected : ImplementationInspected program implementation) :
    FullImplementationInspectionAt program inspected.level implementation := by
  classical
  exact (Classical.choose_spec (exists_least_nat inspected)).1

/-- Weak clients receive erasure at the one full-source minimum, never an
independently minimized source-only certificate. -/
theorem ImplementationInspected.minimum {program : Program} {implementation : ImplDefinition}
    (inspected : ImplementationInspected program implementation) :
    ImplementationInspectionAt program inspected.level implementation := inspected.full_minimum.erase

theorem ImplementationInspected.level_le {program : Program} {implementation : ImplDefinition}
    (inspected : ImplementationInspected program implementation) {level : Nat}
    (certificate : FullImplementationInspectionAt program level implementation) : inspected.level ≤ level := by
  classical
  exact (Classical.choose_spec (exists_least_nat inspected)).2 level certificate

/-- A declaration is earlier only when both source inspections exist and
their canonical minimum levels strictly decrease. Missing evidence is never
assigned a low rank that would authorize a recursive source inspection. -/
def InspectionPrecedes (program : Program) (first second : ImplDefinition) : Prop :=
  ∃ (left : ImplementationInspected program first) (right : ImplementationInspected program second),
    left.level < right.level

theorem ImplementationInspected.precedes_of_lower {program : Program} {first second : ImplDefinition}
    (parent : ImplementationInspected program second) {level : Nat}
    (child : FullImplementationInspectionAt program level first) (lower : level < parent.level) :
    InspectionPrecedes program first second :=
  ⟨⟨level,child⟩,parent,Nat.lt_of_le_of_lt (ImplementationInspected.level_le ⟨level,child⟩ child) lower⟩

/-- This is well-foundedness of derived source inspection, not termination
of arbitrary term normalization and not a confluence assumption. -/
theorem InspectionPrecedes.wellFounded (program : Program) : WellFounded (InspectionPrecedes program) := by
  have accessible : ∀ level implementation (inspected : ImplementationInspected program implementation),
      inspected.level = level → Acc (InspectionPrecedes program) implementation := by
    intro level
    induction level using Nat.strongRecOn with
    | ind level ih =>
      intro implementation inspected same
      apply Acc.intro
      intro previous before
      obtain ⟨first,second,lower⟩ := before
      change first.level < inspected.level at lower
      rw [same] at lower
      exact ih first.level lower previous first rfl
  refine ⟨?_⟩
  intro implementation
  classical
  by_cases inspected : ImplementationInspected program implementation
  · exact accessible inspected.level implementation inspected rfl
  · apply Acc.intro
    intro previous before
    obtain ⟨_,second,_⟩ := before
    exact False.elim (inspected second)

/-- A projection certificate bounds the implementation actually selected at
its source. Coherence is used only for declaration identity, so proof
irrelevance cannot substitute a different implementation dependency. -/
theorem HeadInspectionStepAt.selected_level {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Term} {stepped : DefinitionalStep program context left right}
    {bound : Nat} (certificate : HeadInspectionStepAt program bound stepped)
    {trait member : DeclId} {owners items : List Term} {kind : Kind}
    (projection : left = .projection trait member owners items kind)
    {implementation : ImplDefinition} {substitution : Substitution}
    (selected : SelectsImpl program context trait owners false implementation substitution) :
    ∃ level, ImplementationInspectionAt program level implementation ∧ level < bound := by
  cases certificate with
  | alias => cases projection
  | @projection _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sourceSelected _ _ inspected lower =>
    cases projection
    obtain rfl := sourceSelected.implementation_unique valid selected
    exact ⟨_,inspected,lower⟩
  | @defaultProjection _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sourceSelected _ _ _ inspected lower =>
    cases projection
    obtain rfl := sourceSelected.implementation_unique valid selected
    exact ⟨_,inspected,lower⟩

theorem HeadInspectionStepAt.monotone {program : Program} {context : Context} {left right : Term}
    {stepped : DefinitionalStep program context left right} {level bound : Nat}
    (inspected : HeadInspectionStepAt program level stepped) (higher : level ≤ bound) :
    HeadInspectionStepAt program bound stepped := by
  cases inspected with
  | alias =>
    exact .alias (found := by assumption) (instantiated := by assumption)
      (kinded := by assumption) (substituted := by assumption)
  | projection lower below =>
    exact .projection (domain := by assumption) (selected := by assumption)
      (present := by assumption) (substituted := by assumption) lower (Nat.lt_of_lt_of_le below higher)
  | defaultProjection lower below =>
    exact .defaultProjection (domain := by assumption) (selected := by assumption)
      (absent := by assumption) (default := by assumption) (substituted := by assumption) lower (Nat.lt_of_lt_of_le below higher)

theorem HeadInspectionReductionAt.monotone {program : Program} {context : Context} {left right : Term}
    {reduced : DefinitionalReduction program context left right} {level bound : Nat}
    (inspected : HeadInspectionReductionAt program level reduced) (higher : level ≤ bound) :
    HeadInspectionReductionAt program bound reduced := by
  have widen : ∀ next, level ≤ next → HeadInspectionReductionAt program next reduced := by
    apply HeadInspectionReductionAt.rec
      (motive_1 := fun _ _ _ => True)
      (motive_2 := fun _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ _ _ => True)
      (motive_4 := fun level _ _ _ reduced _ =>
        ∀ next, level ≤ next → HeadInspectionReductionAt program next reduced)
      <;> try assumption
    all_goals intros
    all_goals try exact True.intro
    case refl => exact .refl
    case step _ _ _ _ stepped certificate _ _ higher => exact .step (stepped := stepped) (certificate.monotone higher)
    case trans _ _ _ _ _ first second _ _ firstIH secondIH next higher =>
      exact .trans (first := first) (second := second) (firstIH next higher) (secondIH next higher)
    case congrChildren _ _ _ _ same children _ childIH next higher =>
      exact .congrChildren (same := same) (children := children)
        (fun index first second leftAt rightAt => childIH index first second leftAt rightAt next higher)
    case row _ _ _ _ equivalent _ _ => exact .row (equivalent := equivalent)
  exact widen bound higher

theorem HeadInspectionOriginAt.monotone {program : Program} {implementation : ImplDefinition} {binder : Binder}
    {level bound : Nat} (origin : HeadInspectionOriginAt program level implementation binder) (higher : level ≤ bound) :
    HeadInspectionOriginAt program bound implementation binder := by
  cases origin with
  | exposed sourceAt inspected path => exact .exposed (reduced := by assumption) sourceAt (inspected.monotone higher) path

theorem ImplementationInspectionAt.monotone {program : Program} {implementation : ImplDefinition}
    {level bound : Nat} (inspected : ImplementationInspectionAt program level implementation) (higher : level ≤ bound) :
    ImplementationInspectionAt program bound implementation := by
  cases inspected with
  | inspected origins => exact .inspected (fun binder present => (origins binder present).monotone higher)

theorem ImplementationInspected.inspected {program : Program} {implementation : ImplDefinition}
    (origins : ∀ binder ∈ implementation.generics, FullHeadInspectionOrigin program implementation binder) :
    ImplementationInspected program implementation := FullImplementationInspected.inspected origins

theorem HeadInspectionOrigin.exposed {program : Program} {implementation : ImplDefinition} {binder : Binder}
    {index : Nat} {template expanded : Term}
    {reduced : DefinitionalReduction program implementation.context template expanded}
    (sourceAt : implementation.arguments[index]? = some template) (inspected : HeadInspectionReduction program reduced)
    (path : StructuralHeadOrigin binder expanded expanded (.parameter binder.id binder.kind)) :
    HeadInspectionOrigin program implementation binder := by
  obtain ⟨level,certificate⟩ := inspected
  exact ⟨level,.exposed (reduced := reduced) sourceAt certificate path⟩

theorem HeadInspectionStep.alias {program : Program} {context : Context} {id : DeclId} {declaration : AliasDefinition}
    {arguments : List Term} {substitution : Substitution} {value : Term}
    {found : program.alias id = some declaration} {instantiated : Instantiates declaration.generics arguments substitution}
    {kinded : ∀ argument ∈ arguments, Kinding program context argument argument.kind}
    {substituted : Substitutes substitution declaration.value value} :
    HeadInspectionStep program (.alias found instantiated kinded substituted) :=
  ⟨0,.alias (found := found) (instantiated := instantiated) (kinded := kinded) (substituted := substituted)⟩

theorem HeadInspectionStep.projection {program : Program} {context : Context}
    {trait member : DeclId} {owners items : List Term} {associated : AssociatedDefinition}
    {ownerSub itemSub : Substitution} {implementation : ImplDefinition} {implSub : Substitution} {body value : Term}
    {domain : ProjectionDomain program context trait member owners items associated ownerSub itemSub}
    {selected : SelectsImpl program context trait owners false implementation implSub}
    {present : (member,body) ∈ implementation.associated} {substituted : Substitutes (implSub ++ itemSub) body value}
    (inspected : ImplementationInspected program implementation) :
    HeadInspectionStep program (.projection domain selected present substituted) := by
  obtain ⟨level,certificate⟩ := inspected
  exact ⟨level+1,.projection (domain := domain) (selected := selected) (present := present)
    (substituted := substituted) certificate.erase (Nat.lt_succ_self _)⟩

theorem HeadInspectionStep.defaultProjection {program : Program} {context : Context}
    {trait member : DeclId} {owners items : List Term} {associated : AssociatedDefinition}
    {ownerSub itemSub : Substitution} {implementation : ImplDefinition} {implSub : Substitution} {body value : Term}
    {domain : ProjectionDomain program context trait member owners items associated ownerSub itemSub}
    {selected : SelectsImpl program context trait owners false implementation implSub}
    {absent : ∀ body, (member,body) ∉ implementation.associated} {default : associated.defaultValue = some body}
    {substituted : Substitutes (ownerSub ++ itemSub) body value}
    (inspected : ImplementationInspected program implementation) :
    HeadInspectionStep program (.defaultProjection domain selected absent default substituted) := by
  obtain ⟨level,certificate⟩ := inspected
  exact ⟨level+1,.defaultProjection (domain := domain) (selected := selected) (absent := absent)
    (default := default) (substituted := substituted) certificate.erase (Nat.lt_succ_self _)⟩

theorem HeadInspectionReduction.refl {program : Program} {context : Context} {term : Term} :
    HeadInspectionReduction program (DefinitionalReduction.refl (context := context) (term := term)) := ⟨0,.refl⟩

theorem HeadInspectionReduction.step {program : Program} {context : Context} {left right : Term}
    {stepped : DefinitionalStep program context left right} (inspected : HeadInspectionStep program stepped) :
    HeadInspectionReduction program (.step stepped) := by
  obtain ⟨level,certificate⟩ := inspected
  exact ⟨level,.step certificate⟩

theorem HeadInspectionReduction.trans {program : Program} {context : Context} {left middle right : Term}
    {first : DefinitionalReduction program context left middle} {second : DefinitionalReduction program context middle right}
    (firstInspected : HeadInspectionReduction program first) (secondInspected : HeadInspectionReduction program second) :
    HeadInspectionReduction program (.trans first second) := by
  obtain ⟨firstLevel,firstCertificate⟩ := firstInspected
  obtain ⟨secondLevel,secondCertificate⟩ := secondInspected
  exact ⟨max firstLevel secondLevel,.trans (firstCertificate.monotone (Nat.le_max_left _ _))
    (secondCertificate.monotone (Nat.le_max_right _ _))⟩

private def InspectedReductionAtBetween (program : Program) (context : Context) (level : Nat) (left right : Term) : Prop :=
  ∃ reduced : DefinitionalReduction program context left right, HeadInspectionReductionAt program level reduced

theorem HeadInspectionReduction.congrChildren {program : Program} {context : Context} {left right : Term}
    {same : SameHead left right}
    {children : ∀ (index : Nat) first second, left.children[index]? = some first → right.children[index]? = some second →
      DefinitionalReduction program context first second}
    (inspected : ∀ (index : Nat) first second leftAt rightAt,
      HeadInspectionReduction program (children index first second leftAt rightAt)) :
    HeadInspectionReduction program (.congrChildren same children) := by
  have pairs : ListRel (fun left right => ∃ level, InspectedReductionAtBetween program context level left right)
      left.children right.children := ListRel.of_at same.children_length (fun index first second firstAt secondAt => by
        obtain ⟨level,certificate⟩ := inspected index first second firstAt secondAt
        exact ⟨level,children index first second firstAt secondAt,certificate⟩)
  obtain ⟨level,bounded⟩ := pairs.exists_uniform (fun _ _ _ _ higher ⟨reduced,certificate⟩ =>
    ⟨reduced,certificate.monotone higher⟩)
  exact ⟨level,.congrChildren (same := same) (children := children)
    (fun _ _ _ firstAt secondAt => (bounded.at firstAt secondAt).choose_spec)⟩

theorem HeadInspectionReduction.row {program : Program} {context : Context} {left right : Term}
    {equivalent : RowEquivalent left right} :
    HeadInspectionReduction program (DefinitionalReduction.row (context := context) equivalent) :=
  ⟨0,.row (equivalent := equivalent)⟩

/-- The weak origin interface is a forgetful consumer of full finite
inspection, not another origin extraction or a second source minimum. -/
theorem InfersHeadArgument.inspected_origin {program : Program} {context : Context}
    {implementation : ImplDefinition} {arguments : List Term} {binder : Binder} {value : Term}
    (inferred : InfersHeadArgument program context implementation arguments binder value) :
    HeadInspectionOrigin program implementation binder := by
  obtain ⟨level,certificate⟩ := inferred.full_inspected_origin
  exact ⟨level,certificate.erase⟩

/-- Source admission already supplies all finite origins needed by this
well-founded inspection certificate, at the implementation's exact context. -/
theorem ProgramWellFormed.implementation_inspected {program : Program} (valid : ProgramWellFormed program)
    {implementation : ImplDefinition} (declared : Definition.implementation implementation ∈ program.declarations) :
    ImplementationInspected program implementation :=
  .inspected (fun binder present => (valid.implementation_head_determined declared binder present).full_inspected_origin)

theorem HeadInspectionOrigin.source_exposure {program : Program} {implementation : ImplDefinition} {binder : Binder}
    (origin : HeadInspectionOrigin program implementation binder) :
    ∃ (index : Nat) (template expanded : Term)
      (reduced : DefinitionalReduction program implementation.context template expanded),
      implementation.arguments[index]? = some template ∧ HeadInspectionReduction program reduced ∧
        StructuralHeadOrigin binder expanded expanded (.parameter binder.id binder.kind) := by
  obtain ⟨level,certificate⟩ := origin
  cases certificate with
  | exposed sourceAt inspected path => exact ⟨_,_,_,_,sourceAt,⟨level,inspected⟩,path⟩

/-- The actual source exposure comes from the unique full whole-head
minimum. All query conversions used inside its source roots remain present. -/
theorem ImplementationInspected.minimum_full_source_exposure {program : Program} {implementation : ImplDefinition}
    (inspected : ImplementationInspected program implementation) {binder : Binder} (member : binder ∈ implementation.generics) :
    ∃ (index : Nat) (template expanded : Term)
      (reduced : DefinitionalReduction program implementation.context template expanded),
      implementation.arguments[index]? = some template ∧ FullHeadInspectionReductionAt program inspected.level reduced ∧
        StructuralHeadOrigin binder expanded expanded (.parameter binder.id binder.kind) := by
  cases inspected.full_minimum with
  | inspected origins =>
    cases origins binder member with
    | exposed sourceAt certificate path => exact ⟨_,_,_,_,sourceAt,certificate,path⟩

theorem ImplementationInspected.minimum_source_exposure {program : Program} {implementation : ImplDefinition}
    (inspected : ImplementationInspected program implementation) {binder : Binder} (member : binder ∈ implementation.generics) :
    ∃ (index : Nat) (template expanded : Term)
      (reduced : DefinitionalReduction program implementation.context template expanded),
      implementation.arguments[index]? = some template ∧ HeadInspectionReductionAt program inspected.level reduced ∧
        StructuralHeadOrigin binder expanded expanded (.parameter binder.id binder.kind) := by
  obtain ⟨index,template,expanded,reduced,sourceAt,certificate,path⟩ := inspected.minimum_full_source_exposure member
  exact ⟨index,template,expanded,reduced,sourceAt,certificate.erase,path⟩

theorem ImplementationInspected.source_exposure {program : Program} {implementation : ImplDefinition}
    (inspected : ImplementationInspected program implementation) {binder : Binder} (member : binder ∈ implementation.generics) :
    ∃ (index : Nat) (template expanded : Term)
      (reduced : DefinitionalReduction program implementation.context template expanded),
      implementation.arguments[index]? = some template ∧ HeadInspectionReduction program reduced ∧
        StructuralHeadOrigin binder expanded expanded (.parameter binder.id binder.kind) := by
  obtain ⟨index,template,expanded,reduced,sourceAt,certificate,path⟩ := inspected.minimum_source_exposure member
  exact ⟨index,template,expanded,reduced,sourceAt,⟨inspected.level,certificate⟩,path⟩

end Glorious.Language
