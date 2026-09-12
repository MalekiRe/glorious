import GloriousLanguage.HeadOriginDecomposition

/-! A well-founded source-inspection certificate derived from the existing
finite origin judgments. Every annotated edge has genuine positive evidence;
this does not produce a second source matcher. Query conversions and logical
requirements do not become source-inspection dependencies. Every recursive
inspection is justified by an actual selected origin. -/
namespace Glorious.Language

mutual
  /-- Each generic has one actual source exposure. The projection steps in
  these exposures recursively carry inspected implementation evidence. -/
  inductive ImplementationInspectionAt (program : Program) : Nat → ImplDefinition → Prop where
    | inspected {level implementation} :
        (∀ binder ∈ implementation.generics, HeadInspectionOriginAt program level implementation binder) →
        ImplementationInspectionAt program level implementation

  /-- One source exposure retains its exact head position and positive proof.
  This constructor keeps recursive occurrences explicit at their indices. -/
  inductive HeadInspectionOriginAt (program : Program) : Nat → ImplDefinition → Binder → Prop where
    | exposed {level implementation binder} {index : Nat} {template expanded : Term}
        {reduced : DefinitionalReduction program implementation.context template expanded} :
        implementation.arguments[index]? = some template → HeadInspectionReductionAt program level reduced →
        StructuralHeadOrigin binder expanded expanded (.parameter binder.id binder.kind) →
        HeadInspectionOriginAt program level implementation binder

  /-- This certificate retains a genuine root-step proof. Only the chosen
  implementation's source inspections are recursive dependencies. -/
  inductive HeadInspectionStepAt (program : Program) :
      Nat → {context : Context} → {left right : Term} → DefinitionalStep program context left right → Prop where
    | alias {level context id declaration arguments substitution value}
        {found : program.alias id = some declaration}
        {instantiated : Instantiates declaration.generics arguments substitution}
        {kinded : ∀ argument ∈ arguments, Kinding program context argument argument.kind}
        {substituted : Substitutes substitution declaration.value value} :
        HeadInspectionStepAt program level (.alias found instantiated kinded substituted)
    | projection {level bound context trait member owners items associated ownerSub itemSub implementation implSub body value}
        {domain : ProjectionDomain program context trait member owners items associated ownerSub itemSub}
        {selected : SelectsImpl program context trait owners false implementation implSub}
        {present : (member,body) ∈ implementation.associated}
        {substituted : Substitutes (implSub ++ itemSub) body value} :
        ImplementationInspectionAt program level implementation → level < bound →
        HeadInspectionStepAt program bound (.projection domain selected present substituted)
    | defaultProjection {level bound context trait member owners items associated ownerSub itemSub implementation implSub body value}
        {domain : ProjectionDomain program context trait member owners items associated ownerSub itemSub}
        {selected : SelectsImpl program context trait owners false implementation implSub}
        {absent : ∀ body, (member,body) ∉ implementation.associated}
        {default : associated.defaultValue = some body}
        {substituted : Substitutes (ownerSub ++ itemSub) body value} :
        ImplementationInspectionAt program level implementation → level < bound →
        HeadInspectionStepAt program bound (.defaultProjection domain selected absent default substituted)

  /-- A source-inspection certificate includes an authoritative positive
  reduction and actual ordered child proofs. Proof irrelevance does not make
  this a syntactic trace or assign a size to an arbitrary proof term. -/
  inductive HeadInspectionReductionAt (program : Program) :
      Nat → {context : Context} → {left right : Term} → DefinitionalReduction program context left right → Prop where
    | refl {level context term} : HeadInspectionReductionAt program level (DefinitionalReduction.refl (context := context) (term := term))
    | step {level context left right} {stepped : DefinitionalStep program context left right} :
        HeadInspectionStepAt program level stepped → HeadInspectionReductionAt program level (.step stepped)
    | trans {level context left middle right}
        {first : DefinitionalReduction program context left middle}
        {second : DefinitionalReduction program context middle right} :
        HeadInspectionReductionAt program level first → HeadInspectionReductionAt program level second →
        HeadInspectionReductionAt program level (.trans first second)
    | congrChildren {level context left right} {same : SameHead left right}
        {children : ∀ (index : Nat) first second, left.children[index]? = some first → right.children[index]? = some second →
          DefinitionalReduction program context first second} :
        (∀ (index : Nat) first second leftAt rightAt,
          HeadInspectionReductionAt program level (children index first second leftAt rightAt)) →
        HeadInspectionReductionAt program level (.congrChildren same children)
    | row {level context left right} {equivalent : RowEquivalent left right} :
        HeadInspectionReductionAt program level (DefinitionalReduction.row (context := context) equivalent)
end

def ImplementationInspected (program : Program) (implementation : ImplDefinition) : Prop :=
  ∃ level, ImplementationInspectionAt program level implementation

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

theorem ImplementationInspected.minimum {program : Program} {implementation : ImplDefinition}
    (inspected : ImplementationInspected program implementation) :
    ImplementationInspectionAt program inspected.level implementation := by
  classical
  exact (Classical.choose_spec (exists_least_nat inspected)).1

theorem ImplementationInspected.level_le {program : Program} {implementation : ImplDefinition}
    (inspected : ImplementationInspected program implementation) {level : Nat}
    (certificate : ImplementationInspectionAt program level implementation) : inspected.level ≤ level := by
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
    (child : ImplementationInspectionAt program level first) (lower : level < parent.level) :
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

private theorem List.exists_uniform_bound {α : Type} (values : List α) (predicate : α → Nat → Prop)
    (monotone : ∀ value first second, first ≤ second → predicate value first → predicate value second)
    (each : ∀ value ∈ values, ∃ level, predicate value level) :
    ∃ bound, ∀ value ∈ values, predicate value bound := by
  induction values with
  | nil => exact ⟨0,fun _ present => False.elim (List.not_mem_nil present)⟩
  | cons value rest ih =>
    obtain ⟨first,head⟩ := each value List.mem_cons_self
    obtain ⟨second,tail⟩ := ih (fun value present => each value (List.mem_cons_of_mem _ present))
    refine ⟨max first second,?_⟩
    intro actual present
    rcases List.mem_cons.mp present with rfl | inside
    · exact monotone _ first _ (Nat.le_max_left _ _) head
    · exact monotone actual second _ (Nat.le_max_right _ _) (tail actual inside)

theorem ImplementationInspected.inspected {program : Program} {implementation : ImplDefinition}
    (origins : ∀ binder ∈ implementation.generics, HeadInspectionOrigin program implementation binder) :
    ImplementationInspected program implementation := by
  obtain ⟨level,inspected⟩ := List.exists_uniform_bound implementation.generics
    (fun binder level => HeadInspectionOriginAt program level implementation binder)
    (fun _ _ _ higher origin => origin.monotone higher) origins
  exact ⟨level,.inspected inspected⟩

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
    (substituted := substituted) certificate (Nat.lt_succ_self _)⟩

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
    (default := default) (substituted := substituted) certificate (Nat.lt_succ_self _)⟩

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

theorem HeadInspectionReduction.congrChildren {program : Program} {context : Context} {left right : Term}
    {same : SameHead left right}
    {children : ∀ (index : Nat) first second, left.children[index]? = some first → right.children[index]? = some second →
      DefinitionalReduction program context first second}
    (inspected : ∀ (index : Nat) first second leftAt rightAt,
      HeadInspectionReduction program (children index first second leftAt rightAt)) :
    HeadInspectionReduction program (.congrChildren same children) := by
  let predicate := fun index level => ∀ first second leftAt rightAt,
    HeadInspectionReductionAt program level (children index first second leftAt rightAt)
  have bounded : ∀ index ∈ List.range left.children.length, ∃ level, predicate index level := by
    intro index _
    cases leftAt : left.children[index]? with
    | none =>
      exact ⟨0,fun _ _ found _ => False.elim (by rw [leftAt] at found; cases found)⟩
    | some first =>
      cases rightAt : right.children[index]? with
      | none =>
        exact ⟨0,fun _ _ _ found => False.elim (by rw [rightAt] at found; cases found)⟩
      | some second =>
        obtain ⟨level,certificate⟩ := inspected index first second leftAt rightAt
        refine ⟨level,?_⟩
        intro actual other firstAt secondAt
        obtain rfl := Option.some.inj (leftAt.symm.trans firstAt)
        obtain rfl := Option.some.inj (rightAt.symm.trans secondAt)
        exact certificate
  obtain ⟨level,certificates⟩ := List.exists_uniform_bound (List.range left.children.length) predicate
    (fun _ _ _ higher all first second leftAt rightAt => (all first second leftAt rightAt).monotone higher) bounded
  exact ⟨level,.congrChildren (same := same) (children := children)
    (fun index first second leftAt rightAt => certificates index
      (List.mem_range.mpr (List.getElem?_eq_some_iff.mp leftAt).1) first second leftAt rightAt)⟩

theorem HeadInspectionReduction.row {program : Program} {context : Context} {left right : Term}
    {equivalent : RowEquivalent left right} :
    HeadInspectionReduction program (DefinitionalReduction.row (context := context) equivalent) :=
  ⟨0,.row (equivalent := equivalent)⟩

private def InspectedReductionBetween (program : Program) (context : Context) (left right : Term) : Prop :=
  ∃ reduced : DefinitionalReduction program context left right, HeadInspectionReduction program reduced

private theorem InspectedReductionBetween.reflexive (program : Program) (context : Context) (term : Term) :
    InspectedReductionBetween program context term term := ⟨.refl,.refl⟩

private theorem InspectedReductionBetween.congr {program : Program} {context : Context} {left right : Term}
    (same : SameHead left right)
    (children : ListRel (InspectedReductionBetween program context) left.children right.children) :
    InspectedReductionBetween program context left right := by
  classical
  let reductions := fun index first second (leftAt : left.children[index]? = some first)
      (rightAt : right.children[index]? = some second) => Classical.choose (children.at leftAt rightAt)
  exact ⟨.congrChildren same reductions,
    .congrChildren (same := same) (children := reductions)
      (fun _ _ _ leftAt rightAt => Classical.choose_spec (children.at leftAt rightAt))⟩

/-- Any actual caller origin supplies a well-founded inspection of its fixed
source head. The caller query and its conversions are not consulted to invent
an exposure; they are discarded only after the actual source edge is retained. -/
theorem InfersHeadArgument.inspected_origin {program : Program} {context : Context}
    {implementation : ImplDefinition} {arguments : List Term} {binder : Binder} {value : Term}
    (inferred : InfersHeadArgument program context implementation arguments binder value) :
    HeadInspectionOrigin program implementation binder := by
  apply InfersHeadArgument.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ implementation _ _ => ImplementationInspected program implementation)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ => True)
    (motive_8 := fun _ _ _ => True)
    (motive_9 := fun _ _ _ _ => True)
    (motive_10 := fun _ _ _ stepped => HeadInspectionStep program stepped)
    (motive_11 := fun _ _ _ _ => True)
    (motive_12 := fun _ _ _ reduced => HeadInspectionReduction program reduced)
    (motive_13 := fun _ implementation _ _ _ => ImplementationInspected program implementation)
    (motive_14 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_15 := fun sourceContext _ binder template _ _ _ =>
      ∃ (expanded : Term) (reduced : DefinitionalReduction program sourceContext template expanded),
        HeadInspectionReduction program reduced ∧
          StructuralHeadOrigin binder expanded expanded (.parameter binder.id binder.kind))
    (motive_16 := fun _ implementation _ binder _ _ => HeadInspectionOrigin program implementation binder)
    <;> try assumption
  all_goals intros
  all_goals try exact True.intro
  case selected _ _ _ _ _ _ _ _ _ _ _ inspected _ => exact inspected
  case alias _ _ _ _ _ _ found instantiated kinded substituted =>
    exact .alias (found := found) (instantiated := instantiated) (kinded := kinded) (substituted := substituted)
  case projection _ _ _ _ _ _ _ _ _ _ _ _ domain selected present substituted _ inspected =>
    exact .projection (domain := domain) (selected := selected) (present := present) (substituted := substituted) inspected
  case defaultProjection _ _ _ _ _ _ _ _ _ _ _ _ domain selected absent default substituted _ inspected =>
    exact .defaultProjection (domain := domain) (selected := selected) (absent := absent)
      (default := default) (substituted := substituted) inspected
  case refl => exact .refl
  case step _ _ _ stepped inspected => exact .step (stepped := stepped) inspected
  case trans _ _ _ _ first second firstInspected secondInspected =>
    exact .trans (first := first) (second := second) firstInspected secondInspected
  case congrChildren _ _ _ same children inspected => exact .congrChildren (same := same) (children := children) inspected
  case row _ _ _ equivalent => exact .row (equivalent := equivalent)
  case inferred _ implementation _ values _ _ instantiated _ _ _ _ _ _ origins =>
    apply ImplementationInspected.inspected
    intro binder member
    obtain ⟨index,binderAt⟩ := List.mem_iff_getElem?.mp member
    cases valueAt : values[index]? with
    | none =>
      have firstBound := (List.getElem?_eq_some_iff.mp binderAt).1
      have secondBound := List.getElem?_eq_none_iff.mp valueAt
      have lengths := instantiated.2.1.length_eq
      omega
    | some value => exact origins index binder value binderAt valueAt
  case parameter => exact ⟨_,.refl,.refl,.parameter rfl⟩
  case child _ sourceContext _ template _ _ _ _ _ structural _ sourceAt _ _ ih =>
    obtain ⟨expanded,reduced,inspected,path⟩ := ih
    obtain ⟨rebuilt,same,rebuiltAt,reduction,certificate⟩ := Term.child_related
      (relation := InspectedReductionBetween program sourceContext)
      (InspectedReductionBetween.reflexive program sourceContext)
      InspectedReductionBetween.congr sourceAt ⟨reduced,inspected⟩
    exact ⟨rebuilt,reduction,certificate,
      .child (same.structuralHead_iff.mp structural) rfl rebuiltAt rebuiltAt path⟩
  case sourceReduction _ _ _ _ _ _ _ reduced _ inspected ih =>
    obtain ⟨expanded,later,laterInspected,path⟩ := ih
    exact ⟨expanded,reduced.trans later,.trans inspected laterInspected,path⟩
  case queryConversion _ _ _ _ _ _ _ _ _ _ ih => exact ih
  case argument _ _ _ _ _ _ _ _ sourceAt _ _ ih =>
    obtain ⟨expanded,reduced,inspected,path⟩ := ih
    exact .exposed (reduced := reduced) sourceAt inspected path

/-- Source admission already supplies all finite origins needed by this
well-founded inspection certificate, at the implementation's exact context. -/
theorem ProgramWellFormed.implementation_inspected {program : Program} (valid : ProgramWellFormed program)
    {implementation : ImplDefinition} (declared : Definition.implementation implementation ∈ program.declarations) :
    ImplementationInspected program implementation :=
  .inspected (fun binder present => (valid.implementation_head_determined declared binder present).inspected_origin)

theorem HeadInspectionOrigin.source_exposure {program : Program} {implementation : ImplDefinition} {binder : Binder}
    (origin : HeadInspectionOrigin program implementation binder) :
    ∃ (index : Nat) (template expanded : Term)
      (reduced : DefinitionalReduction program implementation.context template expanded),
      implementation.arguments[index]? = some template ∧ HeadInspectionReduction program reduced ∧
        StructuralHeadOrigin binder expanded expanded (.parameter binder.id binder.kind) := by
  obtain ⟨level,certificate⟩ := origin
  cases certificate with
  | exposed sourceAt inspected path => exact ⟨_,_,_,_,sourceAt,⟨level,inspected⟩,path⟩

/-- These exposures come from the exact minimum whole-head certificate.
Every projection certificate encountered inside them therefore carries an
implementation whose own minimum is strictly earlier by `precedes_of_lower`. -/
theorem ImplementationInspected.minimum_source_exposure {program : Program} {implementation : ImplDefinition}
    (inspected : ImplementationInspected program implementation) {binder : Binder} (member : binder ∈ implementation.generics) :
    ∃ (index : Nat) (template expanded : Term)
      (reduced : DefinitionalReduction program implementation.context template expanded),
      implementation.arguments[index]? = some template ∧ HeadInspectionReductionAt program inspected.level reduced ∧
        StructuralHeadOrigin binder expanded expanded (.parameter binder.id binder.kind) := by
  cases inspected.minimum with
  | inspected origins =>
    cases origins binder member with
    | exposed sourceAt certificate path => exact ⟨_,_,_,_,sourceAt,certificate,path⟩

theorem ImplementationInspected.source_exposure {program : Program} {implementation : ImplDefinition}
    (inspected : ImplementationInspected program implementation) {binder : Binder} (member : binder ∈ implementation.generics) :
    ∃ (index : Nat) (template expanded : Term)
      (reduced : DefinitionalReduction program implementation.context template expanded),
      implementation.arguments[index]? = some template ∧ HeadInspectionReduction program reduced ∧
        StructuralHeadOrigin binder expanded expanded (.parameter binder.id binder.kind) := by
  obtain ⟨index,template,expanded,reduced,sourceAt,certificate,path⟩ := inspected.minimum_source_exposure member
  exact ⟨index,template,expanded,reduced,sourceAt,⟨inspected.level,certificate⟩,path⟩

end Glorious.Language
