import GloriousLanguage.HeadInspectionEvidence

/-! The authoritative full finite inspection extracted from actual static
derivations. Query conversions inside source expansions are retained rather
than silently omitted from the well-founded source dependency. -/
namespace Glorious.Language

def FullImplementationInspected (program : Program) (implementation : ImplDefinition) : Prop :=
  ∃ level, FullImplementationInspectionAt program level implementation

def FullHeadInspectionOrigin (program : Program) (implementation : ImplDefinition) (binder : Binder) : Prop :=
  ∃ level, FullHeadInspectionOriginAt program level implementation binder

def FullHeadInspectionStep (program : Program) {context : Context} {left right : Term}
    (stepped : DefinitionalStep program context left right) : Prop := ∃ level, FullHeadInspectionStepAt program level stepped

def FullHeadInspectionEquality (program : Program) {context : Context} {left right : Term}
    (equal : DefinitionallyEqual program context left right) : Prop := ∃ level, FullHeadInspectionEqualityAt program level equal

def FullHeadInspectionReduction (program : Program) {context : Context} {left right : Term}
    (reduced : DefinitionalReduction program context left right) : Prop := ∃ level, FullHeadInspectionReductionAt program level reduced

private def FullQueryAt (program : Program) (context : Context) (level : Nat) (left right : Term) : Prop :=
  ∃ equal : DefinitionallyEqual program context left right, FullHeadInspectionEqualityAt program level equal

private def FullQuery (program : Program) (context : Context) (left right : Term) : Prop :=
  ∃ equal : DefinitionallyEqual program context left right, FullHeadInspectionEquality program equal

private theorem FullQueryAt.monotone {program : Program} {context : Context} {first second : Nat} {left right : Term}
    (higher : first ≤ second) (query : FullQueryAt program context first left right) : FullQueryAt program context second left right := by
  obtain ⟨equal,certificate⟩ := query
  exact ⟨equal,certificate.monotone higher⟩

private theorem ListRel.full_query_bound {program : Program} {context : Context} {left right : List Term}
    (queries : ListRel (FullQuery program context) left right) :
    ∃ level, ListRel (FullQueryAt program context level) left right := by
  apply ListRel.exists_uniform (fun _ _ _ _ higher query => query.monotone higher)
  exact queries.imp (fun _ _ ⟨equal,level,certificate⟩ => ⟨level,equal,certificate⟩)

theorem FullImplementationInspected.inspected {program : Program} {implementation : ImplDefinition}
    (origins : ∀ binder ∈ implementation.generics, FullHeadInspectionOrigin program implementation binder) :
    FullImplementationInspected program implementation := by
  have paired : ListRel (fun binder (_ : Unit) => ∃ level, FullHeadInspectionOriginAt program level implementation binder)
      implementation.generics (implementation.generics.map (fun _ => ())) := by
    simpa only [List.map_id] using ListRel.maps implementation.generics id (fun _ => ()) origins
  obtain ⟨level,certificates⟩ := paired.exists_uniform (fun _ _ _ _ higher origin => origin.monotone higher)
  exact ⟨level,.inspected (fun binder member => (certificates.member_left member).choose_spec.2)⟩

theorem FullHeadInspectionOrigin.exposed {program : Program} {implementation : ImplDefinition} {binder : Binder}
    {index : Nat} {template expanded : Term} {reduced : DefinitionalReduction program implementation.context template expanded}
    (sourceAt : implementation.arguments[index]? = some template) (inspected : FullHeadInspectionReduction program reduced)
    (path : StructuralHeadOrigin binder expanded expanded (.parameter binder.id binder.kind)) :
    FullHeadInspectionOrigin program implementation binder := by
  obtain ⟨level,certificate⟩ := inspected
  exact ⟨level,.exposed (reduced := reduced) sourceAt certificate path⟩

theorem FullHeadInspectionStep.alias {program : Program} {context : Context} {id : DeclId} {declaration : AliasDefinition}
    {arguments : List Term} {substitution : Substitution} {value : Term}
    {found : program.alias id = some declaration} {instantiated : Instantiates declaration.generics arguments substitution}
    {kinded : ∀ argument ∈ arguments, Kinding program context argument argument.kind}
    {substituted : Substitutes substitution declaration.value value} :
    FullHeadInspectionStep program (.alias found instantiated kinded substituted) :=
  ⟨0,.alias (found := found) (instantiated := instantiated) (kinded := kinded) (substituted := substituted)⟩

private theorem FullHeadInspectionStep.projection {program : Program} {context : Context}
    {trait member : DeclId} {owners items : List Term} {associated : AssociatedDefinition}
    {ownerSub itemSub : Substitution} {implementation : ImplDefinition} {implSub : Substitution} {body value : Term}
    {domain : ProjectionDomain program context trait member owners items associated ownerSub itemSub}
    {selected : SelectsImpl program context trait owners false implementation implSub}
    {present : (member,body) ∈ implementation.associated} {substituted : Substitutes (implSub ++ itemSub) body value}
    (inspected : FullImplementationInspected program implementation)
    (queries : ListRel (FullQuery program context) (implementation.arguments.map (Term.substitute implSub)) owners) :
    FullHeadInspectionStep program (.projection domain selected present substituted) := by
  classical
  obtain ⟨sourceLevel,source⟩ := inspected
  obtain ⟨queryLevel,queries⟩ := queries.full_query_bound
  let bound := max (sourceLevel+1) queryLevel
  have bounded := queries.imp (fun _ _ query => query.monotone (Nat.le_max_right (sourceLevel+1) queryLevel))
  let query := fun index first second (firstAt : (implementation.arguments.map (Term.substitute implSub))[index]? = some first)
      (secondAt : owners[index]? = some second) => Classical.choose (bounded.at firstAt secondAt)
  exact ⟨bound,.projection (domain := domain) (selected := selected) (present := present) (substituted := substituted)
    (query := query) source (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _))
    (fun _ _ _ firstAt secondAt => Classical.choose_spec (bounded.at firstAt secondAt))⟩

private theorem FullHeadInspectionStep.defaultProjection {program : Program} {context : Context}
    {trait member : DeclId} {owners items : List Term} {associated : AssociatedDefinition}
    {ownerSub itemSub : Substitution} {implementation : ImplDefinition} {implSub : Substitution} {body value : Term}
    {domain : ProjectionDomain program context trait member owners items associated ownerSub itemSub}
    {selected : SelectsImpl program context trait owners false implementation implSub}
    {absent : ∀ body, (member,body) ∉ implementation.associated} {default : associated.defaultValue = some body}
    {substituted : Substitutes (ownerSub ++ itemSub) body value}
    (inspected : FullImplementationInspected program implementation)
    (queries : ListRel (FullQuery program context) (implementation.arguments.map (Term.substitute implSub)) owners) :
    FullHeadInspectionStep program (.defaultProjection domain selected absent default substituted) := by
  classical
  obtain ⟨sourceLevel,source⟩ := inspected
  obtain ⟨queryLevel,queries⟩ := queries.full_query_bound
  let bound := max (sourceLevel+1) queryLevel
  have bounded := queries.imp (fun _ _ query => query.monotone (Nat.le_max_right (sourceLevel+1) queryLevel))
  let query := fun index first second (firstAt : (implementation.arguments.map (Term.substitute implSub))[index]? = some first)
      (secondAt : owners[index]? = some second) => Classical.choose (bounded.at firstAt secondAt)
  exact ⟨bound,.defaultProjection (domain := domain) (selected := selected) (absent := absent) (default := default)
    (substituted := substituted) (query := query) source (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _))
    (fun _ _ _ firstAt secondAt => Classical.choose_spec (bounded.at firstAt secondAt))⟩

theorem FullHeadInspectionEquality.refl {program : Program} {context : Context} {term : Term} :
    FullHeadInspectionEquality program (DefinitionallyEqual.refl (context := context) (term := term)) := ⟨0,.refl⟩

theorem FullHeadInspectionEquality.symm {program : Program} {context : Context} {left right : Term}
    {equal : DefinitionallyEqual program context left right} (certificate : FullHeadInspectionEquality program equal) :
    FullHeadInspectionEquality program (.symm equal) := by
  obtain ⟨level,certificate⟩ := certificate
  exact ⟨level,.symm (equal := equal) certificate⟩

theorem FullHeadInspectionEquality.trans {program : Program} {context : Context} {left middle right : Term}
    {first : DefinitionallyEqual program context left middle} {second : DefinitionallyEqual program context middle right}
    (before : FullHeadInspectionEquality program first) (after : FullHeadInspectionEquality program second) :
    FullHeadInspectionEquality program (.trans first second) := by
  obtain ⟨a,firstCertificate⟩ := before
  obtain ⟨b,secondCertificate⟩ := after
  exact ⟨max a b,.trans (first := first) (second := second)
    (firstCertificate.monotone (Nat.le_max_left _ _)) (secondCertificate.monotone (Nat.le_max_right _ _))⟩

theorem FullHeadInspectionEquality.congrChildren {program : Program} {context : Context} {left right : Term}
    {same : SameHead left right}
    {children : ∀ (index : Nat) first second, left.children[index]? = some first → right.children[index]? = some second →
      DefinitionallyEqual program context first second}
    (certificates : ∀ (index : Nat) first second firstAt secondAt,
      FullHeadInspectionEquality program (children index first second firstAt secondAt)) :
    FullHeadInspectionEquality program (.congrChildren same children) := by
  have queries : ListRel (FullQuery program context) left.children right.children :=
    ListRel.of_at same.children_length (fun index first second firstAt secondAt =>
      ⟨children index first second firstAt secondAt,certificates index first second firstAt secondAt⟩)
  obtain ⟨level,bounded⟩ := queries.full_query_bound
  exact ⟨level,.congrChildren (same := same) (children := children)
    (fun _ _ _ firstAt secondAt => (bounded.at firstAt secondAt).choose_spec)⟩

theorem FullHeadInspectionEquality.step {program : Program} {context : Context} {left right : Term}
    {stepped : DefinitionalStep program context left right} (certificate : FullHeadInspectionStep program stepped) :
    FullHeadInspectionEquality program (.step stepped) := by
  obtain ⟨level,certificate⟩ := certificate
  exact ⟨level,.step (stepped := stepped) certificate⟩

theorem FullHeadInspectionEquality.row {program : Program} {context : Context} {left right : Term}
    {equivalent : RowEquivalent left right} :
    FullHeadInspectionEquality program (DefinitionallyEqual.row (context := context) equivalent) := ⟨0,.row (equivalent := equivalent)⟩

theorem FullHeadInspectionReduction.refl {program : Program} {context : Context} {term : Term} :
    FullHeadInspectionReduction program (DefinitionalReduction.refl (context := context) (term := term)) := ⟨0,.refl⟩

theorem FullHeadInspectionReduction.step {program : Program} {context : Context} {left right : Term}
    {stepped : DefinitionalStep program context left right} (certificate : FullHeadInspectionStep program stepped) :
    FullHeadInspectionReduction program (.step stepped) := by
  obtain ⟨level,certificate⟩ := certificate
  exact ⟨level,.step (stepped := stepped) certificate⟩

theorem FullHeadInspectionReduction.trans {program : Program} {context : Context} {left middle right : Term}
    {first : DefinitionalReduction program context left middle} {second : DefinitionalReduction program context middle right}
    (before : FullHeadInspectionReduction program first) (after : FullHeadInspectionReduction program second) :
    FullHeadInspectionReduction program (.trans first second) := by
  obtain ⟨a,firstCertificate⟩ := before
  obtain ⟨b,secondCertificate⟩ := after
  exact ⟨max a b,.trans (first := first) (second := second)
    (firstCertificate.monotone (Nat.le_max_left _ _)) (secondCertificate.monotone (Nat.le_max_right _ _))⟩

private def FullReducedAt (program : Program) (context : Context) (level : Nat) (left right : Term) : Prop :=
  ∃ reduced : DefinitionalReduction program context left right, FullHeadInspectionReductionAt program level reduced

theorem FullHeadInspectionReduction.congrChildren {program : Program} {context : Context} {left right : Term}
    {same : SameHead left right}
    {children : ∀ (index : Nat) first second, left.children[index]? = some first → right.children[index]? = some second →
      DefinitionalReduction program context first second}
    (certificates : ∀ (index : Nat) first second firstAt secondAt,
      FullHeadInspectionReduction program (children index first second firstAt secondAt)) :
    FullHeadInspectionReduction program (.congrChildren same children) := by
  have pairs : ListRel (fun left right => ∃ level, FullReducedAt program context level left right) left.children right.children :=
    ListRel.of_at same.children_length (fun index first second firstAt secondAt => by
      obtain ⟨level,certificate⟩ := certificates index first second firstAt secondAt
      exact ⟨level,children index first second firstAt secondAt,certificate⟩)
  obtain ⟨level,bounded⟩ := pairs.exists_uniform (fun _ _ _ _ higher ⟨reduced,certificate⟩ =>
    ⟨reduced,certificate.monotone higher⟩)
  exact ⟨level,.congrChildren (same := same) (children := children)
    (fun _ _ _ firstAt secondAt => (bounded.at firstAt secondAt).choose_spec)⟩

theorem FullHeadInspectionReduction.row {program : Program} {context : Context} {left right : Term}
    {equivalent : RowEquivalent left right} :
    FullHeadInspectionReduction program (DefinitionalReduction.row (context := context) equivalent) := ⟨0,.row (equivalent := equivalent)⟩

private def FullInspectedReductionBetween (program : Program) (context : Context) (left right : Term) : Prop :=
  ∃ reduced : DefinitionalReduction program context left right, FullHeadInspectionReduction program reduced

private theorem FullInspectedReductionBetween.reflexive (program : Program) (context : Context) (term : Term) :
    FullInspectedReductionBetween program context term term := ⟨.refl,.refl⟩

private theorem FullInspectedReductionBetween.congr {program : Program} {context : Context} {left right : Term}
    (same : SameHead left right)
    (children : ListRel (FullInspectedReductionBetween program context) left.children right.children) :
    FullInspectedReductionBetween program context left right := by
  classical
  let reductions := fun index first second (leftAt : left.children[index]? = some first)
      (rightAt : right.children[index]? = some second) => Classical.choose (children.at leftAt rightAt)
  exact ⟨.congrChildren same reductions,
    .congrChildren (same := same) (children := reductions)
      (fun _ _ _ leftAt rightAt => Classical.choose_spec (children.at leftAt rightAt))⟩

/-- One mutual extraction consumes the actual finite static derivation.
Every head conversion used by a selected projection is retained alongside its
strictly earlier complete source inspection. No simulation premise is used. -/
theorem DefinitionalReduction.full_inspected {program : Program} {context : Context} {left right : Term}
    (reduced : DefinitionalReduction program context left right) : FullHeadInspectionReduction program reduced := by
  apply DefinitionalReduction.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun context _ arguments _ implementation substitution _ =>
      FullImplementationInspected program implementation ∧
        ListRel (FullQuery program context) (implementation.arguments.map (Term.substitute substitution)) arguments)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ => True)
    (motive_8 := fun _ _ _ => True)
    (motive_9 := fun _ _ _ _ => True)
    (motive_10 := fun _ _ _ stepped => FullHeadInspectionStep program stepped)
    (motive_11 := fun _ _ _ equal => FullHeadInspectionEquality program equal)
    (motive_12 := fun _ _ _ reduced => FullHeadInspectionReduction program reduced)
    (motive_13 := fun context implementation arguments substitution _ =>
      FullImplementationInspected program implementation ∧
        ListRel (FullQuery program context) (implementation.arguments.map (Term.substitute substitution)) arguments)
    (motive_14 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_15 := fun sourceContext _ binder template _ _ _ =>
      ∃ (expanded : Term) (reduced : DefinitionalReduction program sourceContext template expanded),
        FullHeadInspectionReduction program reduced ∧
          StructuralHeadOrigin binder expanded expanded (.parameter binder.id binder.kind))
    (motive_16 := fun _ implementation _ binder _ _ => FullHeadInspectionOrigin program implementation binder)
    <;> try assumption
  all_goals intros
  all_goals try exact True.intro
  all_goals try exact FullHeadInspectionEquality.refl
  all_goals try exact FullHeadInspectionEquality.symm (equal := by assumption) (by assumption)
  all_goals try exact FullHeadInspectionEquality.trans (first := by assumption) (second := by assumption) (by assumption) (by assumption)
  all_goals try exact FullHeadInspectionEquality.congrChildren (same := by assumption) (children := by assumption) (by assumption)
  all_goals try exact FullHeadInspectionEquality.step (stepped := by assumption) (by assumption)
  all_goals try exact FullHeadInspectionEquality.row (equivalent := by assumption)
  all_goals try exact FullHeadInspectionReduction.refl
  all_goals try exact FullHeadInspectionReduction.step (stepped := by assumption) (by assumption)
  all_goals try exact FullHeadInspectionReduction.trans (first := by assumption) (second := by assumption) (by assumption) (by assumption)
  all_goals try exact FullHeadInspectionReduction.congrChildren (same := by assumption) (children := by assumption) (by assumption)
  all_goals try exact FullHeadInspectionReduction.row (equivalent := by assumption)
  case selected _ _ _ _ _ _ _ _ _ _ _ inspected _ => exact inspected
  case alias _ _ _ _ _ _ found instantiated kinded substituted =>
    exact .alias (found := found) (instantiated := instantiated) (kinded := kinded) (substituted := substituted)
  case projection _ _ _ _ _ _ _ _ _ _ _ _ domain selected present substituted _ inspected =>
    exact FullHeadInspectionStep.projection (domain := domain) (selected := selected) (present := present)
      (substituted := substituted) inspected.1 inspected.2
  case defaultProjection _ _ _ _ _ _ _ _ _ _ _ _ domain selected absent default substituted _ inspected =>
    exact FullHeadInspectionStep.defaultProjection (domain := domain) (selected := selected) (absent := absent)
      (default := default) (substituted := substituted) inspected.1 inspected.2
  case inferred _ implementation _ values substitution specialized instantiated _ graph lengths head _ headIH origins =>
    constructor
    · apply FullImplementationInspected.inspected
      intro binder member
      obtain ⟨index,binderAt⟩ := List.mem_iff_getElem?.mp member
      cases valueAt : values[index]? with
      | none =>
        have firstBound := (List.getElem?_eq_some_iff.mp binderAt).1
        have secondBound := List.getElem?_eq_none_iff.mp valueAt
        have lengths := instantiated.2.1.length_eq
        omega
      | some value => exact origins index binder value binderAt valueAt
    · have mapped : ListRel (fun template value => value = template.substitute substitution)
          implementation.arguments (implementation.arguments.map (Term.substitute substitution)) := by
        simpa only [List.map_id] using ListRel.maps implementation.arguments id (Term.substitute substitution) (fun _ _ => rfl)
      have same := ListRel.functional (fun _ _ _ first second => first.trans second.symm)
        (graph.imp (fun _ _ graph => graph.2.1)) mapped
      rw [← same]
      exact ListRel.of_at lengths (fun index first second firstAt secondAt =>
        ⟨head index first second firstAt secondAt,headIH index first second firstAt secondAt⟩)
  case parameter => exact ⟨_,.refl,.refl,.parameter rfl⟩
  case child _ sourceContext _ template _ _ _ _ _ structural _ sourceAt _ _ ih =>
    obtain ⟨expanded,reduced,inspected,path⟩ := ih
    obtain ⟨rebuilt,same,rebuiltAt,reduction,certificate⟩ := Term.child_related
      (relation := FullInspectedReductionBetween program sourceContext)
      (FullInspectedReductionBetween.reflexive program sourceContext)
      FullInspectedReductionBetween.congr sourceAt ⟨reduced,inspected⟩
    exact ⟨rebuilt,reduction,certificate,
      .child (same.structuralHead_iff.mp structural) rfl rebuiltAt rebuiltAt path⟩
  case sourceReduction _ _ _ _ _ _ _ reduced _ inspected ih =>
    obtain ⟨expanded,later,laterInspected,path⟩ := ih
    exact ⟨expanded,reduced.trans later,.trans inspected laterInspected,path⟩
  case queryConversion _ _ _ _ _ _ _ _ _ _ ih => exact ih
  case argument _ _ _ _ _ _ _ _ sourceAt _ _ ih =>
    obtain ⟨expanded,reduced,inspected,path⟩ := ih
    exact .exposed (reduced := reduced) sourceAt inspected path

theorem FullHeadInspectionReductionAt.equal {program : Program} {level : Nat} {context : Context} {left right : Term}
    {reduced : DefinitionalReduction program context left right} (certificate : FullHeadInspectionReductionAt program level reduced) :
    FullHeadInspectionEqualityAt program level reduced.equal := by
  apply FullHeadInspectionReductionAt.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun level _ _ _ reduced _ => FullHeadInspectionEqualityAt program level reduced.equal)
    <;> try assumption
  all_goals intros
  all_goals try exact True.intro
  case refl => exact .refl
  case step _ _ _ _ stepped root _ => exact .step (stepped := stepped) root
  case trans _ _ _ _ _ first second _ _ firstIH secondIH =>
    exact .trans (first := first.equal) (second := second.equal) firstIH secondIH
  case congrChildren _ _ _ _ same children _ ih =>
    exact .congrChildren (same := same) (children := fun index first second firstAt secondAt =>
      (children index first second firstAt secondAt).equal) ih
  case row _ _ _ _ equivalent => exact .row (equivalent := equivalent)

/-- Symmetric equality delegates every actual root to the single full static
extraction above; only its six ordinary closure rules are assembled here. -/
theorem DefinitionallyEqual.full_inspected {program : Program} {context : Context} {left right : Term}
    (equal : DefinitionallyEqual program context left right) : FullHeadInspectionEquality program equal := by
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
    (motive_11 := fun _ _ _ equal => FullHeadInspectionEquality program equal)
    (motive_12 := fun _ _ _ _ => True)
    (motive_13 := fun _ _ _ _ _ => True)
    (motive_14 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_15 := fun _ _ _ _ _ _ _ => True)
    (motive_16 := fun _ _ _ _ _ _ => True)
    <;> try assumption
  all_goals intros
  all_goals try exact True.intro
  case refl => exact .refl
  case symm _ _ _ equal certificate => exact .symm (equal := equal) certificate
  case trans _ _ _ _ first second firstIH secondIH => exact .trans (first := first) (second := second) firstIH secondIH
  case congrChildren _ _ _ same children ih => exact .congrChildren (same := same) (children := children) ih
  case step _ _ _ stepped _ =>
    obtain ⟨level,certificate⟩ := (DefinitionalReduction.step stepped).full_inspected
    exact ⟨level,certificate.equal⟩
  case row _ _ _ equivalent => exact .row (equivalent := equivalent)

theorem InfersHeadArgument.full_inspected_origin {program : Program} {context : Context}
    {implementation : ImplDefinition} {arguments : List Term} {binder : Binder} {value : Term}
    (inferred : InfersHeadArgument program context implementation arguments binder value) :
    FullHeadInspectionOrigin program implementation binder := by
  obtain ⟨_,_,_,_,_,sourceAt,_,reduced,_,path⟩ := inferred.decompose
  exact .exposed (reduced := reduced) sourceAt reduced.full_inspected path.source_path

end Glorious.Language
