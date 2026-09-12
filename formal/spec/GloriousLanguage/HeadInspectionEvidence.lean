import GloriousLanguage.HeadOriginDecomposition

/-! Inspectable finite source evidence. Weak certificates retain only source
inspection dependencies and deliberately permit unbounded query conversion.
Full certificates additionally retain the actual finite head-query conversions;
the authoritative source-inspection minimum is taken only over the full form. -/
namespace Glorious.Language

/-- One bound suffices for a finite ordered family of monotone witnesses. -/
theorem ListRel.exists_uniform {α β : Type} {relation : Nat → α → β → Prop} {left : List α} {right : List β}
    (monotone : ∀ first second a b, first ≤ second → relation first a b → relation second a b)
    (related : ListRel (fun a b => ∃ level, relation level a b) left right) :
    ∃ bound, ListRel (relation bound) left right := by
  induction related with
  | nil => exact ⟨0,.nil⟩
  | cons head _ tail =>
    obtain ⟨first,head⟩ := head
    obtain ⟨second,tail⟩ := tail
    exact ⟨max first second,.cons (monotone first _ _ _ (Nat.le_max_left _ _) head)
      (tail.imp (fun _ _ item => monotone second _ _ _ (Nat.le_max_right _ _) item))⟩

mutual
  inductive ImplementationInspectionAt (program : Program) : Nat → ImplDefinition → Prop where
    | inspected {level implementation} :
        (∀ binder ∈ implementation.generics, HeadInspectionOriginAt program level implementation binder) →
        ImplementationInspectionAt program level implementation

  inductive HeadInspectionOriginAt (program : Program) : Nat → ImplDefinition → Binder → Prop where
    | exposed {level implementation binder} {index : Nat} {template expanded : Term}
        {reduced : DefinitionalReduction program implementation.context template expanded} :
        implementation.arguments[index]? = some template → HeadInspectionReductionAt program level reduced →
        StructuralHeadOrigin binder expanded expanded (.parameter binder.id binder.kind) →
        HeadInspectionOriginAt program level implementation binder

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

mutual
  inductive FullImplementationInspectionAt (program : Program) : Nat → ImplDefinition → Prop where
    | inspected {level implementation} :
        (∀ binder ∈ implementation.generics, FullHeadInspectionOriginAt program level implementation binder) →
        FullImplementationInspectionAt program level implementation

  inductive FullHeadInspectionOriginAt (program : Program) : Nat → ImplDefinition → Binder → Prop where
    | exposed {level implementation binder} {index : Nat} {template expanded : Term}
        {reduced : DefinitionalReduction program implementation.context template expanded} :
        implementation.arguments[index]? = some template → FullHeadInspectionReductionAt program level reduced →
        StructuralHeadOrigin binder expanded expanded (.parameter binder.id binder.kind) →
        FullHeadInspectionOriginAt program level implementation binder

  inductive FullHeadInspectionStepAt (program : Program) :
      Nat → {context : Context} → {left right : Term} → DefinitionalStep program context left right → Prop where
    | alias {level context id declaration arguments substitution value}
        {found : program.alias id = some declaration}
        {instantiated : Instantiates declaration.generics arguments substitution}
        {kinded : ∀ argument ∈ arguments, Kinding program context argument argument.kind}
        {substituted : Substitutes substitution declaration.value value} :
        FullHeadInspectionStepAt program level (.alias found instantiated kinded substituted)
    | projection {level bound context trait member owners items associated ownerSub itemSub implementation implSub body value}
        {domain : ProjectionDomain program context trait member owners items associated ownerSub itemSub}
        {selected : SelectsImpl program context trait owners false implementation implSub}
        {present : (member,body) ∈ implementation.associated}
        {substituted : Substitutes (implSub ++ itemSub) body value}
        {query : ∀ (index : Nat) first second,
          (implementation.arguments.map (Term.substitute implSub))[index]? = some first → owners[index]? = some second →
          DefinitionallyEqual program context first second} :
        FullImplementationInspectionAt program level implementation → level < bound →
        (∀ (index : Nat) first second firstAt secondAt,
          FullHeadInspectionEqualityAt program bound (query index first second firstAt secondAt)) →
        FullHeadInspectionStepAt program bound (.projection domain selected present substituted)
    | defaultProjection {level bound context trait member owners items associated ownerSub itemSub implementation implSub body value}
        {domain : ProjectionDomain program context trait member owners items associated ownerSub itemSub}
        {selected : SelectsImpl program context trait owners false implementation implSub}
        {absent : ∀ body, (member,body) ∉ implementation.associated}
        {default : associated.defaultValue = some body}
        {substituted : Substitutes (ownerSub ++ itemSub) body value}
        {query : ∀ (index : Nat) first second,
          (implementation.arguments.map (Term.substitute implSub))[index]? = some first → owners[index]? = some second →
          DefinitionallyEqual program context first second} :
        FullImplementationInspectionAt program level implementation → level < bound →
        (∀ (index : Nat) first second firstAt secondAt,
          FullHeadInspectionEqualityAt program bound (query index first second firstAt secondAt)) →
        FullHeadInspectionStepAt program bound (.defaultProjection domain selected absent default substituted)

  inductive FullHeadInspectionEqualityAt (program : Program) :
      Nat → {context : Context} → {left right : Term} → DefinitionallyEqual program context left right → Prop where
    | refl {level context term} :
        FullHeadInspectionEqualityAt program level (DefinitionallyEqual.refl (context := context) (term := term))
    | symm {level context left right} {equal : DefinitionallyEqual program context left right} :
        FullHeadInspectionEqualityAt program level equal → FullHeadInspectionEqualityAt program level (.symm equal)
    | trans {level context left middle right}
        {first : DefinitionallyEqual program context left middle} {second : DefinitionallyEqual program context middle right} :
        FullHeadInspectionEqualityAt program level first → FullHeadInspectionEqualityAt program level second →
        FullHeadInspectionEqualityAt program level (.trans first second)
    | congrChildren {level context left right} {same : SameHead left right}
        {children : ∀ (index : Nat) first second, left.children[index]? = some first → right.children[index]? = some second →
          DefinitionallyEqual program context first second} :
        (∀ (index : Nat) first second leftAt rightAt,
          FullHeadInspectionEqualityAt program level (children index first second leftAt rightAt)) →
        FullHeadInspectionEqualityAt program level (.congrChildren same children)
    | step {level context left right} {stepped : DefinitionalStep program context left right} :
        FullHeadInspectionStepAt program level stepped → FullHeadInspectionEqualityAt program level (.step stepped)
    | row {level context left right} {equivalent : RowEquivalent left right} :
        FullHeadInspectionEqualityAt program level (DefinitionallyEqual.row (context := context) equivalent)

  inductive FullHeadInspectionReductionAt (program : Program) :
      Nat → {context : Context} → {left right : Term} → DefinitionalReduction program context left right → Prop where
    | refl {level context term} :
        FullHeadInspectionReductionAt program level (DefinitionalReduction.refl (context := context) (term := term))
    | step {level context left right} {stepped : DefinitionalStep program context left right} :
        FullHeadInspectionStepAt program level stepped → FullHeadInspectionReductionAt program level (.step stepped)
    | trans {level context left middle right}
        {first : DefinitionalReduction program context left middle} {second : DefinitionalReduction program context middle right} :
        FullHeadInspectionReductionAt program level first → FullHeadInspectionReductionAt program level second →
        FullHeadInspectionReductionAt program level (.trans first second)
    | congrChildren {level context left right} {same : SameHead left right}
        {children : ∀ (index : Nat) first second, left.children[index]? = some first → right.children[index]? = some second →
          DefinitionalReduction program context first second} :
        (∀ (index : Nat) first second leftAt rightAt,
          FullHeadInspectionReductionAt program level (children index first second leftAt rightAt)) →
        FullHeadInspectionReductionAt program level (.congrChildren same children)
    | row {level context left right} {equivalent : RowEquivalent left right} :
        FullHeadInspectionReductionAt program level (DefinitionalReduction.row (context := context) equivalent)
end

theorem FullHeadInspectionReductionAt.erase {program : Program} {level : Nat} {context : Context} {left right : Term}
    {reduced : DefinitionalReduction program context left right} (certificate : FullHeadInspectionReductionAt program level reduced) :
    HeadInspectionReductionAt program level reduced := by
  apply FullHeadInspectionReductionAt.rec
    (motive_1 := fun level implementation _ => ImplementationInspectionAt program level implementation)
    (motive_2 := fun level implementation binder _ => HeadInspectionOriginAt program level implementation binder)
    (motive_3 := fun level _ _ _ stepped _ => HeadInspectionStepAt program level stepped)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun level _ _ _ reduced _ => HeadInspectionReductionAt program level reduced)
    <;> try assumption
  all_goals intros
  all_goals try exact True.intro
  case inspected _ _ _ origins => exact .inspected origins
  case exposed _ _ _ _ _ _ reduced sourceAt _ path reducedIH => exact .exposed (reduced := reduced) sourceAt reducedIH path
  case alias =>
    exact .alias (found := by assumption) (instantiated := by assumption) (kinded := by assumption) (substituted := by assumption)
  case projection =>
    exact .projection (domain := by assumption) (selected := by assumption) (present := by assumption)
      (substituted := by assumption) (by assumption) (by assumption)
  case defaultProjection =>
    exact .defaultProjection (domain := by assumption) (selected := by assumption) (absent := by assumption)
      (default := by assumption) (substituted := by assumption) (by assumption) (by assumption)
  case refl => exact .refl
  case step _ _ _ _ stepped _ root => exact .step (stepped := stepped) root
  case trans _ _ _ _ _ first second _ _ firstIH secondIH => exact .trans (first := first) (second := second) firstIH secondIH
  case congrChildren _ _ _ _ same children _ ih => exact .congrChildren (same := same) (children := children) ih
  case row _ _ _ _ equivalent => exact .row (equivalent := equivalent)

theorem FullHeadInspectionOriginAt.erase {program : Program} {level : Nat} {implementation : ImplDefinition} {binder : Binder}
    (certificate : FullHeadInspectionOriginAt program level implementation binder) :
    HeadInspectionOriginAt program level implementation binder := by
  cases certificate with
  | exposed sourceAt reduced path => exact .exposed (reduced := by assumption) sourceAt reduced.erase path

theorem FullImplementationInspectionAt.erase {program : Program} {level : Nat} {implementation : ImplDefinition}
    (certificate : FullImplementationInspectionAt program level implementation) :
    ImplementationInspectionAt program level implementation := by
  cases certificate with
  | inspected origins => exact .inspected (fun binder member => (origins binder member).erase)

theorem FullHeadInspectionStepAt.erase {program : Program} {level : Nat} {context : Context} {left right : Term}
    {stepped : DefinitionalStep program context left right} (certificate : FullHeadInspectionStepAt program level stepped) :
    HeadInspectionStepAt program level stepped := by
  cases certificate with
  | alias =>
    exact .alias (found := by assumption) (instantiated := by assumption) (kinded := by assumption) (substituted := by assumption)
  | projection lower below _ =>
    exact .projection (domain := by assumption) (selected := by assumption) (present := by assumption)
      (substituted := by assumption) lower.erase below
  | defaultProjection lower below _ =>
    exact .defaultProjection (domain := by assumption) (selected := by assumption) (absent := by assumption)
      (default := by assumption) (substituted := by assumption) lower.erase below

theorem FullHeadInspectionEqualityAt.monotone {program : Program} {level bound : Nat} {context : Context} {left right : Term}
    {equal : DefinitionallyEqual program context left right} (certificate : FullHeadInspectionEqualityAt program level equal)
    (higher : level ≤ bound) : FullHeadInspectionEqualityAt program bound equal := by
  have widen : ∀ bound, level ≤ bound → FullHeadInspectionEqualityAt program bound equal := by
    apply FullHeadInspectionEqualityAt.rec
      (motive_1 := fun _ _ _ => True)
      (motive_2 := fun _ _ _ _ => True)
      (motive_3 := fun level _ _ _ stepped _ => ∀ bound, level ≤ bound → FullHeadInspectionStepAt program bound stepped)
      (motive_4 := fun level _ _ _ equal _ => ∀ bound, level ≤ bound → FullHeadInspectionEqualityAt program bound equal)
      (motive_5 := fun _ _ _ _ _ _ => True)
      <;> try assumption
    all_goals intros
    all_goals try exact True.intro
    case alias =>
      exact .alias (found := by assumption) (instantiated := by assumption) (kinded := by assumption) (substituted := by assumption)
    case projection =>
      rename_i actualQuery inspected below _ _ queryIH next higher
      exact FullHeadInspectionStepAt.projection (domain := by assumption) (selected := by assumption)
        (present := by assumption) (substituted := by assumption) (query := actualQuery) inspected
        (Nat.lt_of_lt_of_le below higher)
        (fun index first second firstAt secondAt => queryIH index first second firstAt secondAt next higher)
    case defaultProjection =>
      rename_i actualQuery inspected below _ _ queryIH next higher
      exact FullHeadInspectionStepAt.defaultProjection (domain := by assumption) (selected := by assumption)
        (absent := by assumption) (default := by assumption) (substituted := by assumption) (query := actualQuery) inspected
        (Nat.lt_of_lt_of_le below higher)
        (fun index first second firstAt secondAt => queryIH index first second firstAt secondAt next higher)
    case refl => exact .refl
    case symm _ _ _ _ equal _ ih bound higher => exact .symm (equal := equal) (ih bound higher)
    case trans _ _ _ _ _ first second _ _ firstIH secondIH bound higher =>
      exact .trans (first := first) (second := second) (firstIH bound higher) (secondIH bound higher)
    case congrChildren _ _ _ _ same children _ ih bound higher =>
      exact .congrChildren (same := same) (children := children) (fun index first second firstAt secondAt =>
        ih index first second firstAt secondAt bound higher)
    case step _ _ _ _ stepped _ ih bound higher => exact .step (stepped := stepped) (ih bound higher)
    case row _ _ _ _ equivalent _ _ => exact .row (equivalent := equivalent)
  exact widen bound higher

theorem FullHeadInspectionStepAt.monotone {program : Program} {level bound : Nat} {context : Context} {left right : Term}
    {stepped : DefinitionalStep program context left right} (certificate : FullHeadInspectionStepAt program level stepped)
    (higher : level ≤ bound) : FullHeadInspectionStepAt program bound stepped := by
  cases certificate with
  | alias =>
    exact .alias (found := by assumption) (instantiated := by assumption) (kinded := by assumption) (substituted := by assumption)
  | projection lower below query =>
    exact .projection (domain := by assumption) (selected := by assumption) (present := by assumption)
      (substituted := by assumption) lower (Nat.lt_of_lt_of_le below higher)
      (fun index first second firstAt secondAt => (query index first second firstAt secondAt).monotone higher)
  | defaultProjection lower below query =>
    exact .defaultProjection (domain := by assumption) (selected := by assumption) (absent := by assumption)
      (default := by assumption) (substituted := by assumption) lower (Nat.lt_of_lt_of_le below higher)
      (fun index first second firstAt secondAt => (query index first second firstAt secondAt).monotone higher)

theorem FullHeadInspectionReductionAt.monotone {program : Program} {level bound : Nat} {context : Context} {left right : Term}
    {reduced : DefinitionalReduction program context left right} (certificate : FullHeadInspectionReductionAt program level reduced)
    (higher : level ≤ bound) : FullHeadInspectionReductionAt program bound reduced := by
  have widen : ∀ bound, level ≤ bound → FullHeadInspectionReductionAt program bound reduced := by
    apply FullHeadInspectionReductionAt.rec
      (motive_1 := fun _ _ _ => True)
      (motive_2 := fun _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ => True)
      (motive_5 := fun level _ _ _ reduced _ => ∀ bound, level ≤ bound → FullHeadInspectionReductionAt program bound reduced)
      <;> try assumption
    all_goals intros
    all_goals try exact True.intro
    case refl => exact .refl
    case step _ _ _ _ stepped root _ bound higher => exact .step (stepped := stepped) (root.monotone higher)
    case trans _ _ _ _ _ first second _ _ firstIH secondIH bound higher =>
      exact .trans (first := first) (second := second) (firstIH bound higher) (secondIH bound higher)
    case congrChildren _ _ _ _ same children _ ih bound higher =>
      exact .congrChildren (same := same) (children := children) (fun index first second firstAt secondAt =>
        ih index first second firstAt secondAt bound higher)
    case row _ _ _ _ equivalent _ _ => exact .row (equivalent := equivalent)
  exact widen bound higher

theorem FullHeadInspectionOriginAt.monotone {program : Program} {level bound : Nat} {implementation : ImplDefinition} {binder : Binder}
    (certificate : FullHeadInspectionOriginAt program level implementation binder) (higher : level ≤ bound) :
    FullHeadInspectionOriginAt program bound implementation binder := by
  cases certificate with
  | exposed sourceAt reduced path => exact .exposed (reduced := by assumption) sourceAt (reduced.monotone higher) path

theorem FullImplementationInspectionAt.monotone {program : Program} {level bound : Nat} {implementation : ImplDefinition}
    (certificate : FullImplementationInspectionAt program level implementation) (higher : level ≤ bound) :
    FullImplementationInspectionAt program bound implementation := by
  cases certificate with
  | inspected origins => exact .inspected (fun binder member => (origins binder member).monotone higher)

end Glorious.Language
