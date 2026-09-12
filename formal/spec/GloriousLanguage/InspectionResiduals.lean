import GloriousLanguage.HeadInspection

/-! Actual root/child residuals preserve source-inspection dependencies.
Query conversion is permitted by the existing matcher and does not increase
the root's inspection bound. Body reductions retain the children's bound;
neither bound is a claim about arbitrary conversion proof depth. -/
namespace Glorious.Language

/-- Any root at the converted query uses the same selected declaration.
Only that identity consequence of coherence is needed to carry the existing
strict source-inspection dependency into the residual. -/
theorem HeadInspectionStepAt.children_invariant {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {term value changed result : Term}
    {stepped : DefinitionalStep program context term value} {level : Nat}
    (certificate : HeadInspectionStepAt program level stepped)
    (same : SameHead term changed)
    (children : ListRel (DefinitionallyEqual program context) term.children changed.children)
    (next : DefinitionalStep program context changed result) :
    HeadInspectionStepAt program level next := by
  cases certificate <;> cases next <;> simp_all [SameHead,Term.mapChildren]
  all_goals simp only [Term.children] at children
  case alias.alias =>
    exact .alias (found := by assumption) (instantiated := by assumption)
      (kinded := by assumption) (substituted := by assumption)
  all_goals
    have split := children.split_append (by simpa using congrArg List.length same.2.2.1)
    have identity := (SelectsImpl.convertible_unique valid (by assumption) (by assumption) split.1).1
    cases identity
  case projection.projection =>
    exact .projection (domain := by assumption) (selected := by assumption)
      (present := by assumption) (substituted := by assumption) (by assumption) (by assumption)
  case projection.defaultProjection =>
    exact .defaultProjection (domain := by assumption) (selected := by assumption)
      (absent := by assumption) (default := by assumption) (substituted := by assumption) (by assumption) (by assumption)
  case defaultProjection.projection =>
    exact .projection (domain := by assumption) (selected := by assumption)
      (present := by assumption) (substituted := by assumption) (by assumption) (by assumption)
  case defaultProjection.defaultProjection =>
    exact .defaultProjection (domain := by assumption) (selected := by assumption)
      (absent := by assumption) (default := by assumption) (substituted := by assumption) (by assumption) (by assumption)

theorem HeadInspectionStepAt.children_relation {program : Program} (valid : ProgramWellFormed program)
    {relation : Term → Term → Prop} {context : Context} {term value changed : Term}
    {stepped : DefinitionalStep program context term value} {level : Nat}
    (certificate : HeadInspectionStepAt program level stepped)
    (reflexive : ∀ term, relation term term)
    (converts : ∀ left right, relation left right → DefinitionallyEqual program context left right)
    (substitutionPreserves : ∀ (term : Term) (left right : Substitution),
      (∀ id kind, relation ((left.get id).getD (.parameter id kind))
        ((right.get id).getD (.parameter id kind))) → relation (term.substitute left) (term.substitute right))
    (same : SameHead term changed) (children : ListRel relation term.children changed.children) :
    ∃ newValue, (∃ residual : DefinitionalStep program context changed newValue,
      HeadInspectionStepAt program level residual) ∧ relation value newValue := by
  obtain ⟨newValue,residual,related⟩ := stepped.children_relation valid reflexive converts substitutionPreserves same children
  exact ⟨newValue,⟨residual,certificate.children_invariant valid same (children.imp converts) residual⟩,related⟩

private def InspectedReduction (program : Program) (context : Context) (level : Nat) (left right : Term) : Prop :=
  ∃ reduced : DefinitionalReduction program context left right, HeadInspectionReductionAt program level reduced

private theorem InspectedReduction.reflexive (program : Program) (context : Context) (level : Nat) (term : Term) :
    InspectedReduction program context level term term := ⟨.refl,.refl⟩

private theorem InspectedReduction.congr {program : Program} {context : Context} {level : Nat} {left right : Term}
    (same : SameHead left right)
    (children : ListRel (InspectedReduction program context level) left.children right.children) :
    InspectedReduction program context level left right := by
  classical
  let reductions := fun index first second (leftAt : left.children[index]? = some first)
      (rightAt : right.children[index]? = some second) => Classical.choose (children.at leftAt rightAt)
  exact ⟨.congrChildren same reductions,.congrChildren (same := same) (children := reductions)
    (fun _ _ _ leftAt rightAt => Classical.choose_spec (children.at leftAt rightAt))⟩

/-- Syntactic substitution transports the actual inspected child reductions
without introducing a new declared root expansion. -/
private theorem Term.substitutions_inspected (program : Program) (context : Context) (level : Nat) (term : Term)
    {left right : Substitution}
    (agree : ∀ id kind, InspectedReduction program context level ((left.get id).getD (.parameter id kind))
      ((right.get id).getD (.parameter id kind))) :
    InspectedReduction program context level (term.substitute left) (term.substitute right) :=
  term.substitutions_related InspectedReduction.congr agree

/-- The actual root/children square carries two independent bounds: the
residual root keeps its source-inspection level, and the body residual keeps
the level of the child reductions. No conversion-to-join premise is used. -/
theorem HeadInspectionStepAt.children_residual {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {term value changed : Term} {stepped : DefinitionalStep program context term value}
    {rootLevel childLevel : Nat} (certificate : HeadInspectionStepAt program rootLevel stepped)
    (same : SameHead term changed)
    (children : ListRel (fun left right => ∃ reduced : DefinitionalReduction program context left right,
      HeadInspectionReductionAt program childLevel reduced) term.children changed.children) :
    ∃ newValue, (∃ residual : DefinitionalStep program context changed newValue,
      HeadInspectionStepAt program rootLevel residual) ∧
      (∃ body : DefinitionalReduction program context value newValue, HeadInspectionReductionAt program childLevel body) := by
  apply certificate.children_relation valid (InspectedReduction.reflexive program context childLevel)
    (fun _ _ reduced => reduced.choose.equal)
    (fun term _ _ agree => term.substitutions_inspected program context childLevel agree) same children

private theorem RowEquivalent.inspected_step_residuals {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Term} (equivalent : RowEquivalent left right) :
    ∀ level,
      (∀ value (stepped : DefinitionalStep program context left value), HeadInspectionStepAt program level stepped →
        ∃ result, (∃ residual : DefinitionalStep program context right result, HeadInspectionStepAt program level residual) ∧
          RowEquivalent value result) ∧
      (∀ value (stepped : DefinitionalStep program context right value), HeadInspectionStepAt program level stepped →
        ∃ result, (∃ residual : DefinitionalStep program context left result, HeadInspectionStepAt program level residual) ∧
          RowEquivalent value result) := by
  apply RowEquivalent.rec
    (motive_1 := fun left right _ => ∀ level,
      (∀ value (stepped : DefinitionalStep program context left value), HeadInspectionStepAt program level stepped →
        ∃ result, (∃ residual : DefinitionalStep program context right result, HeadInspectionStepAt program level residual) ∧
          RowEquivalent value result) ∧
      (∀ value (stepped : DefinitionalStep program context right value), HeadInspectionStepAt program level stepped →
        ∃ result, (∃ residual : DefinitionalStep program context left result, HeadInspectionStepAt program level residual) ∧
          RowEquivalent value result))
    (motive_2 := fun _ _ _ => True)
  · intro term level
    constructor <;> intro value stepped certificate <;> exact ⟨value,⟨stepped,certificate⟩,.refl⟩
  · intro _ _ _ ih level
    exact ⟨(ih level).2,(ih level).1⟩
  · intro _ _ _ _ _ first second level
    constructor
    · intro value stepped certificate
      obtain ⟨middle,⟨next,nextCertificate⟩,changed⟩ := (first level).1 value stepped certificate
      obtain ⟨result,residual,changedAgain⟩ := (second level).1 middle next nextCertificate
      exact ⟨result,residual,changed.trans changedAgain⟩
    · intro value stepped certificate
      obtain ⟨middle,⟨next,nextCertificate⟩,changed⟩ := (second level).2 value stepped certificate
      obtain ⟨result,residual,changedAgain⟩ := (first level).2 middle next nextCertificate
      exact ⟨result,residual,changed.trans changedAgain⟩
  · intro _ _ same children _ level
    constructor
    · intro _ _ certificate
      exact certificate.children_relation valid (fun _ => .refl) (fun _ _ equivalent => .row equivalent)
        (fun term _ _ agree => term.substitutions_rowEquivalent agree) same children
    · intro _ _ certificate
      exact certificate.children_relation valid (fun _ => .refl) (fun _ _ equivalent => .row equivalent)
        (fun term _ _ agree => term.substitutions_rowEquivalent agree) same.symm
        (children.swap.imp (fun _ _ equivalent => equivalent.symm))
  · intros; constructor <;> intro value stepped _ <;> cases stepped
  · intros; constructor <;> intro value stepped _ <;> cases stepped
  · intros; constructor <;> intro value stepped _ <;> cases stepped
  · intros; constructor <;> intro value stepped _ <;> cases stepped
  · exact True.intro
  · intros; exact True.intro
  · exact equivalent

/-- Row permutation, flattening and duplication retain an actual root
residual at the original source-inspection level. -/
theorem HeadInspectionStepAt.row_residual {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {term value changed : Term} {stepped : DefinitionalStep program context term value}
    {level : Nat} (certificate : HeadInspectionStepAt program level stepped) (equivalent : RowEquivalent term changed) :
    ∃ result, (∃ residual : DefinitionalStep program context changed result, HeadInspectionStepAt program level residual) ∧
      RowEquivalent value result :=
  (equivalent.inspected_step_residuals valid level).1 value stepped certificate

end Glorious.Language
