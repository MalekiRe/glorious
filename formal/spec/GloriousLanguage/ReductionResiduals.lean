import GloriousLanguage.LogicalEvidence

/-! Residuals of actual declared expansions under reduction of their argument
children. These consume source admission and logical domain transport; no
termination or global confluence premise is introduced. -/
namespace Glorious.Language

theorem ProjectionDomain.relate_arguments {program : Program} (valid : ProgramWellFormed program)
    {relation : Term → Term → Prop}
    {context : Context} {trait member : DeclId} {owners items newOwners newItems : List Term}
    {associated : AssociatedDefinition} {ownerSub itemSub : Substitution}
    (converts : ∀ left right, relation left right → DefinitionallyEqual program context left right)
    (domain : ProjectionDomain program context trait member owners items associated ownerSub itemSub)
    (ownerReduces : ListRel relation owners newOwners)
    (itemReduces : ListRel relation items newItems) :
    ∃ newOwnerSub newItemSub,
      ProjectionDomain program context trait member newOwners newItems associated newOwnerSub newItemSub ∧
      ListRel (fun first second => first.1 = second.1 ∧
        relation first.2 second.2) ownerSub newOwnerSub ∧
      ListRel (fun first second => first.1 = second.1 ∧
        relation first.2 second.2) itemSub newItemSub := by
  obtain ⟨newOwnerSub,newItemSub,next⟩ := domain.congr_arguments valid
    (ownerReduces.imp converts) (itemReduces.imp converts)
  refine ⟨newOwnerSub,newItemSub,next,?_⟩
  cases domain with
  | valid traitFound _ _ _ ownerInstance itemInstance _ _ _ =>
    cases next with
    | valid nextTraitFound _ _ _ nextOwnerInstance nextItemInstance _ _ _ =>
      have same := Option.some.inj (traitFound.symm.trans nextTraitFound)
      subst_vars
      constructor
      · rw [nextOwnerInstance.2.2]
        exact ownerInstance.related_values ownerReduces
      · rw [nextItemInstance.2.2]
        exact itemInstance.related_values itemReduces

theorem DefinitionalStep.alias_argument_relation {program : Program} (valid : ProgramWellFormed program)
    {relation : Term → Term → Prop}
    {context : Context} {id : DeclId} {arguments newArguments : List Term} {value : Term}
    (reflexive : ∀ term, relation term term)
    (converts : ∀ left right, relation left right → DefinitionallyEqual program context left right)
    (substitutionPreserves : ∀ (term : Term) (left right : Substitution),
      (∀ id kind, relation ((left.get id).getD (.parameter id kind))
        ((right.get id).getD (.parameter id kind))) → relation (term.substitute left) (term.substitute right))
    (step : DefinitionalStep program context (.alias id arguments) value)
    (argumentsReduce : ListRel relation arguments newArguments) :
    ∃ newValue, DefinitionalStep program context (.alias id newArguments) newValue ∧
      relation value newValue := by
  cases step with
  | alias found instantiated kinded substituted =>
    have transport : ListRel (KindTransport program context) arguments newArguments :=
      argumentsReduce.imp (fun _ _ reduced kind typed => ((converts _ _ reduced).kinding_iff valid kind).mp typed)
    have nextInstance := instantiated.kind_transport kinded transport
    have environments := instantiated.related_values argumentsReduce
    have lookup := environments.substitution_getD_related reflexive
    refine ⟨_,.alias found nextInstance (transport.arguments_kinded_right kinded)
      (substituted.congr_substitution valid (fun id kind => converts _ _ (lookup id kind))),?_⟩
    rw [substituted.2.1]
    exact substitutionPreserves _ _ _ lookup

theorem DefinitionalStep.projection_argument_relation {program : Program} (valid : ProgramWellFormed program)
    {relation : Term → Term → Prop}
    {context : Context} {trait member : DeclId} {owners items newOwners newItems : List Term} {kind : Kind}
    {value : Term} (reflexive : ∀ term, relation term term)
    (converts : ∀ left right, relation left right → DefinitionallyEqual program context left right)
    (substitutionPreserves : ∀ (term : Term) (left right : Substitution),
      (∀ id kind, relation ((left.get id).getD (.parameter id kind))
        ((right.get id).getD (.parameter id kind))) → relation (term.substitute left) (term.substitute right))
    (step : DefinitionalStep program context (.projection trait member owners items kind) value)
    (ownerReduces : ListRel relation owners newOwners)
    (itemReduces : ListRel relation items newItems) :
    ∃ newValue, DefinitionalStep program context (.projection trait member newOwners newItems kind) newValue ∧
      relation value newValue := by
  cases step with
  | @projection _ _ _ _ _ associated ownerSub itemSub implementation implSub body value
      domain selected memberBody substituted =>
    obtain ⟨newOwnerSub,newItemSub,next,_,itemEnvironments⟩ :=
      domain.relate_arguments valid converts ownerReduces itemReduces
    have unchanged : ListRel (fun first second => first.1 = second.1 ∧
        relation first.2 second.2) implSub implSub := by
      simpa only [List.map_id] using
        ListRel.maps implSub id id (fun _ _ => And.intro rfl (reflexive _))
    have environments := unchanged.append itemEnvironments
    have lookup := environments.substitution_getD_related reflexive
    refine ⟨_,.projection next (selected.congr_query (ownerReduces.imp converts))
      memberBody (substituted.congr_substitution valid (fun id kind => converts _ _ (lookup id kind))),?_⟩
    rw [substituted.2.1]
    exact substitutionPreserves body _ _ lookup
  | defaultProjection domain selected missing default substituted =>
    obtain ⟨newOwnerSub,newItemSub,next,ownerEnvironments,itemEnvironments⟩ :=
      domain.relate_arguments valid converts ownerReduces itemReduces
    have lookup := (ownerEnvironments.append itemEnvironments).substitution_getD_related reflexive
    refine ⟨_,.defaultProjection next (selected.congr_query (ownerReduces.imp converts))
      missing default (substituted.congr_substitution valid (fun id kind => converts _ _ (lookup id kind))),?_⟩
    rw [substituted.2.1]
    exact substitutionPreserves _ _ _ lookup

/-- A root expansion has a residual after arbitrary positive reduction of its
children. The resulting body is related by positive reduction, not merely by
the symmetric equality relation used by head matching. -/
theorem DefinitionalStep.children_relation {program : Program} (valid : ProgramWellFormed program)
    {relation : Term → Term → Prop} {context : Context} {term value changed : Term}
    (reflexive : ∀ term, relation term term)
    (converts : ∀ left right, relation left right → DefinitionallyEqual program context left right)
    (substitutionPreserves : ∀ (term : Term) (left right : Substitution),
      (∀ id kind, relation ((left.get id).getD (.parameter id kind))
        ((right.get id).getD (.parameter id kind))) → relation (term.substitute left) (term.substitute right))
    (step : DefinitionalStep program context term value)
    (same : SameHead term changed)
    (children : ListRel relation term.children changed.children) :
    ∃ newValue, DefinitionalStep program context changed newValue ∧
      relation value newValue := by
  cases step <;> cases changed <;> simp_all [SameHead,Term.mapChildren]
  all_goals simp only [Term.children] at children
  case alias.alias =>
    exact DefinitionalStep.alias_argument_relation valid reflexive converts substitutionPreserves
      (.alias (by assumption) (by assumption)
      (by assumption) (by assumption)) children
  case projection.projection =>
    have split := children.split_append (by simpa using congrArg List.length same.2.2.1)
    rw [← same.2.2.2.2]
    exact DefinitionalStep.projection_argument_relation valid reflexive converts substitutionPreserves
      (.projection (by assumption) (by assumption)
      (by assumption) (by assumption)) split.1 split.2
  case defaultProjection.projection =>
    have split := children.split_append (by simpa using congrArg List.length same.2.2.1)
    rw [← same.2.2.2.2]
    exact DefinitionalStep.projection_argument_relation valid reflexive converts substitutionPreserves
      (.defaultProjection (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption)) split.1 split.2

theorem DefinitionalStep.children_residual {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {term value changed : Term} (step : DefinitionalStep program context term value)
    (same : SameHead term changed)
    (children : ListRel (DefinitionalReduction program context) term.children changed.children) :
    ∃ newValue, DefinitionalStep program context changed newValue ∧
      DefinitionalReduction program context value newValue :=
  step.children_relation valid (fun _ => .refl) (fun _ _ reduced => reduced.equal)
    (fun term _ _ agrees => term.substitutions_reduce program context agrees) same children

theorem DefinitionalStep.row_children_residual {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {term value changed : Term} (step : DefinitionalStep program context term value)
    (same : SameHead term changed) (children : ListRel RowEquivalent term.children changed.children) :
    ∃ newValue, DefinitionalStep program context changed newValue ∧ RowEquivalent value newValue :=
  step.children_relation valid (fun _ => .refl) (fun _ _ same => .row same)
    (fun term _ _ agrees => term.substitutions_rowEquivalent agrees) same children

private theorem ListRel.row_symm {left right : List Term} (related : ListRel RowEquivalent left right) :
    ListRel RowEquivalent right left := by
  induction related with
  | nil => exact .nil
  | cons head _ tail => exact .cons head.symm tail

/-- Row transport is a property of a root relation and its actual child
residuals. Proof-only restrictions on declared roots reuse this same closure
argument; they do not reconstruct row semantics independently. -/
theorem RowEquivalent.root_relation_residuals {root : Term → Term → Prop}
    (notRow : ∀ instances tails value, ¬ root (.row instances tails) value)
    (childrenResidual : ∀ {term value changed}, root term value → SameHead term changed →
      ListRel RowEquivalent term.children changed.children →
      ∃ result, root changed result ∧ RowEquivalent value result)
    {left right : Term} (equivalent : RowEquivalent left right) :
    (∀ value, root left value → ∃ result, root right result ∧ RowEquivalent value result) ∧
    (∀ value, root right value → ∃ result, root left result ∧ RowEquivalent value result) := by
  apply RowEquivalent.rec
    (motive_1 := fun left right _ =>
      (∀ value, root left value → ∃ result, root right result ∧ RowEquivalent value result) ∧
      (∀ value, root right value → ∃ result, root left result ∧ RowEquivalent value result))
    (motive_2 := fun _ _ _ => True)
  · intro term
    constructor <;> intro value step <;> exact ⟨value,step,.refl⟩
  · intro _ _ _ ih
    exact ⟨ih.2,ih.1⟩
  · intro _ _ _ _ _ first second
    constructor
    · intro value step
      obtain ⟨middle,stepped,changed⟩ := first.1 value step
      obtain ⟨result,steppedAgain,changedAgain⟩ := second.1 middle stepped
      exact ⟨result,steppedAgain,changed.trans changedAgain⟩
    · intro value step
      obtain ⟨middle,stepped,changed⟩ := second.2 value step
      obtain ⟨result,steppedAgain,changedAgain⟩ := first.2 middle stepped
      exact ⟨result,steppedAgain,changed.trans changedAgain⟩
  · intro _ _ same children _
    exact ⟨fun _ step => childrenResidual step same children,
      fun _ step => childrenResidual step same.symm children.row_symm⟩
  · intros
    constructor <;> intro value step <;> exact False.elim (notRow _ _ value step)
  · intros
    constructor <;> intro value step <;> exact False.elim (notRow _ _ value step)
  · intros
    constructor <;> intro value step <;> exact False.elim (notRow _ _ value step)
  · intros
    constructor <;> intro value step <;> exact False.elim (notRow _ _ value step)
  · exact True.intro
  · intros; exact True.intro
  · exact equivalent

/-- Permuting, flattening, or deduplicating rows cannot destroy a declared
redex. Its actual residual result remains row-equivalent, including through
arbitrary enclosing term constructors. -/
theorem DefinitionalStep.row_residual {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {term value changed : Term} (step : DefinitionalStep program context term value)
    (equivalent : RowEquivalent term changed) :
    ∃ result, DefinitionalStep program context changed result ∧ RowEquivalent value result :=
  (equivalent.root_relation_residuals (fun _ _ _ impossible => by cases impossible)
    (fun root same children => root.row_children_residual valid same children)).1 value step

end Glorious.Language
