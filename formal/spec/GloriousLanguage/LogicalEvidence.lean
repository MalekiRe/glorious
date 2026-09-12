import GloriousLanguage.ContextualReduction
import GloriousLanguage.PredicateSubstitutionKinding

/-! Logical equality transports actual predicate evidence through the existing
capture-admissible substitution graph. Definitional matching remains separate:
lexical assumptions never become declaration-head coherence evidence. -/
namespace Glorious.Language

theorem Entails.congr_substitution {program : Program} {context : Context} {template left right : Constraint}
    {leftSub rightSub : Substitution} (held : Entails program context left)
    (before : SubstituteConstraint leftSub template left) (after : SubstituteConstraint rightSub template right)
    (equal : ∀ id kind, Equal program context ((leftSub.get id).getD (.parameter id kind))
      ((rightSub.get id).getD (.parameter id kind))) : Entails program context right :=
  .congr (.substitution equal before after) held

theorem EntailsSubstitution.congr_substitution {program : Program} {context : Context} {requirement : Constraint}
    {left right : Substitution} (held : EntailsSubstitution program context left requirement)
    (admitted : requirement.SubstitutionAdmissible right)
    (equal : ∀ id kind, Equal program context ((left.get id).getD (.parameter id kind))
      ((right.get id).getD (.parameter id kind))) : EntailsSubstitution program context right requirement := by
  cases held with
  | instantiated before held =>
    exact .instantiated ⟨admitted,rfl⟩ (held.congr_substitution before ⟨admitted,rfl⟩ equal)

theorem Entails.quantified_requirement {program : Program} {context : Context} {binders : List Binder}
    {requirements : List Constraint} {values : List Term} {substitution : Substitution} {requirement : Constraint}
    (held : Entails program context (.quantified binders requirements))
    (admitted : ConstraintKinded program context (.quantified binders requirements))
    (instantiated : Instantiates binders values substitution)
    (kinded : ∀ value ∈ values, Kinding program context value value.kind)
    (member : requirement ∈ requirements) :
    EntailsSubstitution program context substitution requirement ∧
      ConstraintKinded program context (requirement.substitute substitution) := by
  obtain ⟨substituted,resultKinded⟩ := admitted.quantified_instance instantiated kinded member
  exact ⟨.instantiated substituted (.quantifiedInstance held instantiated kinded member substituted),resultKinded⟩

theorem ListRel.substitution_getD_related {relation : Term → Term → Prop}
    (reflexive : ∀ term, relation term term) {left right : Substitution}
    (related : ListRel (fun first second => first.1 = second.1 ∧
      relation first.2 second.2) left right) :
    ∀ id kind, relation ((left.get id).getD (.parameter id kind))
      ((right.get id).getD (.parameter id kind)) := by
  induction related with
  | nil => intros; exact reflexive _
  | @cons first second left right head _ ih =>
    rcases first with ⟨key,first⟩
    rcases second with ⟨otherKey,second⟩
    obtain ⟨same,equal⟩ := head
    simp only at same equal
    subst otherKey
    intro id kind
    by_cases found : key = id
    · simpa [Table.get,found] using equal
    · simpa [Table.get,found] using ih id kind

theorem ListRel.substitution_getD {program : Program} {context : Context} {left right : Substitution}
    (related : ListRel (fun first second => first.1 = second.1 ∧
      DefinitionallyEqual program context first.2 second.2) left right) :
    ∀ id kind, DefinitionallyEqual program context ((left.get id).getD (.parameter id kind))
      ((right.get id).getD (.parameter id kind)) :=
  related.substitution_getD_related (fun _ => .refl)

theorem Instantiates.related_values {relation : Term → Term → Prop}
    {binders : List Binder} {before after : List Term} {substitution : Substitution}
    (instantiated : Instantiates binders before substitution)
    (related : ListRel relation before after) :
    ListRel (fun first second => first.1 = second.1 ∧ relation first.2 second.2)
      substitution ((binders.map (·.id)).zip after) := by
  rw [instantiated.2.2]
  have alignment := instantiated.2.1
  clear instantiated substitution
  induction alignment generalizing after with
  | nil => cases related; exact .nil
  | cons _ _ ih =>
    cases related with
    | cons head tail => exact .cons ⟨rfl,head⟩ (ih tail)

theorem Instantiates.congr_values {program : Program} {context : Context}
    {binders : List Binder} {before after : List Term} {substitution : Substitution}
    (instantiated : Instantiates binders before substitution)
    (related : ListRel (DefinitionallyEqual program context) before after) :
    ListRel (fun first second => first.1 = second.1 ∧ DefinitionallyEqual program context first.2 second.2)
      substitution ((binders.map (·.id)).zip after) := instantiated.related_values related

theorem Term.substitutions_convert (program : Program) (context : Context) (term : Term)
    {left right : Substitution}
    (agree : ∀ id kind, DefinitionallyEqual program context ((left.get id).getD (.parameter id kind))
      ((right.get id).getD (.parameter id kind))) :
    DefinitionallyEqual program context (term.substitute left) (term.substitute right) :=
  term.substitutions_related DefinitionallyEqual.congr agree

/-- Actual ordered instantiations and field graphs share one conversion
transport, consumed by both capability inversion and target representation. -/
theorem Instantiates.convertible_tables {program : Program} {context : Context}
    {binders : List Binder} {left right : List Term} {first second : Substitution}
    (before : Instantiates binders left first) (after : Instantiates binders right second)
    (arguments : ListRel (DefinitionallyEqual program context) left right) :
    SubstitutionsConvertible program context first second := by
  rw [after.2.2]
  exact before.related_values arguments

theorem ListRel.substituted_conversion {program : Program} {context : Context}
    {templates left right : List Term} {first second : Substitution}
    (before : ListRel (Substitutes first) templates left) (after : ListRel (Substitutes second) templates right)
    (tables : SubstitutionsConvertible program context first second) :
    ListRel (DefinitionallyEqual program context) left right := by
  induction before generalizing right with
  | nil => cases after; exact .nil
  | @cons template left templates rest graph _ ih =>
    cases after with
    | cons other tail =>
      exact .cons (by rw [graph.2.1,other.2.1]; exact template.substitutions_convert program context tables.substitution_getD)
        (ih tail)

/-- The authoritative callable-field instance transports its own captures
through the actual related argument tables, including operation values. -/
theorem CallableFields.convertible {program : Program} {context : Context} {id : DeclId}
    {left right first second : List Term} (before : CallableFields program id left first)
    (after : CallableFields program id right second)
    (arguments : ListRel (DefinitionallyEqual program context) left right) :
    ListRel (DefinitionallyEqual program context) first second := by
  cases before with
  | function found instantiated fields =>
    cases after with
    | function other next otherFields =>
      obtain rfl := Option.some.inj (found.symm.trans other)
      exact fields.substituted_conversion otherFields (instantiated.convertible_tables next arguments)
    | operation other _ =>
      cases (Program.function_lookup found).symm.trans (Program.operation_lookup other)
  | operation found _ =>
    cases after with
    | function other _ _ =>
      cases (Program.operation_lookup found).symm.trans (Program.function_lookup other)
    | operation => exact .nil

theorem Substitutes.congr_substitution {program : Program} (valid : ProgramWellFormed program) {context : Context}
    {left right : Substitution} {before after : Term} (substituted : Substitutes left before after)
    (equal : ∀ id kind, DefinitionallyEqual program context ((left.get id).getD (.parameter id kind))
      ((right.get id).getD (.parameter id kind))) : Substitutes right before (before.substitute right) := by
  have previous : before.kind = (before.substitute left).kind := by rw [← substituted.2.1]; exact substituted.1
  refine ⟨previous.trans ((before.substitutions_convert program context equal).kind_eq valid),rfl,?_⟩
  intro id kind value occurs found
  have changed := (equal id kind).kind_eq valid
  cases original : left.get id with
  | none => simpa only [original,found,Option.getD,Term.kind] using changed.symm
  | some old =>
    have previous := substituted.2.2 id kind old occurs original
    simp only [original,found,Option.getD] at changed
    exact changed.symm.trans previous

theorem Constraint.SubstitutionAdmissible.congr_substitution {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Substitution} {constraint : Constraint}
    (admitted : constraint.SubstitutionAdmissible left)
    (related : ListRel (fun first second => first.1 = second.1 ∧
      DefinitionallyEqual program context first.2 second.2) left right) : constraint.SubstitutionAdmissible right := by
  cases constraint <;> simp only [Constraint.SubstitutionAdmissible] at admitted ⊢
  all_goals try exact ⟨admitted.1.congr_substitution valid related.substitution_getD,
    admitted.2.congr_substitution valid related.substitution_getD⟩
  case use => exact admitted.congr_substitution valid related.substitution_getD
  all_goals try {
    intro term present
    exact (admitted term present).congr_substitution valid related.substitution_getD }
  case quantified binders requirements =>
    have filtered := related.filter
      (fun entry => !(binders.any (fun binder => binder.id == entry.1)))
      (fun entry => !(binders.any (fun binder => binder.id == entry.1)))
      (fun _ _ pair => by rw [pair.1])
    constructor
    · intro index binder present value found
      have prefixRelated := related.filter
        (fun entry => !((binders.take index).any (fun binder => binder.id == entry.1)))
        (fun entry => !((binders.take index).any (fun binder => binder.id == entry.1)))
        (fun _ _ pair => by rw [pair.1])
      exact (admitted.1 index binder present value found).congr_substitution valid prefixRelated.substitution_getD
    · intro requirement present
      exact (admitted.2 requirement present).congr_substitution valid filtered
termination_by constraint

theorem EntailsSubstitution.convert_substitution {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Substitution} {requirement : Constraint}
    (held : EntailsSubstitution program context left requirement)
    (related : ListRel (fun first second => first.1 = second.1 ∧
      DefinitionallyEqual program context first.2 second.2) left right) :
    EntailsSubstitution program context right requirement := by
  cases held with
  | instantiated substituted held =>
    have admitted := substituted.1.congr_substitution valid related
    exact .instantiated ⟨admitted,rfl⟩ (held.congr_substitution substituted ⟨admitted,rfl⟩
      (fun id kind => .definitional (related.substitution_getD id kind)))

/-- Actual projection domains survive conversion of owner and item arguments.
Target kinded substitution graphs are derived from the input graph and general
conversion kind preservation; hygienic quantified substitution supplies capture
avoidance without an extra target-domain or freshness admission premise. -/
theorem ProjectionDomain.congr_arguments {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {trait member : DeclId} {owners items newOwners newItems : List Term}
    {associated : AssociatedDefinition} {ownerSub itemSub : Substitution}
    (domain : ProjectionDomain program context trait member owners items associated ownerSub itemSub)
    (ownerEqual : ListRel (DefinitionallyEqual program context) owners newOwners)
    (itemEqual : ListRel (DefinitionallyEqual program context) items newItems) :
    ∃ newOwnerSub newItemSub,
      ProjectionDomain program context trait member newOwners newItems associated newOwnerSub newItemSub := by
  cases domain with
  | valid found member associatedFound owner ownerInstance itemInstance arguments ownerRequirements itemRequirements =>
    have ownerKinds := fun term present => arguments term (List.mem_append_left _ present)
    have itemKinds := fun term present => arguments term (List.mem_append_right _ present)
    have ownerTransport := ownerEqual.imp (fun _ _ equal kind => (equal.kinding_iff valid kind).mp)
    have itemTransport := itemEqual.imp (fun _ _ equal kind => (equal.kinding_iff valid kind).mp)
    have ownerRelation := ownerInstance.congr_values ownerEqual
    have itemRelation := itemInstance.congr_values itemEqual
    refine ⟨_,_,.valid found member associatedFound owner
      (ownerInstance.kind_transport ownerKinds ownerTransport)
      (itemInstance.kind_transport itemKinds itemTransport) ?_ ?_ ?_⟩
    · exact (ownerTransport.append itemTransport).arguments_kinded_right arguments
    · intro requirement present
      exact (ownerRequirements requirement present).convert_substitution valid ownerRelation
    · intro requirement present
      exact (itemRequirements requirement present).convert_substitution valid (ownerRelation.append itemRelation)

end Glorious.Language
