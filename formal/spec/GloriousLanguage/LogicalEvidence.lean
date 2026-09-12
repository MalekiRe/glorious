import GloriousLanguage.ContextualReduction

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
    (instantiated : Instantiates binders values substitution)
    (kinded : ∀ value ∈ values, Kinding program context value value.kind)
    (member : requirement ∈ requirements) (admitted : requirement.SubstitutionAdmissible substitution) :
    EntailsSubstitution program context substitution requirement :=
  .instantiated ⟨admitted,rfl⟩ (.quantifiedInstance held instantiated kinded member ⟨admitted,rfl⟩)

theorem ListRel.substitution_getD {program : Program} {context : Context} {left right : Substitution}
    (related : ListRel (fun first second => first.1 = second.1 ∧
      DefinitionallyEqual program context first.2 second.2) left right) :
    ∀ id kind, DefinitionallyEqual program context ((left.get id).getD (.parameter id kind))
      ((right.get id).getD (.parameter id kind)) := by
  induction related with
  | nil => intros; exact .refl
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

theorem Instantiates.congr_values {program : Program} {context : Context}
    {binders : List Binder} {before after : List Term} {substitution : Substitution}
    (instantiated : Instantiates binders before substitution)
    (related : ListRel (DefinitionallyEqual program context) before after) :
    ListRel (fun first second => first.1 = second.1 ∧ DefinitionallyEqual program context first.2 second.2)
      substitution ((binders.map (·.id)).zip after) := by
  rw [instantiated.2.2]
  have alignment := instantiated.2.1
  clear instantiated substitution
  induction alignment generalizing after with
  | nil => cases related; exact .nil
  | cons _ _ ih =>
    cases related with
    | cons head tail => exact .cons ⟨rfl,head⟩ (ih tail)

/-- The logical requirement consumer is complete once the target's actual
capture-admissible graphs are available. Deriving those graphs across arbitrary
conversion requires hygienic predicate substitution; it is not assumed here. -/
theorem ProjectionDomain.congr_arguments {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {trait member : DeclId} {owners items newOwners newItems : List Term}
    {associated : AssociatedDefinition} {ownerSub itemSub : Substitution}
    (domain : ProjectionDomain program context trait member owners items associated ownerSub itemSub)
    (ownerEqual : ListRel (DefinitionallyEqual program context) owners newOwners)
    (itemEqual : ListRel (DefinitionallyEqual program context) items newItems)
    (ownerAdmissible : ∀ declaration, program.trait trait = some declaration →
      ∀ requirement ∈ declaration.requirements,
        requirement.SubstitutionAdmissible ((declaration.generics.map (·.id)).zip newOwners))
    (itemAdmissible : ∀ declaration, program.trait trait = some declaration →
      ∀ requirement ∈ associated.requirements,
        requirement.SubstitutionAdmissible (((declaration.generics.map (·.id)).zip newOwners) ++
          ((associated.generics.map (·.id)).zip newItems))) :
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
      exact (ownerRequirements requirement present).congr_substitution (ownerAdmissible _ found requirement present)
        (fun id kind => .definitional (ownerRelation.substitution_getD id kind))
    · intro requirement present
      exact (itemRequirements requirement present).congr_substitution (itemAdmissible _ found requirement present)
        (fun id kind => .definitional ((ownerRelation.append itemRelation).substitution_getD id kind))

end Glorious.Language
