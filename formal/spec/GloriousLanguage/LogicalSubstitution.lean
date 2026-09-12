import GloriousLanguage.LogicalKinding

/-! Logical conversion preserves the actual hygienic substitution domain.
Kind preservation is derived from admitted source assumptions; callers need
not provide an admissibility certificate for the desired converted table. -/
namespace Glorious.Language

theorem Substitutes.congr_logical_substitution {program : Program} (valid : ProgramWellFormed program)
    {context : Context} (contextKinded : ∀ constraint ∈ context.assumptions, ConstraintKinded program context constraint)
    {left right : Substitution} {before after : Term} (substituted : Substitutes left before after)
    (equal : ∀ id kind, Equal program context ((left.get id).getD (.parameter id kind))
      ((right.get id).getD (.parameter id kind))) : Substitutes right before (before.substitute right) := by
  have checked : ∀ id kind value, Occurs (.parameter id kind) before → right.get id = some value → value.kind = kind := by
    intro id kind value occurs found
    have changed := (equal id kind).kind_eq valid contextKinded
    cases original : left.get id with
    | none => simpa only [original,found,Option.getD,Term.kind] using changed.symm
    | some old =>
      have previous := substituted.2.2 id kind old occurs original
      simp only [original,found,Option.getD] at changed
      exact changed.symm.trans previous
  refine ⟨?_,rfl,checked⟩
  cases before <;> simp only [Term.substitute,Term.kind]
  case parameter id kind =>
    cases found : right.get id with
    | none => rfl
    | some value => exact (checked id kind value .here found).symm

theorem Constraint.SubstitutionAdmissible.congr_logical_substitution {program : Program}
    (valid : ProgramWellFormed program) {context : Context}
    (contextKinded : ∀ constraint ∈ context.assumptions, ConstraintKinded program context constraint)
    {left right : Substitution} {constraint : Constraint} (admitted : constraint.SubstitutionAdmissible left)
    (related : ListRel (fun first second => first.1 = second.1 ∧ Equal program context first.2 second.2) left right) :
    constraint.SubstitutionAdmissible right := by
  have lookups := related.substitution_getD_related (fun _ => Equal.refl (program := program) (context := context))
  cases constraint <;> simp only [Constraint.SubstitutionAdmissible] at admitted ⊢
  all_goals try exact ⟨admitted.1.congr_logical_substitution valid contextKinded lookups,
    admitted.2.congr_logical_substitution valid contextKinded lookups⟩
  case use => exact admitted.congr_logical_substitution valid contextKinded lookups
  all_goals try {
    intro term present
    exact (admitted term present).congr_logical_substitution valid contextKinded lookups }
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
      exact (admitted.1 index binder present value found).congr_logical_substitution valid contextKinded
        (prefixRelated.substitution_getD_related (fun _ => .refl))
    · intro requirement present
      exact (admitted.2 requirement present).congr_logical_substitution valid contextKinded filtered
termination_by constraint

/-- Actual instantiated requirements survive logical conversion of their
ordered raw table, including all nested quantifier masks and default prefixes.
The target substitution graph is a theorem, not an additional caller premise. -/
theorem EntailsSubstitution.convert_logical_substitution {program : Program} (valid : ProgramWellFormed program)
    {context : Context} (contextKinded : ∀ constraint ∈ context.assumptions, ConstraintKinded program context constraint)
    {left right : Substitution} {requirement : Constraint} (held : EntailsSubstitution program context left requirement)
    (related : ListRel (fun first second => first.1 = second.1 ∧ Equal program context first.2 second.2) left right) :
    EntailsSubstitution program context right requirement := by
  cases held with
  | instantiated substituted held =>
    have admitted := substituted.1.congr_logical_substitution valid contextKinded related
    exact .instantiated ⟨admitted,rfl⟩ (held.congr_substitution substituted ⟨admitted,rfl⟩
      (related.substitution_getD_related (fun _ => .refl)))

end Glorious.Language
