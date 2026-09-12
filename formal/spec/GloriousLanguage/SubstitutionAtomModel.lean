import GloriousLanguage.AtomInstantiation

/-! A proof-model totalization of simultaneous substitution. On every
admitted source term this is exactly `Term.substitute`; the only extension is
to leave a wrong-kind parameter occurrence unchanged outside that domain.
This lets the single atom/capability morphism cover untyped proof syntax
without altering the source substitution operation or granting permissions. -/
namespace Glorious.Language

namespace SubstitutionAtomModel

noncomputable def term (substitution : Substitution) (source : Term) : Term :=
  open Classical in
  match source with
  | .parameter id kind =>
      let value := (substitution.get id).getD (.parameter id kind)
      if value.kind = kind then value else .parameter id kind
  | other => other.mapChildren (fun child => if _member : child ∈ other.children then term substitution child else child)
termination_by source
decreasing_by exact Term.child_sizeOf _member

theorem node (substitution : Substitution) {source : Term}
    (notParameter : ∀ id kind, source ≠ .parameter id kind) :
    term substitution source = source.mapChildren (term substitution) := by
  rw [term]
  · apply Term.mapChildren_congr
    intro child member
    simp only [dif_pos member]
  · exact notParameter

theorem shape (substitution : Substitution) : AtomHomomorphism (term substitution) := by
  intro source
  cases source
  all_goals try rfl
  all_goals apply node
  all_goals intro id kind equal
  all_goals cases equal

theorem kind (substitution : Substitution) (source : Term) : (term substitution source).kind = source.kind := by
  cases source
  case parameter id kind =>
    rw [term]
    split
    · assumption
    · rfl
  all_goals rw [node substitution (by intro id kind equal; cases equal)]
  all_goals rfl

theorem fixed (substitution : Substitution) (source : Term) : source.AtomsFixed (term substitution) := by
  intro atom _
  cases atom <;> try trivial
  all_goals rw [node substitution (by intro id kind equal; cases equal)]
  all_goals rfl

theorem kinded_eq {program : Program} {source target : Context} {value : Term} {kind : Kind}
    (kinded : Kinding program source value kind) (substitution : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute substitution) binder.kind) :
    term substitution value = value.substitute substitution := by
  by_cases parameter : ∃ id kind, value = .parameter id kind
  · obtain ⟨id,kind,rfl⟩ := parameter
    cases kinded with
    | parameter member =>
      rw [term]
      have correct := (parameters _ member).term_kind
      simp only [Term.substitute] at correct ⊢
      exact if_pos correct
  · have notParameter : ∀ id kind, value ≠ .parameter id kind := fun id kind equal => parameter ⟨id,kind,equal⟩
    rw [node substitution notParameter,Term.substitute_eq_mapChildren substitution notParameter]
    apply Term.mapChildren_congr
    intro child member
    obtain ⟨childKind,childKinded⟩ := kinded.child member
    exact kinded_eq childKinded substitution parameters
termination_by value
decreasing_by exact Term.child_sizeOf member

end SubstitutionAtomModel
end Glorious.Language
