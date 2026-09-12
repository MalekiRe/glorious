import GloriousLanguage.FreshAtomInterpretation

/-! A generic inspection uses one fresh rigid per actual binder identity.
The same ordered `Instantiates` graph supplies both inspection arguments and
their arbitrary caller specialization; no second binding mechanism is used. -/
namespace Glorious.Language

theorem Instantiates.values_eq_lookup {binders : List Binder} {values : List Term} {substitution : Substitution}
    (instantiated : Instantiates binders values substitution) :
    values = binders.map (fun binder => (substitution.get binder.id).getD (.parameter binder.id binder.kind)) := by
  rw [instantiated.2.2]
  have unique := instantiated.1
  have related := instantiated.2.1
  clear instantiated substitution
  induction related with
  | nil => rfl
  | @cons first value binders values head tail ih =>
    simp only [List.map_cons,List.nodup_cons] at unique
    simp only [List.map_cons,List.zip_cons_cons]
    congr 1
    · simp only [Table.get,List.find?_cons,beq_self_eq_true,Option.map_some,Option.getD_some]
    · apply (ih unique.2).trans
      apply List.map_congr_left
      intro binder present
      have different : first.id ≠ binder.id := by
        intro same
        exact unique.1 (same.symm ▸ List.mem_map.mpr ⟨binder,present,rfl⟩)
      simp [Table.get,different]

namespace FreshInstantiation

def values (binders : List Binder) (level : Nat) : List Term :=
  binders.map (fun binder => .rigid binder.id binder.kind level)

def substitution (binders : List Binder) (level : Nat) : Substitution :=
  (binders.map (·.id)).zip (values binders level)

theorem instantiated {binders : List Binder} (unique : (binders.map (·.id)).Nodup) (level : Nat) :
    Instantiates binders (values binders level) (substitution binders level) := by
  refine ⟨unique,?_,rfl⟩
  clear unique
  induction binders with
  | nil => exact .nil
  | cons binder binders ih => exact .cons rfl ih

theorem kinded (program : Program) (context : Context) (binders : List Binder) {level : Nat}
    (bounded : level ≤ context.universeLevel) :
    ∀ value ∈ values binders level, Kinding program context value value.kind := by
  intro value present
  obtain ⟨binder,_,rfl⟩ := List.mem_map.mp present
  exact .rigid bounded

theorem specialize_values {binders : List Binder} {arguments : List Term} {caller : Substitution}
    (opened : Instantiates binders arguments caller) {cutoff level : Nat} (fresh : cutoff < level) :
    (values binders level).map (FreshAtomSpecialization.ofSubstitution cutoff caller).term = arguments := by
  rw [opened.values_eq_lookup]
  unfold values
  rw [List.map_map]
  apply List.map_congr_left
  intro binder present
  obtain ⟨value,_,sameKind,found⟩ := opened.binder_lookup present
  simp only [Function.comp_def,found,Option.getD_some]
  exact FreshAtomSpecialization.ofSubstitution_rigid fresh found sameKind.symm

/-- The fresh inspection table specializes to the caller's actual raw table,
not merely to a table with extensionally equal lookups. This equality is
consumed by the hygienic predicate substitution graph. -/
theorem specialize_substitution {binders : List Binder} {arguments : List Term} {caller : Substitution}
    (opened : Instantiates binders arguments caller) {cutoff level : Nat} (fresh : cutoff < level) :
    (substitution binders level).map (fun entry =>
      (entry.1,(FreshAtomSpecialization.ofSubstitution cutoff caller).term entry.2)) = caller := by
  have mapped := (instantiated opened.1 level).map_values
    (FreshAtomSpecialization.ofSubstitution cutoff caller).term
    (fun value _ => (FreshAtomSpecialization.ofSubstitution cutoff caller).kind value)
  rw [specialize_values opened fresh] at mapped
  exact mapped.2.2.trans opened.2.2.symm

theorem admitted {program : Program} {context : Context} {binders : List Binder} {arguments : List Term}
    {caller : Substitution} (opened : Instantiates binders arguments caller)
    (argumentsKinded : ∀ value ∈ arguments, Kinding program context value value.kind) :
    (FreshAtomSpecialization.ofSubstitution context.universeLevel caller).Admitted program context := by
  apply FreshAtomSpecialization.ofSubstitution_admitted
  intro id value found
  exact argumentsKinded value (opened.argument_of_get found)

end FreshInstantiation
end Glorious.Language
