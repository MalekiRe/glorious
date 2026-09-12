import GloriousLanguage.AtomRenaming

/-! Bijective atom actions carry an exact correspondence between admitted
universe domains. Only elementary inverse and numerical level laws are input;
kinding and logical transport are derived from the actual Static rules. -/
namespace Glorious.Language

theorem AtomRenaming.term_leftInverse (forward backward : AtomRenaming)
    (regions : ∀ id, backward.region (forward.region id) = id)
    (rigids : ∀ id kind level,
      backward.rigid (forward.rigid id kind level).1 kind (forward.rigid id kind level).2 = (id,level))
    (variables : ∀ id kind level,
      backward.inference (forward.inference id kind level).1 kind (forward.inference id kind level).2 = (id,level))
    (term : Term) : backward.term (forward.term term) = term := by
  cases term <;> simp only [AtomRenaming.term,regions,rigids,variables,List.map_map,Function.comp_def]
  all_goals try rfl
  all_goals congr 1
  all_goals first
  | exact AtomRenaming.term_leftInverse forward backward regions rigids variables _
  | apply List.map_eq_self_of
    intro child _
    exact AtomRenaming.term_leftInverse forward backward regions rigids variables child
termination_by term

theorem AtomRenaming.constraint_leftInverse (forward backward : AtomRenaming)
    (terms : ∀ term, backward.term (forward.term term) = term) (constraint : Constraint) :
    backward.constraint (forward.constraint constraint) = constraint := by
  cases constraint <;>
    simp only [AtomRenaming.constraint,Constraint.mapTerms,terms,List.map_map,Function.comp_def,
      Option.map_map,Option.map_id']
  all_goals try rfl
  all_goals congr 1
  all_goals first
  | exact List.map_eq_self_of _ _ (fun _ _ => rfl)
  | apply List.map_eq_self_of
    intro child _
    exact terms child
  | apply List.map_eq_self_of
    intro requirement _
    exact AtomRenaming.constraint_leftInverse forward backward terms requirement
termination_by constraint

structure AtomEmbedding extends AtomRenaming where
  inverse : AtomRenaming
  levelMap : Nat → Nat
  region_left : ∀ id, inverse.region (region id) = id
  region_right : ∀ id, region (inverse.region id) = id
  rigid_left : ∀ id kind level, inverse.rigid (rigid id kind level).1 kind (rigid id kind level).2 = (id,level)
  rigid_right : ∀ id kind level, rigid (inverse.rigid id kind level).1 kind (inverse.rigid id kind level).2 = (id,level)
  inference_left : ∀ id kind level,
    inverse.inference (inference id kind level).1 kind (inference id kind level).2 = (id,level)
  inference_right : ∀ id kind level,
    inference (inverse.inference id kind level).1 kind (inverse.inference id kind level).2 = (id,level)
  rigid_bound : ∀ id kind level ambient, (rigid id kind level).2 ≤ levelMap ambient ↔ level ≤ ambient
  inference_bound : ∀ id kind level ambient, (inference id kind level).2 ≤ levelMap ambient ↔ level ≤ ambient

def AtomEmbedding.context (embedding : AtomEmbedding) (context : Context) : Context :=
  { context with
    binders := context.binders.map embedding.binder
    assumptions := context.assumptions.map embedding.constraint
    universeLevel := embedding.levelMap context.universeLevel }

theorem AtomEmbedding.term_leftInverse (embedding : AtomEmbedding) (term : Term) :
    embedding.inverse.term (embedding.term term) = term :=
  embedding.toAtomRenaming.term_leftInverse embedding.inverse embedding.region_left embedding.rigid_left embedding.inference_left term

theorem AtomEmbedding.term_rightInverse (embedding : AtomEmbedding) (term : Term) :
    embedding.term (embedding.inverse.term term) = term :=
  embedding.inverse.term_leftInverse embedding.toAtomRenaming embedding.region_right embedding.rigid_right embedding.inference_right term

theorem AtomEmbedding.constraint_leftInverse (embedding : AtomEmbedding) (constraint : Constraint) :
    embedding.inverse.constraint (embedding.constraint constraint) = constraint :=
  embedding.toAtomRenaming.constraint_leftInverse embedding.inverse embedding.term_leftInverse constraint

theorem AtomEmbedding.constraint_rightInverse (embedding : AtomEmbedding) (constraint : Constraint) :
    embedding.constraint (embedding.inverse.constraint constraint) = constraint :=
  embedding.inverse.constraint_leftInverse embedding.toAtomRenaming embedding.term_rightInverse constraint

theorem AtomEmbedding.binder_leftInverse (embedding : AtomEmbedding) (binder : Binder) :
    embedding.inverse.binder (embedding.binder binder) = binder := by
  cases binder
  simp only [AtomRenaming.binder,Option.map_map,Function.comp_def,embedding.term_leftInverse,Option.map_id']

theorem AtomEmbedding.substitution_leftInverse (embedding : AtomEmbedding) (substitution : Substitution) :
    embedding.inverse.substitution (embedding.substitution substitution) = substitution := by
  simp only [AtomRenaming.substitution,List.map_map,Function.comp_def,embedding.term_leftInverse]
  exact List.map_eq_self_of _ _ (fun _ _ => rfl)

theorem AtomEmbedding.substitution_rightInverse (embedding : AtomEmbedding) (substitution : Substitution) :
    embedding.substitution (embedding.inverse.substitution substitution) = substitution := by
  simp only [AtomRenaming.substitution,List.map_map,Function.comp_def,embedding.term_rightInverse]
  exact List.map_eq_self_of _ _ (fun _ _ => rfl)

theorem Kinding.renameAtoms {program : Program} {context : Context} {term : Term} {kind : Kind}
    (kinded : Kinding program context term kind) (embedding : AtomEmbedding) :
    Kinding program (embedding.context context) (embedding.term term) kind := by
  apply kinded.map_atoms (target := embedding.context context) embedding.term (by
    intro term
    cases term <;> simp only [AtomRenaming.term,Term.mapChildren]) _
    (fun _ member => member) (fun _ member => member)
  intro atom occurs
  cases atom <;> try exact True.intro
  all_goals simp only [AtomRenaming.term]
  case parameter id kind =>
    obtain ⟨binder,member,sameId,sameKind⟩ := kinded.parameter_occurs occurs
    have mapped : embedding.binder binder ∈ (embedding.context context).binders := List.mem_map.mpr ⟨binder,member,rfl⟩
    simpa only [AtomRenaming.binder,AtomRenaming.term,sameId,sameKind] using Kinding.parameter (program := program) mapped
  case rigid id kind level =>
    exact .rigid ((embedding.rigid_bound id kind level context.universeLevel).mpr (kinded.rigid_level occurs))
  case «variable» id kind level =>
    exact .variable ((embedding.inference_bound id kind level context.universeLevel).mpr (kinded.variable_level occurs))
  case runtimeRegion => exact .runtimeRegion

/-- The inverse covers every value admitted by the target universe. This
is the contravariant domain fact needed by actual universal introduction. -/
theorem Kinding.unrenameAtoms {program : Program} {context : Context} {term : Term} {kind : Kind}
    (embedding : AtomEmbedding) (kinded : Kinding program (embedding.context context) term kind) :
    Kinding program context (embedding.inverse.term term) kind := by
  apply kinded.map_atoms (target := context) embedding.inverse.term (by
    intro term
    cases term <;> simp only [AtomRenaming.term,Term.mapChildren]) _
    (fun _ member => member) (fun _ member => member)
  intro atom occurs
  cases atom <;> try exact True.intro
  all_goals simp only [AtomRenaming.term]
  case parameter id kind =>
    obtain ⟨binder,member,sameId,sameKind⟩ := kinded.parameter_occurs occurs
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    change original.id = id at sameId
    change original.kind = kind at sameKind
    simpa only [sameId,sameKind] using Kinding.parameter (program := program) present
  case rigid id kind level =>
    have bounded :
        (embedding.rigid (embedding.inverse.rigid id kind level).1 kind (embedding.inverse.rigid id kind level).2).2 ≤
          embedding.levelMap context.universeLevel := by
      rw [embedding.rigid_right]
      exact kinded.rigid_level occurs
    exact .rigid ((embedding.rigid_bound _ _ _ _).mp bounded)
  case «variable» id kind level =>
    have bounded :
        (embedding.inference (embedding.inverse.inference id kind level).1 kind (embedding.inverse.inference id kind level).2).2 ≤
          embedding.levelMap context.universeLevel := by
      rw [embedding.inference_right]
      exact kinded.variable_level occurs
    exact .variable ((embedding.inference_bound _ _ _ _).mp bounded)
  case runtimeRegion => exact .runtimeRegion

end Glorious.Language
