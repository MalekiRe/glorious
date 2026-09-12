import GloriousLanguage.AtomInstantiation
import GloriousLanguage.LogicalUniverse

/-! Fresh generative atoms above the caller's universe can be specialized
to caller-kinded terms. Target values are fixed preimages: this is the
contravariant domain fact needed for universal introduction. -/
namespace Glorious.Language

structure FreshAtomSpecialization where
  cutoff : Nat
  rigid : Identity → Kind → Term
  rigid_kind : ∀ id kind, (rigid id kind).kind = kind

def FreshAtomSpecialization.term (specialization : FreshAtomSpecialization) : Term → Term
  | .rigid id kind level => if specialization.cutoff < level then specialization.rigid id kind else .rigid id kind level
  | .variable id kind level => if specialization.cutoff < level then .variable id kind specialization.cutoff else .variable id kind level
  | .tuple fields => .tuple (fields.map specialization.term)
  | .array a b => .array (specialization.term a) (specialization.term b)
  | .reference mode a b => .reference mode (specialization.term a) (specialization.term b)
  | .rawPointer mode a => .rawPointer mode (specialization.term a)
  | .nominal id arguments => .nominal id (arguments.map specialization.term)
  | .alias id arguments => .alias id (arguments.map specialization.term)
  | .callable id arguments => .callable id (arguments.map specialization.term)
  | .continuation a b c d q => .continuation (specialization.term a) (specialization.term b)
      (specialization.term c) (specialization.term d) q
  | .label a b c => .label (specialization.term a) (specialization.term b) (specialization.term c)
  | .environment a b residents => .environment (specialization.term a) (specialization.term b) (residents.map specialization.term)
  | .available a b residents => .available (specialization.term a) (specialization.term b) (residents.map specialization.term)
  | .bindings a b arguments => .bindings (specialization.term a) (specialization.term b) (arguments.map specialization.term)
  | .effect id arguments => .effect id (arguments.map specialization.term)
  | .row instances tails => .row (instances.map specialization.term) (tails.map specialization.term)
  | .projection trait member owners items kind => .projection trait member (owners.map specialization.term) (items.map specialization.term) kind
  | .constantTuple fields => .constantTuple (fields.map specialization.term)
  | .constantConstructor id arguments fields => .constantConstructor id (arguments.map specialization.term) (fields.map specialization.term)
  | term => term

theorem FreshAtomSpecialization.shape (specialization : FreshAtomSpecialization) : AtomHomomorphism specialization.term := by
  intro term
  cases term <;> simp only [FreshAtomSpecialization.term,Term.mapChildren]

theorem FreshAtomSpecialization.kind (specialization : FreshAtomSpecialization) (term : Term) :
    (specialization.term term).kind = term.kind := by
  cases term
  case rigid id kind level =>
    simp only [FreshAtomSpecialization.term]
    split
    · exact specialization.rigid_kind id kind
    · rfl
  case «variable» =>
    simp only [FreshAtomSpecialization.term]
    split <;> simp only [Term.kind]
  all_goals simp only [FreshAtomSpecialization.term,Term.kind]

theorem FreshAtomSpecialization.atoms_fixed {program : Program} {context : Context}
    (specialization : FreshAtomSpecialization) (level : context.universeLevel ≤ specialization.cutoff)
    {term : Term} {kind : Kind} (kinded : Kinding program context term kind) : term.AtomsFixed specialization.term := by
  intro atom occurs
  cases atom <;> try exact True.intro
  case rigid id kind atomLevel =>
    have bounded := kinded.rigid_level occurs
    simp only [FreshAtomSpecialization.term,if_neg (by omega : ¬specialization.cutoff < atomLevel)]
  case «variable» id kind atomLevel =>
    have bounded := kinded.variable_level occurs
    simp only [FreshAtomSpecialization.term,if_neg (by omega : ¬specialization.cutoff < atomLevel)]
  case runtimeRegion => simp only [FreshAtomSpecialization.term]

theorem FreshAtomSpecialization.fixed {program : Program} {context : Context}
    (specialization : FreshAtomSpecialization) (level : context.universeLevel = specialization.cutoff)
    {term : Term} {kind : Kind} (kinded : Kinding program context term kind) : specialization.term term = term := by
  apply specialization.shape.fixed_term
  · intro _ _ _
    simp only [FreshAtomSpecialization.term]
  · exact specialization.atoms_fixed (Nat.le_of_eq level) kinded

theorem ConstraintKinded.fresh_atoms_fixed {program : Program} {context : Context} {constraint : Constraint}
    (kinded : ConstraintKinded program context constraint) (specialization : FreshAtomSpecialization)
    (level : context.universeLevel ≤ specialization.cutoff) :
    ∀ term ∈ constraint.terms, term.AtomsFixed specialization.term := by
  intro term member
  obtain ⟨binders,typed⟩ := kinded.terms_kinded term member
  exact specialization.atoms_fixed (context := { context with binders := binders }) level typed

def FreshAtomSpecialization.Admitted (specialization : FreshAtomSpecialization) (program : Program) (context : Context) : Prop :=
  context.universeLevel = specialization.cutoff ∧ ∀ id kind, Kinding program context (specialization.rigid id kind) kind

theorem FreshAtomSpecialization.idempotent {program : Program} {context : Context}
    (specialization : FreshAtomSpecialization) (admitted : specialization.Admitted program context) (term : Term) :
    specialization.term (specialization.term term) = specialization.term term := by
  cases term
  case rigid id kind level =>
    have atom : specialization.term (.rigid id kind level) =
        if specialization.cutoff < level then specialization.rigid id kind else .rigid id kind level := by
      simp only [FreshAtomSpecialization.term]
    rw [atom]
    by_cases fresh : specialization.cutoff < level
    · simpa only [if_pos fresh] using specialization.fixed admitted.1 (admitted.2 id kind)
    · simp only [FreshAtomSpecialization.term,if_neg fresh]
  case «variable» id kind level =>
    by_cases fresh : specialization.cutoff < level
    · simp only [FreshAtomSpecialization.term,if_pos fresh,Nat.lt_irrefl,if_false]
    · simp only [FreshAtomSpecialization.term,if_neg fresh]
  all_goals simp only [FreshAtomSpecialization.term,List.map_map,Function.comp_def]
  all_goals try rfl
  all_goals congr 1
  all_goals first
  | exact specialization.idempotent admitted _
  | apply List.map_congr_left
    intro child _
    exact specialization.idempotent admitted child
termination_by term

theorem Kinding.specializeFresh {program : Program} {context : Context} {inspectionLevel : Nat} {term : Term} {kind : Kind}
    (kinded : Kinding program { context with universeLevel := inspectionLevel } term kind)
    (specialization : FreshAtomSpecialization) (admitted : specialization.Admitted program context) :
    Kinding program context (specialization.term term) kind := by
  have cutoff := admitted.1
  apply kinded.map_atoms (target := context) specialization.term specialization.shape _ (fun _ member => member) (fun _ member => member)
  intro atom occurs
  cases atom <;> try exact True.intro
  case parameter id kind =>
    obtain ⟨binder,member,sameId,sameKind⟩ := kinded.parameter_occurs occurs
    simpa only [FreshAtomSpecialization.term,sameId,sameKind] using Kinding.parameter (program := program) (context := context) member
  case rigid id kind level =>
    simp only [FreshAtomSpecialization.term]
    split
    · exact admitted.2 id kind
    · exact .rigid (by omega)
  case «variable» id kind level =>
    simp only [FreshAtomSpecialization.term]
    split
    · exact .variable (Nat.le_of_eq admitted.1.symm)
    · exact .variable (by omega)
  case runtimeRegion id =>
    simpa only [FreshAtomSpecialization.term] using Kinding.runtimeRegion (program := program) (context := context) (id := id)

/-- Every admitted target argument is literally an unchanged source
argument. The pullback is derived from kinding and old-level fixedness,
rather than assumed as a universal proof-transport premise. -/
theorem FreshAtomSpecialization.target_preimage {program : Program} {context : Context}
    (specialization : FreshAtomSpecialization) (admitted : specialization.Admitted program context)
    {inspectionLevel : Nat} (higher : context.universeLevel ≤ inspectionLevel)
    {term : Term} {kind : Kind} (kinded : Kinding program context term kind) :
    Kinding program { context with universeLevel := inspectionLevel } term kind ∧ specialization.term term = term :=
  ⟨kinded.raiseUniverse higher,specialization.fixed admitted.1 kinded⟩

theorem FreshAtomSpecialization.source_fixed {program : Program} (valid : ProgramWellFormed program)
    (specialization : FreshAtomSpecialization) : program.AtomsFixed specialization.term := by
  intro declaration declared term member
  obtain ⟨context,level,kinded⟩ := valid.terms_kinded declared term member
  exact specialization.atoms_fixed (by omega) kinded

def FreshAtomSpecialization.ofSubstitution (cutoff : Nat) (substitution : Substitution) : FreshAtomSpecialization where
  cutoff := cutoff
  rigid := fun id kind => match substitution.get id with
    | some value => if value.kind = kind then value else .rigid id kind cutoff
    | none => .rigid id kind cutoff
  rigid_kind := by
    intro id kind
    cases found : substitution.get id <;> simp only
    · rfl
    · split
      · assumption
      · rfl

theorem FreshAtomSpecialization.ofSubstitution_admitted {program : Program} {context : Context} {substitution : Substitution}
    (kinded : ∀ id value, substitution.get id = some value → Kinding program context value value.kind) :
    (ofSubstitution context.universeLevel substitution).Admitted program context := by
  refine ⟨rfl,?_⟩
  intro id kind
  simp only [ofSubstitution]
  cases found : substitution.get id with
  | none => exact .rigid (Nat.le_refl _)
  | some value =>
    simp only
    split
    · rename_i same
      simpa only [same] using kinded id value found
    · exact .rigid (Nat.le_refl _)

theorem FreshAtomSpecialization.ofSubstitution_rigid {cutoff id level : Nat} {kind : Kind}
    {substitution : Substitution} {value : Term}
    (fresh : cutoff < level) (found : substitution.get id = some value) (sameKind : value.kind = kind) :
    (ofSubstitution cutoff substitution).term (.rigid id kind level) = value := by
  simp only [FreshAtomSpecialization.term,ofSubstitution,if_pos fresh,found,if_pos sameKind]

end Glorious.Language
