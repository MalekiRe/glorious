import GloriousLanguage.RuntimeSupport
import GloriousLanguage.CapabilityModels
import GloriousLanguage.DefinitionalAdmission
import GloriousLanguage.PredicateHygiene
import GloriousLanguage.StaticAtomTransport

/-! Static judgments transport along a genuine runtime-region permutation.
The permutation supplies only fresh-name mathematics, never an assumed
typing, capability, layout or declaration-equivalence conclusion. -/
namespace Glorious.Language

structure RegionPermutation where
  rename : Identity → Identity
  involutive : ∀ id, rename (rename id) = id

def RegionPermutation.term (permutation : RegionPermutation) : Term → Term :=
  Term.renameRuntimeRegions permutation.rename

theorem RegionPermutation.term_def (permutation : RegionPermutation) (term : Term) :
    permutation.term term = term.renameRuntimeRegions permutation.rename := rfl

def RegionPermutation.substitution (permutation : RegionPermutation) (substitution : Substitution) : Substitution :=
  substitution.map (fun (id,value) => (id,permutation.term value))

def RegionPermutation.binder (permutation : RegionPermutation) (binder : Binder) : Binder :=
  { binder with defaultValue := binder.defaultValue.map permutation.term }

def RegionPermutation.constraint (permutation : RegionPermutation) : Constraint → Constraint :=
  Constraint.mapTerms permutation.term

def RegionPermutation.context (permutation : RegionPermutation) (context : Context) : Context :=
  { context with
    binders := context.binders.map permutation.binder
    assumptions := context.assumptions.map permutation.constraint }

/-- Runtime relocation is the universe-preserving instance of the shared
concrete atom action. It fixes rigid universals and inference variables. -/
def RegionPermutation.embedding (permutation : RegionPermutation) : AtomEmbedding where
  region := permutation.rename
  rigid := fun id _ level => (id,level)
  inference := fun id _ level => (id,level)
  inverse := ⟨permutation.rename,fun id _ level => (id,level),fun id _ level => (id,level)⟩
  levelMap := id
  region_left := permutation.involutive
  region_right := permutation.involutive
  rigid_left := by intros; rfl
  rigid_right := by intros; rfl
  inference_left := by intros; rfl
  inference_right := by intros; rfl
  rigid_bound := by intros; rfl
  inference_bound := by intros; rfl

theorem RegionPermutation.embedding_term (permutation : RegionPermutation) (term : Term) :
    permutation.embedding.term term = permutation.term term := by
  cases term <;> simp only [RegionPermutation.embedding,AtomRenaming.term,RegionPermutation.term,Term.renameRuntimeRegions]
  all_goals try rfl
  all_goals congr 1
  all_goals first
  | exact RegionPermutation.embedding_term permutation _
  | apply List.map_congr_left
    intro child _
    exact permutation.embedding_term child
termination_by term

theorem RegionPermutation.embedding_action (permutation : RegionPermutation) :
    permutation.embedding.term = permutation.term := funext permutation.embedding_term

theorem RegionPermutation.embedding_binder (permutation : RegionPermutation) (binder : Binder) :
    permutation.embedding.binder binder = permutation.binder binder := by
  simp only [AtomRenaming.binder,RegionPermutation.binder,permutation.embedding_action]

theorem RegionPermutation.embedding_constraint (permutation : RegionPermutation) (constraint : Constraint) :
    permutation.embedding.constraint constraint = permutation.constraint constraint := by
  simp only [AtomRenaming.constraint,RegionPermutation.constraint,permutation.embedding_action]

theorem RegionPermutation.embedding_substitution (permutation : RegionPermutation) (substitution : Substitution) :
    permutation.embedding.substitution substitution = permutation.substitution substitution := by
  simp only [AtomRenaming.substitution,RegionPermutation.substitution,permutation.embedding_action]

theorem RegionPermutation.embedding_context (permutation : RegionPermutation) (context : Context) :
    permutation.embedding.context context = permutation.context context := by
  have binders := funext permutation.embedding_binder
  have constraints := funext permutation.embedding_constraint
  simp only [AtomEmbedding.context,RegionPermutation.context,binders,constraints]
  rfl

theorem RegionPermutation.term_involutive (permutation : RegionPermutation) (term : Term) :
    permutation.term (permutation.term term) = term :=
  term.renameRuntimeRegions_involutive permutation.rename permutation.involutive

theorem RegionPermutation.term_injective (permutation : RegionPermutation) : Function.Injective permutation.term :=
  Term.renameRuntimeRegions_injective permutation.rename permutation.involutive

theorem RegionPermutation.term_kind (permutation : RegionPermutation) (term : Term) :
    (permutation.term term).kind = term.kind := by
  cases term <;> simp only [RegionPermutation.term,Term.renameRuntimeRegions,Term.kind]

theorem RegionPermutation.lexical_term (permutation : RegionPermutation) {term : Term}
    (lexical : term.Lexical) : permutation.term term = term := by
  have identity : permutation.term term = term.renameRuntimeRegions id :=
    term.renameRuntimeRegions_congr permutation.rename id (fun id occurs => False.elim (lexical.1 id occurs))
  exact identity.trans term.renameRuntimeRegions_id

theorem RegionPermutation.embedding_fixes (permutation : RegionPermutation) {program : Program}
    (valid : ProgramWellFormed program) : permutation.embedding.Fixes program := by
  intro declaration member term present
  rw [permutation.embedding_term]
  exact permutation.lexical_term (valid.lexical member term present)

theorem RegionPermutation.term_substitute (permutation : RegionPermutation) (substitution : Substitution) (term : Term) :
    permutation.term (term.substitute substitution) =
      (permutation.term term).substitute (permutation.substitution substitution) := by
  simpa only [RegionPermutation.term,RegionPermutation.substitution] using
    term.renameRuntimeRegions_substitute permutation.rename substitution

theorem RegionPermutation.substitution_involutive (permutation : RegionPermutation) (substitution : Substitution) :
    permutation.substitution (permutation.substitution substitution) = substitution := by
  simp only [RegionPermutation.substitution,List.map_map,Function.comp_def,permutation.term_involutive]
  exact List.map_eq_self_of _ _ (fun _ _ => rfl)

theorem RegionPermutation.substitution_filter (permutation : RegionPermutation) (substitution : Substitution)
    (keep : Identity → Bool) :
    permutation.substitution (substitution.filter (fun entry => keep entry.1)) =
      (permutation.substitution substitution).filter (fun entry => keep entry.1) := by
  simp only [RegionPermutation.substitution,List.filter_map,Function.comp_def]

theorem RegionPermutation.binder_involutive (permutation : RegionPermutation) (binder : Binder) :
    permutation.binder (permutation.binder binder) = binder := by
  cases binder
  simp only [RegionPermutation.binder,Option.map_map,Function.comp_def,permutation.term_involutive,Option.map_id']

theorem RegionPermutation.constraint_involutive (permutation : RegionPermutation) (constraint : Constraint) :
    permutation.constraint (permutation.constraint constraint) = constraint := by
  cases constraint <;>
    simp only [RegionPermutation.constraint,Constraint.mapTerms,permutation.term_involutive,
      List.map_map,Function.comp_def,Option.map_map,Option.map_id']
  all_goals try rfl
  all_goals
    congr 1
    all_goals first
    | exact List.map_eq_self_of _ _ (fun _ _ => rfl)
    | exact List.map_eq_self_of _ _ (fun _ _ => permutation.term_involutive _)
    | exact List.map_eq_self_of _ _ (fun _ _ => permutation.binder_involutive _)
    | exact List.map_eq_self_of _ _ (fun _ _ => permutation.constraint_involutive _)
termination_by constraint

theorem RegionPermutation.context_involutive (permutation : RegionPermutation) (context : Context) :
    permutation.context (permutation.context context) = context := by
  cases context
  simp only [RegionPermutation.context,List.map_map,Function.comp_def,
    permutation.binder_involutive,permutation.constraint_involutive,List.map_id']

theorem RegionPermutation.constraint_substitute (permutation : RegionPermutation)
    (substitution : Substitution) (constraint : Constraint) :
    permutation.constraint (constraint.substitute substitution) =
      (permutation.constraint constraint).substitute (permutation.substitution substitution) := by
  simpa only [RegionPermutation.constraint,RegionPermutation.term,RegionPermutation.substitution] using
    constraint.renameRuntimeRegions_substitute permutation.rename substitution

theorem RegionPermutation.parameter_origin (permutation : RegionPermutation) {term : Term} {id : Identity} {kind : Kind}
    (same : permutation.term term = .parameter id kind) : term = .parameter id kind := by
  cases term <;> simp only [RegionPermutation.term,Term.renameRuntimeRegions] at same <;> cases same <;> rfl

theorem RegionPermutation.parameter_occurs (permutation : RegionPermutation) {term : Term} {id : Identity} {kind : Kind}
    (occurs : Occurs (.parameter id kind) (permutation.term term)) : Occurs (.parameter id kind) term := by
  obtain ⟨original,nested,same⟩ := Term.renameRuntimeRegions_occurs_preimage permutation.rename occurs
  have originalEq := permutation.parameter_origin same
  exact originalEq ▸ nested

theorem RegionPermutation.substitutes (permutation : RegionPermutation) {substitution : Substitution} {before after : Term}
    (related : Substitutes substitution before after) :
    Substitutes (permutation.substitution substitution) (permutation.term before) (permutation.term after) := by
  refine ⟨by simpa only [permutation.term_kind] using related.1,?_,?_⟩
  · rw [related.2.1,permutation.term_substitute]
  · intro id kind value occurs found
    change Table.get (substitution.map (fun (id,term) => (id,permutation.term term))) id = some value at found
    rw [Table.get_map_values] at found
    obtain ⟨previous,selected,rfl⟩ := Option.map_eq_some_iff.mp found
    simpa only [permutation.term_kind] using related.2.2 id kind previous (permutation.parameter_occurs occurs) selected

theorem RegionPermutation.substitutes_self (permutation : RegionPermutation) {substitution : Substitution} {term : Term}
    (related : Substitutes substitution term (term.substitute substitution)) :
    Substitutes (permutation.substitution substitution) (permutation.term term)
      ((permutation.term term).substitute (permutation.substitution substitution)) := by
  simpa only [permutation.term_substitute] using permutation.substitutes related

theorem RegionPermutation.substitutes_lexical (permutation : RegionPermutation) {substitution : Substitution} {before after : Term}
    (lexical : before.Lexical) (related : Substitutes substitution before after) :
    Substitutes (permutation.substitution substitution) before (permutation.term after) := by
  simpa only [permutation.lexical_term lexical] using permutation.substitutes related

theorem RegionPermutation.substitutes_list (permutation : RegionPermutation) {substitution : Substitution} {before after : List Term}
    (related : ListRel (Substitutes substitution) before after) :
    ListRel (Substitutes (permutation.substitution substitution)) (before.map permutation.term) (after.map permutation.term) := by
  induction related with
  | nil => exact .nil
  | cons first _ ih => exact .cons (permutation.substitutes first) ih

theorem RegionPermutation.substitutes_lexical_list (permutation : RegionPermutation) {substitution : Substitution}
    {before after : List Term} (lexical : ∀ term ∈ before, term.Lexical)
    (related : ListRel (Substitutes substitution) before after) :
    ListRel (Substitutes (permutation.substitution substitution)) before (after.map permutation.term) := by
  have unchanged : before.map permutation.term = before :=
    List.map_eq_self_of _ _ (fun term member => permutation.lexical_term (lexical term member))
  simpa only [unchanged] using permutation.substitutes_list related

theorem RegionPermutation.constraint_admissible (permutation : RegionPermutation)
    {substitution : Substitution} {constraint : Constraint}
    (admissible : constraint.SubstitutionAdmissible substitution) :
    (permutation.constraint constraint).SubstitutionAdmissible (permutation.substitution substitution) := by
  cases constraint <;>
    simp only [RegionPermutation.constraint,Constraint.mapTerms,Constraint.SubstitutionAdmissible] at admissible ⊢
  all_goals try exact ⟨permutation.substitutes_self admissible.1,permutation.substitutes_self admissible.2⟩
  case use => exact permutation.substitutes_self admissible
  all_goals try {
    intro term member
    try simp only [← List.map_cons] at member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    exact permutation.substitutes_self (admissible original present) }
  case quantified binders requirements =>
    have restricted :
        (permutation.substitution substitution).filter
          (fun entry => !(binders.any (fun binder => binder.id == entry.1))) =
        permutation.substitution (substitution.filter
          (fun entry => !(binders.any (fun binder => binder.id == entry.1)))) :=
      (permutation.substitution_filter substitution
        (fun id => !(binders.any (fun binder => binder.id == id)))).symm
    simp only [List.any_map,Function.comp_def,restricted]
    refine ⟨?_,?_⟩
    · intro index binder member value found
      simp only [List.getElem?_map] at member
      obtain ⟨original,present,rfl⟩ := Option.map_eq_some_iff.mp member
      obtain ⟨oldValue,selected,rfl⟩ := Option.map_eq_some_iff.mp found
      have mapped := permutation.substitutes_self (admissible.1 index original present oldValue selected)
      rw [permutation.substitution_filter substitution
        (fun id => !((binders.take index).any (fun binder => binder.id == id)))] at mapped
      simpa only [← List.map_take,List.any_map,Function.comp_def] using mapped
    · intro requirement member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact permutation.constraint_admissible (admissible.2 original present)
termination_by constraint

theorem RegionPermutation.substitute_constraint (permutation : RegionPermutation)
    {substitution : Substitution} {before after : Constraint} (related : SubstituteConstraint substitution before after) :
    SubstituteConstraint (permutation.substitution substitution) (permutation.constraint before) (permutation.constraint after) := by
  refine ⟨permutation.constraint_admissible related.1,?_⟩
  rw [related.2,permutation.constraint_substitute]

theorem Instantiates.permute {binders : List Binder} {arguments : List Term} {substitution : Substitution}
    (instantiated : Instantiates binders arguments substitution) (permutation : RegionPermutation) :
    Instantiates binders (arguments.map permutation.term) (permutation.substitution substitution) := by
  simpa only [permutation.embedding_action,permutation.embedding_substitution] using
    instantiated.renameAtoms permutation.embedding.toAtomRenaming

theorem Instantiates.permute_binders {binders : List Binder} {arguments : List Term} {substitution : Substitution}
    (instantiated : Instantiates binders arguments substitution) (permutation : RegionPermutation) :
    Instantiates (binders.map permutation.binder) arguments substitution := by
  have binderMap := funext permutation.embedding_binder
  simpa only [binderMap] using instantiated.renameBinders permutation.embedding.toAtomRenaming

theorem CallableFields.permute {program : Program} (valid : ProgramWellFormed program)
    {id : DeclId} {arguments fields : List Term} (declared : CallableFields program id arguments fields)
    (permutation : RegionPermutation) :
    CallableFields program id (arguments.map permutation.term) (fields.map permutation.term) := by
  simpa only [permutation.embedding_action] using
    declared.renameAtoms permutation.embedding.toAtomRenaming (permutation.embedding_fixes valid)

def RegionPermutation.assignment (permutation : RegionPermutation) (assignment : Term → Option Principal) :
    Term → Option Principal := fun term => assignment (permutation.term term)

theorem RegionPermutation.embedding_assignment (permutation : RegionPermutation)
    (assignment : Term → Option Principal) : permutation.embedding.assignment assignment = permutation.assignment assignment := by
  have inverse : permutation.embedding.inverse = permutation.embedding.toAtomRenaming := rfl
  funext term
  simp only [AtomEmbedding.assignment,RegionPermutation.assignment,inverse,permutation.embedding_term]

theorem RegionPermutation.assignment_at (permutation : RegionPermutation)
    (assignment : Term → Option Principal) (term : Term) :
    permutation.assignment assignment (permutation.term term) = assignment term := by
  simp only [RegionPermutation.assignment,permutation.term_involutive]

theorem RegionPermutation.assignment_fields (permutation : RegionPermutation)
    {assignment : Term → Option Principal} {fields : List Term} {principals : List Principal}
    (related : ListRel (fun field principal => assignment field = some principal) fields principals) :
    ListRel (fun field principal => permutation.assignment assignment field = some principal)
      (fields.map permutation.term) principals := by
  induction related with
  | nil => exact .nil
  | cons first _ ih => exact .cons (by simpa only [permutation.assignment_at] using first) ih


theorem CapabilityEquation.permute {program : Program} (valid : ProgramWellFormed program)
    {assignment : Term → Option Principal} {term : Term} {principal : Principal}
    (equation : CapabilityEquation program assignment term principal) (permutation : RegionPermutation) :
    CapabilityEquation program (permutation.assignment assignment) (permutation.term term) principal := by
  simpa only [permutation.embedding_assignment,permutation.embedding_term] using
    equation.renameAtoms permutation.embedding (permutation.embedding_fixes valid)

theorem Kinding.permute {program : Program} {context : Context} {term : Term} {kind : Kind}
    (typed : Kinding program context term kind) (permutation : RegionPermutation) :
    Kinding program (permutation.context context) (permutation.term term) kind := by
  simpa only [permutation.embedding_context,permutation.embedding_term] using
    typed.renameAtoms permutation.embedding

theorem RegionPermutation.term_children (permutation : RegionPermutation) (term : Term) :
    (permutation.term term).children = term.children.map permutation.term := by
  cases term <;> simp only [RegionPermutation.term,Term.renameRuntimeRegions,Term.children,
    List.map_cons,List.map_nil,List.map_append]

theorem RegionPermutation.occurs (permutation : RegionPermutation) {part term : Term} (occurs : Occurs part term) :
    Occurs (permutation.term part) (permutation.term term) := by
  induction occurs with
  | here => exact .here
  | child member _ ih =>
    exact .child (by rw [permutation.term_children]; exact List.mem_map.mpr ⟨_,member,rfl⟩) ih

theorem Term.Scoped.permute {scope : LexicalScope} {term : Term} (admitted : term.Scoped scope)
    (permutation : RegionPermutation) : (permutation.term term).Scoped scope := by
  constructor
  · intro id occurs
    have original := permutation.occurs occurs
    rw [permutation.term_involutive] at original
    exact admitted.1 id (by simpa only [RegionPermutation.term,Term.renameRuntimeRegions] using original)
  · intro id occurs
    have original := permutation.occurs occurs
    rw [permutation.term_involutive] at original
    exact admitted.2 id (by simpa only [RegionPermutation.term,Term.renameRuntimeRegions] using original)

theorem Term.ScopeClosed.permute {term : Term} (closed : term.ScopeClosed)
    (permutation : RegionPermutation) : (permutation.term term).ScopeClosed :=
  Term.Scoped.permute closed permutation

theorem RegionPermutation.term_head (permutation : RegionPermutation) (term : Term) :
    (permutation.term term).mapChildren (fun _ => .unit) = permutation.term (term.mapChildren (fun _ => .unit)) := by
  cases term <;> simp only [RegionPermutation.term,Term.renameRuntimeRegions,Term.mapChildren,
    List.map_map,Function.comp_def]
  all_goals try rfl
  all_goals congr 1
  all_goals apply List.map_congr_left
  all_goals intro child _
  all_goals simp only [Term.renameRuntimeRegions]

theorem SameHead.permute {a b : Term} (same : SameHead a b) (permutation : RegionPermutation) :
    SameHead (permutation.term a) (permutation.term b) := by
  unfold SameHead at same ⊢
  rw [permutation.term_head,permutation.term_head,same]

theorem RegionPermutation.lexical_binder (permutation : RegionPermutation) {binder : Binder}
    (lexical : ∀ term, binder.defaultValue = some term → term.Lexical) : permutation.binder binder = binder := by
  cases binder with
  | mk id name kind defaultValue =>
      cases defaultValue with
      | none => rfl
      | some term => simp only [RegionPermutation.binder,Option.map,permutation.lexical_term (lexical term rfl)]

theorem RegionPermutation.lexical_constraint (permutation : RegionPermutation) {constraint : Constraint}
    (lexical : ∀ term ∈ constraint.terms, term.Lexical) : permutation.constraint constraint = constraint := by
  cases constraint <;> simp only [RegionPermutation.constraint,Constraint.mapTerms]
  all_goals try {
    congr 1
    all_goals first
    | exact permutation.lexical_term (lexical _ (by simp [Constraint.terms]))
    | exact List.map_eq_self_of _ _ (fun term member => permutation.lexical_term (lexical term (by
        simp [Constraint.terms,member]))) }
  case quantified binders requirements =>
    congr 1
    · apply List.map_eq_self_of
      intro binder member
      apply permutation.lexical_binder
      intro term found
      exact lexical term (by
        simp only [Constraint.terms,List.mem_append,List.mem_flatMap]
        exact Or.inl ⟨binder,member,by simp [found]⟩)
    · apply List.map_eq_self_of
      intro requirement member
      exact permutation.lexical_constraint (fun term present => lexical term (by
        simp only [Constraint.terms,List.mem_append,List.mem_flatMap]
        exact Or.inr ⟨requirement,member,present⟩))
termination_by constraint

theorem RegionPermutation.substitute_lexical_constraint (permutation : RegionPermutation)
    {substitution : Substitution} {before after : Constraint} (lexical : ∀ term ∈ before.terms, term.Lexical)
    (related : SubstituteConstraint substitution before after) :
    SubstituteConstraint (permutation.substitution substitution) before (permutation.constraint after) := by
  simpa only [permutation.lexical_constraint lexical] using permutation.substitute_constraint related

theorem RegionPermutation.substitute_lexical_constraints (permutation : RegionPermutation)
    {substitution : Substitution} {before after : List Constraint}
    (lexical : ∀ constraint ∈ before, ∀ term ∈ constraint.terms, term.Lexical)
    (related : ListRel (SubstituteConstraint substitution) before after) :
    ListRel (SubstituteConstraint (permutation.substitution substitution)) before (after.map permutation.constraint) := by
  induction related with
  | nil => exact .nil
  | cons first _ ih =>
      exact .cons (permutation.substitute_lexical_constraint (lexical _ List.mem_cons_self) first)
        (ih (fun constraint member => lexical constraint (List.mem_cons_of_mem _ member)))



theorem RegionPermutation.lexical_terms (permutation : RegionPermutation) {terms : List Term}
    (lexical : ∀ term ∈ terms, term.Lexical) : terms.map permutation.term = terms :=
  List.map_eq_self_of _ _ (fun term member => permutation.lexical_term (lexical term member))

theorem RegionPermutation.lookup_default (permutation : RegionPermutation)
    (substitution : Substitution) (id : Identity) (kind : Kind) :
    ((permutation.substitution substitution).get id).getD (.parameter id kind) =
      permutation.term ((substitution.get id).getD (.parameter id kind)) := by
  rw [RegionPermutation.substitution,Table.get_map_values]
  cases substitution.get id <;> simp only [Option.map,Option.getD,RegionPermutation.term,Term.renameRuntimeRegions]

theorem RegionPermutation.list_at (permutation : RegionPermutation)
    {relation : Term → Term → Prop} {left right : List Term}
    (related : ∀ (index : Nat) first second, left[index]? = some first → right[index]? = some second →
      relation (permutation.term first) (permutation.term second)) :
    ∀ (index : Nat) first second, (left.map permutation.term)[index]? = some first →
      (right.map permutation.term)[index]? = some second → relation first second := by
  intro index first second leftAt rightAt
  rw [List.getElem?_map] at leftAt rightAt
  obtain ⟨a,atA,rfl⟩ := Option.map_eq_some_iff.mp leftAt
  obtain ⟨b,atB,rfl⟩ := Option.map_eq_some_iff.mp rightAt
  exact related index a b atA atB

theorem RegionPermutation.children_at (permutation : RegionPermutation)
    {relation : Term → Term → Prop} {left right : Term}
    (related : ∀ (index : Nat) first second, left.children[index]? = some first →
      right.children[index]? = some second → relation (permutation.term first) (permutation.term second)) :
    ∀ (index : Nat) first second, (permutation.term left).children[index]? = some first →
      (permutation.term right).children[index]? = some second → relation first second := by
  rw [permutation.term_children,permutation.term_children]
  exact permutation.list_at related

theorem RegionPermutation.structuralHead (permutation : RegionPermutation) {term : Term}
    (structural : term.StructuralHead) : (permutation.term term).StructuralHead := by
  cases term <;> simp only [RegionPermutation.term,Term.renameRuntimeRegions,Term.StructuralHead] at structural ⊢
  all_goals trivial

theorem RegionPermutation.implementation_binder (permutation : RegionPermutation)
    {program : Program} (valid : ProgramWellFormed program) {implementation : ImplDefinition}
    (member : Definition.implementation implementation ∈ program.declarations)
    {binder : Binder} (present : binder ∈ implementation.generics) :
    permutation.binder binder = binder := by
  apply permutation.lexical_binder
  intro term found
  exact valid.lexical member term (by
    simp only [Definition.terms,List.mem_append,List.mem_flatMap]
    exact Or.inr ⟨binder,present,by simp [found]⟩)

theorem RegionPermutation.implementation_context (permutation : RegionPermutation)
    {program : Program} (valid : ProgramWellFormed program) {implementation : ImplDefinition}
    (member : Definition.implementation implementation ∈ program.declarations) :
    permutation.context implementation.context = implementation.context := by
  have binders : implementation.generics.map permutation.binder = implementation.generics :=
    List.map_eq_self_of _ _ (fun binder present => permutation.implementation_binder valid member present)
  have requirements : implementation.requirements.map permutation.constraint = implementation.requirements := by
    apply List.map_eq_self_of
    intro constraint present
    exact permutation.lexical_constraint (fun term nested => valid.lexical member term (by
      simp only [Definition.terms,List.mem_append,List.mem_flatMap]
      exact Or.inl (Or.inr ⟨constraint,present,nested⟩)))
  simp only [RegionPermutation.context,ImplDefinition.context,binders,requirements]

theorem Entails.permute {program : Program} (valid : ProgramWellFormed program) {context : Context}
    {constraint : Constraint} (entailed : Entails program context constraint) (permutation : RegionPermutation) :
    Entails program (permutation.context context) (permutation.constraint constraint) := by
  simpa only [permutation.embedding_context,permutation.embedding_constraint] using
    entailed.renameAtoms permutation.embedding (permutation.embedding_fixes valid)

theorem CapabilityEvidence.permute {program : Program} (valid : ProgramWellFormed program) {context : Context}
    {type : Term} {principal : Principal} (evidence : CapabilityEvidence program context type principal)
    (permutation : RegionPermutation) :
    CapabilityEvidence program (permutation.context context) (permutation.term type) principal := by
  have transported := evidence.entails.permute valid permutation
  simp only [RegionPermutation.constraint,Constraint.mapTerms] at transported
  exact transported.capabilityEvidence

theorem CapabilitySupport.permute {program : Program} (valid : ProgramWellFormed program)
    {type : Term} {principal : Principal} (supported : CapabilitySupport program type principal)
    (permutation : RegionPermutation) : CapabilitySupport program (permutation.term type) principal := by
  obtain ⟨context,closed,evidence⟩ := supported
  exact ⟨permutation.context context,by simp [RegionPermutation.context,closed],evidence.permute valid permutation⟩

/-- Runtime renaming preserves the complete semantic maximum. Its proof
uses the finite logical/coinductive evidence in both directions, not the
superseded claim that every semantic principal has a raw structural equation. -/
theorem PrincipalOf.permute {program : Program} (valid : ProgramWellFormed program)
    {type : Term} {principal : Principal} (capability : PrincipalOf program type principal)
    (permutation : RegionPermutation) : PrincipalOf program (permutation.term type) principal := by
  refine ⟨capability.1.permute valid permutation,?_⟩
  intro other evidence
  have original := evidence.permute valid permutation
  rw [permutation.term_involutive] at original
  exact capability.2 other original

theorem CapabilitySolution.permute {program : Program} (valid : ProgramWellFormed program)
    {assignment : Term → Option Principal} (solution : CapabilitySolution program assignment)
    (permutation : RegionPermutation) : CapabilitySolution program (permutation.assignment assignment) := by
  intro type principal
  constructor
  · intro found
    have transformed := ((solution (permutation.term type) principal).mp found).permute valid permutation
    simpa only [permutation.term_involutive] using transformed
  · intro capability
    exact (solution (permutation.term type) principal).mpr (capability.permute valid permutation)

def CapabilityModel.permute {program : Program} (valid : ProgramWellFormed program)
    (model : CapabilityModel program) (permutation : RegionPermutation) : CapabilityModel program where
  principal := permutation.assignment model.principal
  equations := model.equations.permute valid permutation

theorem Equal.permute {program : Program} (valid : ProgramWellFormed program) {context : Context}
    {a b : Term} (equal : Equal program context a b) (permutation : RegionPermutation) :
    Equal program (permutation.context context) (permutation.term a) (permutation.term b) := by
  have transported := (Entails.equality equal).permute valid permutation
  simp only [RegionPermutation.constraint,Constraint.mapTerms] at transported
  exact .entailed transported

theorem TypeOutlives.permute {program : Program} (valid : ProgramWellFormed program) {context : Context}
    {type region : Term} (outlives : TypeOutlives program context type region) (permutation : RegionPermutation) :
    TypeOutlives program (permutation.context context) (permutation.term type) (permutation.term region) := by
  have transported := (Entails.typeOutlives outlives).permute valid permutation
  simp only [RegionPermutation.constraint,Constraint.mapTerms] at transported
  exact .entailed transported

theorem RowSubset.permute {program : Program} (valid : ProgramWellFormed program) {context : Context}
    {required allowed : Term} (subset : RowSubset program context required allowed) (permutation : RegionPermutation) :
    RowSubset program (permutation.context context) (permutation.term required) (permutation.term allowed) := by
  have transported := (Entails.rows subset).permute valid permutation
  simp only [RegionPermutation.constraint,Constraint.mapTerms] at transported
  exact .entailed transported

theorem EntailsSubstitution.permute {program : Program} (valid : ProgramWellFormed program) {context : Context}
    {substitution : Substitution} {constraint : Constraint}
    (entailed : EntailsSubstitution program context substitution constraint) (permutation : RegionPermutation) :
    EntailsSubstitution program (permutation.context context) (permutation.substitution substitution)
      (permutation.constraint constraint) := by
  cases entailed with
  | instantiated substituted holds => exact .instantiated (permutation.substitute_constraint substituted) (holds.permute valid permutation)

theorem ConstraintsHold.permute {program : Program} (valid : ProgramWellFormed program) {context : Context}
    {substitution : Substitution} {requirements : List Constraint}
    (held : ConstraintsHold program context substitution requirements)
    (lexical : ∀ constraint ∈ requirements, ∀ term ∈ constraint.terms, term.Lexical)
    (permutation : RegionPermutation) :
    ConstraintsHold program (permutation.context context) (permutation.substitution substitution) requirements := by
  intro constraint member
  obtain ⟨instantiated,substituted,entailed⟩ := held constraint member
  exact ⟨permutation.constraint instantiated,
    permutation.substitute_lexical_constraint (lexical constraint member) substituted,
    entailed.permute valid permutation⟩

theorem RegionPermutation.substitutes_variants (permutation : RegionPermutation) {substitution : Substitution}
    {variants : List VariantDefinition} {types : List (List Term)}
    (related : ListRel (fun variant types => ListRel (Substitutes substitution) (variant.fields.map (·.type)) types) variants types)
    (lexical : ∀ variant ∈ variants, ∀ field ∈ variant.fields, field.type.Lexical) :
    ListRel (fun variant types => ListRel (Substitutes (permutation.substitution substitution)) (variant.fields.map (·.type)) types)
      variants (types.map (List.map permutation.term)) := by
  induction related with
  | nil => exact .nil
  | cons first _ ih =>
      exact .cons (permutation.substitutes_lexical_list (by
        intro term present
        obtain ⟨field,member,rfl⟩ := List.mem_map.mp present
        exact lexical _ List.mem_cons_self field member) first)
        (ih (fun variant member => lexical variant (List.mem_cons_of_mem _ member)))

theorem LayoutOf.permute {program : Program} (valid : ProgramWellFormed program) {context : Context}
    {type : Term} {layout : Layout} (located : LayoutOf program context type layout) (permutation : RegionPermutation) :
    LayoutOf program (permutation.context context) (permutation.term type) layout := by
  refine LayoutOf.rec
    (motive_1 := fun type layout _ => LayoutOf program (permutation.context context) (permutation.term type) layout)
    (motive_2 := fun types layout _ => FieldsHaveLayout program (permutation.context context) (types.map permutation.term) layout)
    (motive_3 := fun type layout _ => CCompatible program (permutation.context context) (permutation.term type) layout)
    (motive_4 := fun types layouts _ => ListRel (LayoutOf program (permutation.context context)) (types.map permutation.term) layouts)
    (motive_5 := fun types layouts _ => ListRel (FieldsHaveLayout program (permutation.context context))
      (types.map (List.map permutation.term)) layouts)
    (motive_6 := fun types layouts _ => ListRel (CCompatible program (permutation.context context)) (types.map permutation.term) layouts)
    ?unit ?scalar ?reference ?pointer ?tuple ?callable ?continuation ?label ?available ?bindings ?environment
    ?array ?nominal ?transparent ?cRepresentation ?alias ?fields ?cScalar ?cPointer ?record ?enumeration
    ?cTransparent ?cAlias ?nil ?cons ?variantNil ?variantCons ?cNil ?cCons located
  all_goals intros
  all_goals simp only [RegionPermutation.term,Term.renameRuntimeRegions,List.map_cons,List.map_nil] <;>
    (try simp only [← RegionPermutation.term_def])
  case unit => exact .unit
  case scalar valid => exact .scalar valid
  case reference => exact .reference
  case pointer => exact .pointer
  case tuple _ aggregate fields => exact .tuple fields aggregate
  case callable selected _ aggregate fields => exact .callable (selected.permute valid permutation) fields aggregate
  case continuation => exact .continuation
  case label => exact .label
  case available => exact .available
  case bindings _ aggregate fields => exact .bindings fields aggregate
  case environment _ aggregate fields => exact .environment fields aggregate
  case array nonnegative bound _ array element => exact .array nonnegative bound element array
  case nominal id data arguments substitution variantTypes variantLayouts layout found representation instantiated substituted _ aggregate bound variants =>
    have lexical := valid.lexical (List.mem_of_find?_eq_some (Program.data_lookup found))
    refine .nominal found representation (instantiated.permute permutation) ?_ variants aggregate bound
    have allowed : ∀ (variant : VariantDefinition), variant ∈ data.variants → ∀ (field : FieldDefinition), field ∈ variant.fields → field.type.Lexical := by
      intro variant member field present
      exact lexical field.type (by
        simp only [Definition.terms,List.mem_append,List.mem_map,List.mem_flatMap]
        exact Or.inl (Or.inl (Or.inl ⟨field,⟨variant,member,present⟩,rfl⟩)))
    exact permutation.substitutes_variants substituted allowed
  case transparent found representation notEnum variants fields instantiated substituted _ selected nonzero others shape layouts =>
    have lexical := valid.lexical (List.mem_of_find?_eq_some (Program.data_lookup found))
    refine .transparent found representation notEnum variants fields (instantiated.permute permutation)
      (permutation.substitutes_lexical_list ?_ substituted) layouts selected nonzero others shape
    intro term member
    obtain ⟨field,present,rfl⟩ := List.mem_map.mp member
    exact lexical field.type (by
      simp only [Definition.terms,List.mem_append,List.mem_map,List.mem_flatMap]
      exact Or.inl (Or.inl (Or.inl ⟨field,⟨_,by simp [variants],fields ▸ present⟩,rfl⟩)))
  case cRepresentation found representation _ compatible =>
    exact .cRepresentation found representation (by
      simpa only [RegionPermutation.term,Term.renameRuntimeRegions] using compatible)
  case alias equal _ original => exact .alias (equal.permute valid permutation) original
  case fields _ aggregate fields => exact .fields fields aggregate
  case cScalar mapping => exact .scalar mapping
  case cPointer => exact .pointer
  case record found representation notEnum variants instantiated substituted _ aggregate fields =>
    have lexical := valid.lexical (List.mem_of_find?_eq_some (Program.data_lookup found))
    refine .record found representation notEnum variants (instantiated.permute permutation)
      (permutation.substitutes_lexical_list ?_ substituted) fields aggregate
    intro term member
    obtain ⟨field,present,rfl⟩ := List.mem_map.mp member
    exact lexical field.type (by
      simp only [Definition.terms,List.mem_append,List.mem_map,List.mem_flatMap]
      exact Or.inl (Or.inl (Or.inl ⟨field,⟨_,by simp [variants],present⟩,rfl⟩)))
  case enumeration found instantiated representation enumeration inhabited valid empty bound =>
    exact .enumeration found (instantiated.permute permutation) representation enumeration inhabited valid empty bound
  case cTransparent _ found representation variants instantiated substituted _ selected _ positive size alignment others located fields compatible =>
    have lexical := valid.lexical (List.mem_of_find?_eq_some (Program.data_lookup found))
    refine .transparent (by simpa only [RegionPermutation.term,Term.renameRuntimeRegions] using located)
      found representation variants (instantiated.permute permutation)
      (permutation.substitutes_lexical_list ?_ substituted) fields ?_ compatible positive size alignment others
    · intro term member
      obtain ⟨field,present,rfl⟩ := List.mem_map.mp member
      exact lexical field.type (by
        simp only [Definition.terms,List.mem_append,List.mem_map,List.mem_flatMap]
        exact Or.inl (Or.inl (Or.inl ⟨field,⟨_,by simp [variants],present⟩,rfl⟩)))
    · simp only [List.getElem?_map,selected,Option.map]
  case cAlias equal _ original => exact .alias (equal.permute valid permutation) original
  case nil => exact .nil
  case cons _ _ first rest => exact .cons first rest
  case variantNil => exact .nil
  case variantCons _ _ first rest => exact .cons first rest
  case cNil => exact .nil
  case cCons _ _ first rest => exact .cons first rest

end Glorious.Language
