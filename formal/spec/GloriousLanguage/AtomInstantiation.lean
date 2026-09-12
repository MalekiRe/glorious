import GloriousLanguage.InstantiationComposition

/-! Noninjective atom replacement after an actual declaration opening.
Template parameters are interpreted by the exact raw instantiation table;
nonparameter source atoms remain lexical declaration constants. -/
namespace Glorious.Language

/-- The same constructor law consumed by `Kinding.map_atoms`. Atomic
replacement may identify different types or replace a rigid with a compound
term; every non-atomic constructor retains its ordered children and head. -/
def AtomHomomorphism (map : Term → Term) : Prop :=
  ∀ term, map term = match term with
    | .parameter id kind => map (.parameter id kind)
    | .rigid id kind level => map (.rigid id kind level)
    | .variable id kind level => map (.variable id kind level)
    | .runtimeRegion id => map (.runtimeRegion id)
    | other => other.mapChildren map

theorem Term.mapChildren_congr (term : Term) {first second : Term → Term}
    (agree : ∀ child ∈ term.children, first child = second child) :
    term.mapChildren first = term.mapChildren second := by
  cases term <;> simp only [Term.mapChildren]
  all_goals simp only [Term.children,List.mem_cons,List.mem_append,List.not_mem_nil] at agree
  all_goals congr 1
  all_goals first
    | exact agree _ (by simp)
    | (apply List.map_congr_left
       intro child member
       exact agree child (by simp [member]))

/-- Only nonparameter atoms require fixedness in a declaration template.
Its parameters are opened simultaneously before the outer map acts. -/
def Term.AtomsFixed (map : Term → Term) (term : Term) : Prop :=
  ∀ atom, Occurs atom term → match atom with
    | .rigid .. | .variable .. | .runtimeRegion .. => map atom = atom
    | _ => True

theorem Term.AtomsFixed.child {map : Term → Term} {term child : Term}
    (fixed : term.AtomsFixed map) (member : child ∈ term.children) : child.AtomsFixed map :=
  fun atom occurs => fixed atom (.child member occurs)

theorem AtomHomomorphism.fixed_term {map : Term → Term} (shape : AtomHomomorphism map) (term : Term)
    (parameters : ∀ id kind, Occurs (.parameter id kind) term → map (.parameter id kind) = .parameter id kind)
    (fixed : term.AtomsFixed map) : map term = term := by
  cases term
  case parameter id kind => exact parameters id kind .here
  case rigid => exact fixed _ .here
  case «variable» => exact fixed _ .here
  case runtimeRegion => exact fixed _ .here
  all_goals rw [shape]
  all_goals simp only [Term.mapChildren]
  all_goals try rfl
  all_goals congr 1
  all_goals first
  | apply List.map_eq_self_of
    intro child member
    apply shape.fixed_term child
    · intro id kind occurs
      exact parameters id kind (.child (by simp only [Term.children,List.mem_append]; grind) occurs)
    · exact fixed.child (by simp only [Term.children,List.mem_append]; grind)
  | apply shape.fixed_term
    · intro id kind occurs
      exact parameters id kind (.child (by simp [Term.children]) occurs)
    · exact fixed.child (by simp [Term.children])
termination_by term

theorem Term.map_instantiated_values (term : Term) (inner : Substitution) (map : Term → Term)
    (shape : AtomHomomorphism map) (fixed : term.AtomsFixed map)
    (covered : ∀ id kind, Occurs (.parameter id kind) term → ∃ value, inner.get id = some value) :
    map (term.substitute inner) = term.substitute (inner.map (fun entry => (entry.1,map entry.2))) := by
  cases term
  case parameter id kind =>
    obtain ⟨value,found⟩ := covered id kind .here
    simp only [Term.substitute,Table.get_map_values,found,Option.map_some,Option.getD_some]
  case rigid => simpa only [Term.substitute] using fixed _ .here
  case «variable» => simpa only [Term.substitute] using fixed _ .here
  case runtimeRegion => simpa only [Term.substitute] using fixed _ .here
  all_goals simp only [Term.substitute]
  all_goals rw [shape]
  all_goals simp only [Term.mapChildren,List.map_map,Function.comp_def]
  all_goals congr 1
  all_goals first
    | (apply List.map_congr_left
       intro child member
       apply child.map_instantiated_values inner map shape
       · apply fixed.child
         simp only [Term.children,List.mem_append]
         grind
       · intro id kind occurs
         exact covered id kind (.child (by simp only [Term.children,List.mem_append]; grind) occurs))
    | (apply Term.map_instantiated_values _ inner map shape
       · apply fixed.child
         simp [Term.children]
       intro id kind occurs
       exact covered id kind (.child (by simp [Term.children]) occurs))
termination_by term

theorem Kinding.map_instantiated_values {program : Program} {context : Context} {term : Term} {kind : Kind}
    (kinded : Kinding program context term kind) {arguments : List Term} {inner : Substitution}
    (instantiated : Instantiates context.binders arguments inner) (map : Term → Term)
    (shape : AtomHomomorphism map) (fixed : term.AtomsFixed map) :
    map (term.substitute inner) = term.substitute (inner.map (fun entry => (entry.1,map entry.2))) := by
  apply term.map_instantiated_values inner map shape fixed
  intro id kind occurs
  obtain ⟨binder,member,sameId,_⟩ := kinded.parameter_occurs occurs
  obtain ⟨value,_,_,found⟩ := instantiated.binder_lookup member
  exact ⟨value,sameId ▸ found⟩

/-- The actual mapped instantiation and its checked body edge are derived
from source admission and kinded mapped caller arguments. No injective map,
inverse representative, or prospective output graph is required. -/
theorem Kinding.instantiate_map {program : Program} {source target : Context} {term : Term} {kind : Kind}
    (kinded : Kinding program source term kind) {arguments : List Term} {inner : Substitution}
    (instantiated : Instantiates source.binders arguments inner) (map : Term → Term)
    (shape : AtomHomomorphism map) (fixed : term.AtomsFixed map)
    (argumentsKinded : ∀ argument ∈ arguments, Kinding program target (map argument) argument.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands) :
    Instantiates source.binders (arguments.map map) (inner.map (fun entry => (entry.1,map entry.2))) ∧
      Kinding program target (map (term.substitute inner)) kind ∧
      Substitutes (inner.map (fun entry => (entry.1,map entry.2))) term (map (term.substitute inner)) := by
  have mapped := instantiated.map_values map (fun argument member => (argumentsKinded argument member).term_kind)
  refine ⟨mapped,?_⟩
  rw [kinded.map_instantiated_values instantiated map shape fixed]
  apply kinded.instantiate mapped ?_ levels regions brands
  intro term member
  obtain ⟨argument,present,rfl⟩ := List.mem_map.mp member
  rw [(argumentsKinded argument present).term_kind]
  exact argumentsKinded argument present

theorem ListRel.instantiate_map {program : Program} {source target : Context} {before after arguments : List Term}
    {inner : Substitution} {kind : Kind}
    (related : ListRel (Substitutes inner) before after)
    (templates : ∀ term ∈ before, Kinding program source term kind)
    (instantiated : Instantiates source.binders arguments inner) (map : Term → Term)
    (shape : AtomHomomorphism map) (fixed : ∀ term ∈ before, term.AtomsFixed map)
    (argumentsKinded : ∀ argument ∈ arguments, Kinding program target (map argument) argument.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands) :
    ListRel (Substitutes (inner.map (fun entry => (entry.1,map entry.2)))) before (after.map map) := by
  induction related with
  | nil => exact .nil
  | cons head _ ih =>
    refine .cons ?_ (ih (fun term member => templates term (List.mem_cons_of_mem _ member))
      (fun term member => fixed term (List.mem_cons_of_mem _ member)))
    rw [head.2.1]
    exact ((templates _ List.mem_cons_self).instantiate_map instantiated map shape (fixed _ List.mem_cons_self)
      argumentsKinded levels regions brands).2.2

/-- A globally kind-preserving atom replacement also maps a raw checked
opening whose caller arguments need not themselves be well-kinded. This is
required for intermediate nodes of the untyped logical proof syntax. Source
template admission still supplies complete coverage of declaration binders. -/
theorem Substitutes.map_instantiated {program : Program} {source : Context} {before after : Term} {kind : Kind}
    {arguments : List Term} {inner : Substitution} (graph : Substitutes inner before after)
    (kinded : Kinding program source before kind) (instantiated : Instantiates source.binders arguments inner)
    (map : Term → Term) (shape : AtomHomomorphism map) (fixed : before.AtomsFixed map)
    (kinds : ∀ term, (map term).kind = term.kind) :
    Substitutes (inner.map (fun entry => (entry.1,map entry.2))) before (map after) := by
  refine ⟨by rw [kinds]; exact graph.1,?_,?_⟩
  · rw [graph.2.1]
    exact kinded.map_instantiated_values instantiated map shape fixed
  · intro id kind value occurs found
    rw [Table.get_map_values] at found
    obtain ⟨original,located,rfl⟩ := Option.map_eq_some_iff.mp found
    exact (kinds original).trans (graph.2.2 id kind original occurs located)

theorem ListRel.map_instantiated {program : Program} {source : Context} {before after arguments : List Term}
    {inner : Substitution} {kind : Kind} (related : ListRel (Substitutes inner) before after)
    (templates : ∀ term ∈ before, Kinding program source term kind)
    (instantiated : Instantiates source.binders arguments inner) (map : Term → Term)
    (shape : AtomHomomorphism map) (fixed : ∀ term ∈ before, term.AtomsFixed map)
    (kinds : ∀ term, (map term).kind = term.kind) :
    ListRel (Substitutes (inner.map (fun entry => (entry.1,map entry.2)))) before (after.map map) := by
  induction related with
  | nil => exact .nil
  | cons head _ ih =>
    exact .cons (head.map_instantiated (templates _ List.mem_cons_self) instantiated map shape
      (fixed _ List.mem_cons_self) kinds)
      (ih (fun term member => templates term (List.mem_cons_of_mem _ member))
        (fun term member => fixed term (List.mem_cons_of_mem _ member)))

def Program.AtomsFixed (program : Program) (map : Term → Term) : Prop :=
  ∀ declaration ∈ program.declarations, ∀ term ∈ declaration.terms, term.AtomsFixed map

theorem CallableFields.map_atoms {program : Program} (valid : ProgramWellFormed program)
    {id : DeclId} {arguments fields : List Term} (captured : CallableFields program id arguments fields)
    (map : Term → Term) (shape : AtomHomomorphism map) (fixed : program.AtomsFixed map)
    (kinds : ∀ term, (map term).kind = term.kind) :
    CallableFields program id (arguments.map map) (fields.map map) := by
  cases captured with
  | function found instantiated graphs =>
    have templates := fixed _ (List.mem_of_find?_eq_some (Program.function_lookup found))
    exact .function found (instantiated.map_values map (fun term _ => kinds term))
      (graphs.map_instantiated (valid.function_capture_types found) instantiated map shape
        (fun term member => templates term (by
          simp only [Definition.terms,List.mem_append]
          exact Or.inl (Or.inr member))) kinds)
  | operation found instantiated => exact .operation found (instantiated.map_values map (fun term _ => kinds term))

end Glorious.Language
