import GloriousLanguage.DeclarationDependencyKinding

/-! Composition at an actual fully instantiated declaration. The outer
substitution transforms the caller values already in the raw table; it does
not substitute the declaration's binder identities a second time or recurse
through an inserted argument during the original simultaneous opening. -/
namespace Glorious.Language

theorem Instantiates.map_values {binders : List Binder} {arguments : List Term} {substitution : Substitution}
    (instantiated : Instantiates binders arguments substitution) (map : Term → Term)
    (preserves : ∀ argument ∈ arguments, (map argument).kind = argument.kind) :
    Instantiates binders (arguments.map map) (substitution.map (fun entry => (entry.1,map entry.2))) := by
  have table : (binders.map (·.id)).zip (arguments.map map) =
      substitution.map (fun entry => (entry.1,map entry.2)) := by
    rw [instantiated.2.2,List.zip_map_right]
    apply List.map_congr_left
    intro ⟨key,value⟩ _
    rfl
  rw [← table]
  exact instantiated.map_kind map preserves

theorem Term.substitute_map_values (term : Term) (inner outer : Substitution)
    (covered : ∀ id kind, Occurs (.parameter id kind) term → ∃ value, inner.get id = some value) :
    (term.substitute inner).substitute outer =
      term.substitute (inner.map (fun entry => (entry.1,entry.2.substitute outer))) := by
  cases term
  case parameter id kind =>
    obtain ⟨value,found⟩ := covered id kind .here
    simp only [Term.substitute,Table.get_map_values,found,Option.map_some,Option.getD_some]
  all_goals simp only [Term.substitute,List.map_map,Function.comp_def]
  all_goals congr 1
  all_goals first
    | (apply List.map_congr_left
       intro child member
       apply Term.substitute_map_values
       intro id kind occurs
       exact covered id kind (.child (by simp only [Term.children,List.mem_append]; grind) occurs))
    | (apply Term.substitute_map_values
       intro id kind occurs
       exact covered id kind (.child (by simp [Term.children]) occurs))
termination_by term

/-- A complete lawful binder instantiation covers every source occurrence
already established by kinding, so composition needs no ad-hoc freshness or
caller-normalization hypothesis. -/
theorem Kinding.substitute_instantiated_values {program : Program} {context : Context} {term : Term} {kind : Kind}
    (kinded : Kinding program context term kind) {arguments : List Term} {inner : Substitution}
    (instantiated : Instantiates context.binders arguments inner) (outer : Substitution) :
    (term.substitute inner).substitute outer =
      term.substitute (inner.map (fun entry => (entry.1,entry.2.substitute outer))) := by
  apply term.substitute_map_values inner outer
  intro id kind occurs
  obtain ⟨binder,member,sameId,_⟩ := kinded.parameter_occurs occurs
  obtain ⟨value,_,_,found⟩ := instantiated.binder_lookup member
  exact ⟨value,sameId ▸ found⟩

theorem Instantiates.substitute_values {program : Program} {source target : Context}
    {binders : List Binder} {arguments : List Term} {inner : Substitution}
    (instantiated : Instantiates binders arguments inner)
    (argumentsKinded : ∀ argument ∈ arguments, Kinding program source argument argument.kind)
    (outer : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute outer) binder.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands) :
    Instantiates binders (arguments.map (Term.substitute outer))
      (inner.map (fun entry => (entry.1,entry.2.substitute outer))) := by
  exact instantiated.map_values (Term.substitute outer) (fun argument member =>
    ((argumentsKinded argument member).substitute outer parameters levels regions brands).term_kind)

/-- The output is the outer substitution of the actual first opening. Both
the new raw-table instantiation and its checked substitution edge are derived
from the admitted declaration, not supplied as prospective output premises. -/
theorem Kinding.instantiate_substitute {program : Program} {source target : Context} {term : Term} {kind : Kind}
    (kinded : Kinding program source term kind) {arguments : List Term} {inner : Substitution}
    (instantiated : Instantiates source.binders arguments inner) (outer : Substitution)
    (argumentsKinded : ∀ argument ∈ arguments, Kinding program target (argument.substitute outer) argument.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands) :
    Instantiates source.binders (arguments.map (Term.substitute outer))
        (inner.map (fun entry => (entry.1,entry.2.substitute outer))) ∧
      Kinding program target ((term.substitute inner).substitute outer) kind ∧
      Substitutes (inner.map (fun entry => (entry.1,entry.2.substitute outer))) term
        ((term.substitute inner).substitute outer) := by
  have mapped : Instantiates source.binders (arguments.map (Term.substitute outer))
      (inner.map (fun entry => (entry.1,entry.2.substitute outer))) :=
    instantiated.map_values (Term.substitute outer) (fun argument member => (argumentsKinded argument member).term_kind)
  refine ⟨mapped,?_⟩
  rw [kinded.substitute_instantiated_values instantiated outer]
  apply kinded.instantiate mapped ?_ levels regions brands
  intro term member
  obtain ⟨argument,present,rfl⟩ := List.mem_map.mp member
  rw [(argumentsKinded argument present).term_kind]
  exact argumentsKinded argument present

theorem ListRel.instantiate_substitute {program : Program} {source target : Context} {before after arguments : List Term}
    {inner : Substitution} {kind : Kind}
    (related : ListRel (Substitutes inner) before after)
    (templates : ∀ term ∈ before, Kinding program source term kind)
    (instantiated : Instantiates source.binders arguments inner) (outer : Substitution)
    (argumentsKinded : ∀ argument ∈ arguments, Kinding program target (argument.substitute outer) argument.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands) :
    ListRel (Substitutes (inner.map (fun entry => (entry.1,entry.2.substitute outer)))) before
      (after.map (Term.substitute outer)) := by
  induction related with
  | nil => exact .nil
  | cons head _ ih =>
    refine .cons ?_ (ih (fun term member => templates term (List.mem_cons_of_mem _ member)))
    rw [head.2.1]
    exact ((templates _ List.mem_cons_self).instantiate_substitute instantiated outer argumentsKinded
      levels regions brands).2.2

theorem CallableFields.substitute {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {id : DeclId} {arguments fields : List Term}
    (captured : CallableFields program id arguments fields)
    (kinded : Kinding program source (.callable id arguments) .type) (outer : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute outer) binder.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands) :
    CallableFields program id (arguments.map (Term.substitute outer)) (fields.map (Term.substitute outer)) := by
  cases kinded with
  | callable found _ argumentsKinded =>
    cases captured with
    | function actual instantiated substituted =>
      obtain rfl := Option.some.inj (found.symm.trans actual)
      exact .function actual
        (instantiated.substitute_values argumentsKinded outer parameters levels regions brands)
        (substituted.instantiate_substitute (valid.function_capture_types actual) instantiated outer
          (fun argument member => (argumentsKinded argument member).substitute outer parameters levels regions brands)
          (Nat.zero_le _) (fun _ present => False.elim (List.not_mem_nil present))
          (fun _ present => False.elim (List.not_mem_nil present)))
    | operation actual _ =>
      have impossible := (Program.function_lookup found).symm.trans (Program.operation_lookup actual)
      cases impossible

end Glorious.Language
