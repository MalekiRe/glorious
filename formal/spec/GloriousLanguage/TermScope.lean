import GloriousLanguage.Static

/-! Executable lexical names are closed at invocation, not confused with
universally quantified eigenvariables. The same syntactic admission judgment
is consumed by kinding, declaration instances and the actual entry context. -/
namespace Glorious.Language

theorem List.map_eq_self_of {α : Type} (f : α → α) (values : List α)
    (fixed : ∀ value ∈ values, f value = value) : values.map f = values := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.map_cons,fixed first List.mem_cons_self,
        ih (fun value member => fixed value (List.mem_cons_of_mem _ member))]

theorem Term.mapChildren_children (f : Term → Term) (term : Term) :
    (term.mapChildren f).children = term.children.map f := by
  cases term <;> simp only [Term.mapChildren,Term.children,List.map_cons,List.map_nil,List.map_append]

theorem Term.substitute_eq_mapChildren (substitution : Substitution) {term : Term}
    (notParameter : ∀ id kind, term ≠ .parameter id kind) :
    term.substitute substitution = term.mapChildren (Term.substitute substitution) := by
  cases term <;> simp only [Term.substitute,Term.mapChildren]
  exact False.elim (notParameter _ _ rfl)

theorem Instantiates.argument_of_get {binders : List Binder} {arguments : List Term} {substitution : Substitution}
    (instantiated : Instantiates binders arguments substitution) {id : Identity} {value : Term}
    (found : substitution.get id = some value) : value ∈ arguments := by
  obtain ⟨entry,located,atValue⟩ := Option.map_eq_some_iff.mp found
  have member := List.mem_of_find?_eq_some located
  rw [instantiated.2.2] at member
  rw [← atValue]
  exact (List.of_mem_zip member).2

theorem Term.Scoped.of_children {scope : LexicalScope} {term : Term}
    (region : ∀ id, term = .scopedRegion id → id ∈ scope.regions)
    (brand : ∀ id, term = .scopedBrand id → id ∈ scope.brands)
    (children : ∀ child ∈ term.children, child.Scoped scope) : term.Scoped scope := by
  constructor
  · intro id occurs
    cases occurs with
    | here => exact region id rfl
    | child member nested => exact (children _ member).1 id nested
  · intro id occurs
    cases occurs with
    | here => exact brand id rfl
    | child member nested => exact (children _ member).2 id nested

theorem Term.Scoped.mapChildren {scope : LexicalScope} {term : Term}
    (admitted : term.Scoped scope) (f : Term → Term)
    (children : ∀ child ∈ term.children, (f child).Scoped scope) :
    (term.mapChildren f).Scoped scope := by
  apply Term.Scoped.of_children
  · intro id same
    have original : term = .scopedRegion id := by
      cases term <;> simp only [Term.mapChildren] at same <;> cases same <;> rfl
    subst term
    exact admitted.1 id .here
  · intro id same
    have original : term = .scopedBrand id := by
      cases term <;> simp only [Term.mapChildren] at same <;> cases same <;> rfl
    subst term
    exact admitted.2 id .here
  · intro child member
    rw [Term.mapChildren_children] at member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    exact children original present

theorem Term.Scoped.substitute {scope : LexicalScope} (substitution : Substitution) (term : Term)
    (admitted : term.Scoped scope)
    (arguments : ∀ id value, substitution.get id = some value → value.Scoped scope) :
    (term.substitute substitution).Scoped scope := by
  by_cases parameter : ∃ id kind, term = .parameter id kind
  · obtain ⟨id,kind,rfl⟩ := parameter
    cases found : substitution.get id with
    | none => simpa only [Term.substitute,found,Option.getD] using admitted
    | some value => simpa only [Term.substitute,found,Option.getD] using arguments id value found
  · rw [Term.substitute_eq_mapChildren substitution (by
      intro id kind same; exact parameter ⟨id,kind,same⟩)]
    apply admitted.mapChildren
    intro child member
    exact Term.Scoped.substitute substitution child (admitted.child member) arguments
termination_by term
decreasing_by exact Term.child_sizeOf member

theorem Term.ScopeClosed.substitute {term : Term} (closed : term.ScopeClosed)
    (substitution : Substitution)
    (arguments : ∀ id value, substitution.get id = some value → value.ScopeClosed) :
    (term.substitute substitution).ScopeClosed :=
  Term.Scoped.substitute substitution term closed arguments

theorem ScopeInstantiation.term_fixed (scope : ScopeInstantiation) (term : Term)
    (closed : term.ScopeClosed) : scope.term term = term := by
  cases term <;> simp only [ScopeInstantiation.term]
  case scopedRegion id => exact False.elim (List.not_mem_nil (closed.1 id .here))
  case scopedBrand id => exact False.elim (List.not_mem_nil (closed.2 id .here))
  all_goals try rfl
  all_goals
    congr 1
    all_goals first
    | apply List.map_eq_self_of
      intro child member
      exact scope.term_fixed child (closed.child (by simp [Term.children,member]))
    | exact scope.term_fixed _ (closed.child (by simp [Term.children]))
termination_by term

theorem Kinding.scoped {program : Program} {context : Context} {term : Term} {kind : Kind}
    (kinded : Kinding program context term kind) : term.Scoped context.scope := by
  induction kinded <;> apply Term.Scoped.of_children
  all_goals intros
  all_goals try simp_all [Term.children,Term.Scoped]
  all_goals grind

theorem ProgramWellFormed.scopeClosed {program : Program} (valid : ProgramWellFormed program)
    {definition : Definition} (member : definition ∈ program.declarations) : definition.ScopeClosed :=
  (valid.2.2.2.2.1 definition member).1.2

theorem Instantiates.scopeClosed {binders : List Binder} {arguments : List Term} {substitution : Substitution}
    (instantiated : Instantiates binders arguments substitution)
    (closed : ∀ argument ∈ arguments, argument.ScopeClosed) {term : Term} (admitted : term.ScopeClosed) :
    (term.substitute substitution).ScopeClosed :=
  admitted.substitute substitution (fun _ _ found => closed _ (instantiated.argument_of_get found))

end Glorious.Language
