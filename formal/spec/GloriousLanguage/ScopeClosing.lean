import GloriousLanguage.ScopeTyping

/-! A runtime scope must cover the lexical names admitted by source typing.
Closing then removes those names without rejecting abstract generic arguments
or renaming pre-existing concrete runtime identities. -/
namespace Glorious.Language

theorem Term.Scoped.mono {first second : LexicalScope} {term : Term} (admitted : term.Scoped first)
    (regions : ∀ id ∈ first.regions, id ∈ second.regions)
    (brands : ∀ id ∈ first.brands, id ∈ second.brands) : term.Scoped second :=
  ⟨fun id occurs => regions id (admitted.1 id occurs),fun id occurs => brands id (admitted.2 id occurs)⟩

theorem Term.ScopeClosed.scoped {term : Term} (closed : term.ScopeClosed) (scope : LexicalScope) : term.Scoped scope :=
  closed.mono (fun _ member => False.elim (List.not_mem_nil member))
    (fun _ member => False.elim (List.not_mem_nil member))

def ScopeInstantiation.Covers (instantiation : ScopeInstantiation) (scope : LexicalScope) : Prop :=
  (∀ id ∈ scope.regions, ∃ runtime, instantiation.regions.get id = some runtime) ∧
  (∀ id ∈ scope.brands, ∃ runtime, instantiation.brands.get id = some runtime)

theorem Term.mapChildren_eq_scopedRegion (f : Term → Term) {term : Term} {id : Identity}
    (same : term.mapChildren f = .scopedRegion id) : term = .scopedRegion id := by
  cases term <;> simp only [Term.mapChildren] at same <;> cases same <;> rfl

theorem Term.mapChildren_eq_scopedBrand (f : Term → Term) {term : Term} {id : Identity}
    (same : term.mapChildren f = .scopedBrand id) : term = .scopedBrand id := by
  cases term <;> simp only [Term.mapChildren] at same <;> cases same <;> rfl

theorem ScopeInstantiation.term_eq_mapChildren (instantiation : ScopeInstantiation) {term : Term}
    (notRegion : ∀ id, term ≠ .scopedRegion id) (notBrand : ∀ id, term ≠ .scopedBrand id) :
    instantiation.term term = term.mapChildren instantiation.term := by
  cases term <;> simp only [ScopeInstantiation.term,Term.mapChildren]
  · exact False.elim (notRegion _ rfl)
  · exact False.elim (notBrand _ rfl)

theorem ScopeInstantiation.closes (instantiation : ScopeInstantiation) {scope : LexicalScope}
    (covered : instantiation.Covers scope) (term : Term) (admitted : term.Scoped scope) :
    (instantiation.term term).ScopeClosed := by
  by_cases region : ∃ id, term = .scopedRegion id
  · obtain ⟨id,rfl⟩ := region
    obtain ⟨runtime,found⟩ := covered.1 id (admitted.1 id .here)
    simp only [ScopeInstantiation.term,found,Option.map,Option.getD]
    apply Term.Scoped.of_children
    · intro id same; cases same
    · intro id same; cases same
    · intro child member; cases member
  · by_cases brand : ∃ id, term = .scopedBrand id
    · obtain ⟨id,rfl⟩ := brand
      obtain ⟨runtime,found⟩ := covered.2 id (admitted.2 id .here)
      simp only [ScopeInstantiation.term,found,Option.map,Option.getD]
      apply Term.Scoped.of_children
      · intro id same; cases same
      · intro id same; cases same
      · intro child member; cases member
    · rw [instantiation.term_eq_mapChildren (by intro id same; exact region ⟨id,same⟩)
        (by intro id same; exact brand ⟨id,same⟩)]
      apply Term.Scoped.of_children
      · intro id same
        exact False.elim (region ⟨id,Term.mapChildren_eq_scopedRegion _ same⟩)
      · intro id same
        exact False.elim (brand ⟨id,Term.mapChildren_eq_scopedBrand _ same⟩)
      · intro child member
        rw [Term.mapChildren_children] at member
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
        exact instantiation.closes covered original (admitted.child present)
termination_by term
decreasing_by exact Term.child_sizeOf present

theorem ScopeInstantiation.Covers.bindRegion {instantiation : ScopeInstantiation} {scope : LexicalScope}
    (covered : instantiation.Covers scope) (lexical runtime : Identity) :
    ({ instantiation with regions := instantiation.regions.set lexical runtime } : ScopeInstantiation).Covers
      (scope.bindRegion lexical) := by
  refine ⟨?_,covered.2⟩
  intro id member
  by_cases same : id = lexical
  · subst id; exact ⟨runtime,Table.get_set _ _ _⟩
  · have present : id ∈ scope.regions := by
      simpa only [LexicalScope.bindRegion,List.mem_cons,same,false_or] using member
    obtain ⟨value,found⟩ := covered.1 id present
    exact ⟨value,by simpa only [Table.get_set_other _ _ _ _ same] using found⟩

/-- Closing depends only on the lexical names that actually occur. A fresh
binding cannot reinterpret an existing local's type. -/
theorem ScopeInstantiation.term_congr (first second : ScopeInstantiation) {scope : LexicalScope}
    (regions : ∀ id ∈ scope.regions, first.regions.get id = second.regions.get id)
    (brands : ∀ id ∈ scope.brands, first.brands.get id = second.brands.get id)
    (term : Term) (admitted : term.Scoped scope) : first.term term = second.term term := by
  cases term <;> simp only [ScopeInstantiation.term]
  case scopedRegion id => rw [regions id (admitted.1 id .here)]
  case scopedBrand id => rw [brands id (admitted.2 id .here)]
  all_goals try rfl
  all_goals
    congr 1
    all_goals first
    | apply List.map_congr_left
      intro child member
      exact first.term_congr second regions brands child (admitted.child (by simp [Term.children,member]))
    | exact first.term_congr second regions brands _ (admitted.child (by simp [Term.children]))
termination_by term

theorem Execution.Context.bindRegion_term {context : Execution.Context} {scope : LexicalScope}
    {lexical runtime : Identity} (fresh : lexical ∉ scope.regions) {term : Term} (admitted : term.Scoped scope) :
    (context.bindRegion lexical runtime).term term = context.term term := by
  apply ScopeInstantiation.term_congr _ _ (scope := scope) _ _ term admitted
  · intro id member
    exact Table.get_set_other _ _ _ _ (by intro same; exact fresh (same ▸ member))
  · intro id _; rfl

theorem Execution.Context.bindBrand_term {context : Execution.Context} {scope : LexicalScope}
    {lexical : Identity} {runtime : RuntimeBrand} (fresh : lexical ∉ scope.brands) {term : Term} (admitted : term.Scoped scope) :
    (context.bindBrand lexical runtime).term term = context.term term := by
  apply ScopeInstantiation.term_congr _ _ (scope := scope) _ _ term admitted
  · intro id _; rfl
  · intro id member
    exact Table.get_set_other _ _ _ _ (by intro same; exact fresh (same ▸ member))

theorem ScopeInstantiation.Covers.bindBrand {instantiation : ScopeInstantiation} {scope : LexicalScope}
    (covered : instantiation.Covers scope) (lexical : Identity) (runtime : RuntimeBrand) :
    ({ instantiation with brands := instantiation.brands.set lexical runtime } : ScopeInstantiation).Covers
      (scope.bindBrand lexical) := by
  refine ⟨covered.1,?_⟩
  intro id member
  by_cases same : id = lexical
  · subst id; exact ⟨runtime,Table.get_set _ _ _⟩
  · have present : id ∈ scope.brands := by
      simpa only [LexicalScope.bindBrand,List.mem_cons,same,false_or] using member
    obtain ⟨value,found⟩ := covered.2 id present
    exact ⟨value,by simpa only [Table.get_set_other _ _ _ _ same] using found⟩

theorem Kernel.Function.entryScope_covers (function : Kernel.Function) (region brand : Identity) :
    (function.entryScope region brand).Covers
      ⟨[function.activationRegion],function.namedExit.toList,some function.activationRegion⟩ := by
  constructor
  · intro id member
    have same : id = function.activationRegion := by simpa only [List.mem_singleton] using member
    subst id
    exact ⟨region,by simp [Kernel.Function.entryScope,Table.get]⟩
  · intro id member
    cases named : function.namedExit with
    | none => simp [named] at member
    | some label =>
      have same : id = label := by simpa only [named,Option.toList_some,List.mem_singleton] using member
      subst id
      exact ⟨.label brand,by simp [Kernel.Function.entryScope,named,Table.get]⟩

theorem Execution.Context.term_scopeClosed {context : Execution.Context} {source : Typing.Context}
    (covered : context.instantiation.Covers source.static.scope) {program : Program} {term : Term} {kind : Kind}
    (kinded : Kinding program source.static term kind) : (context.term term).ScopeClosed :=
  context.instantiation.closes covered term kinded.scoped

end Glorious.Language
