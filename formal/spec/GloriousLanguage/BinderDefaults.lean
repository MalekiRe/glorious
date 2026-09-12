import GloriousLanguage.SubstitutionKinding

/-! Ordered generic defaults consume the same actual parameter instantiation
and substitution graph as explicit arguments. Declaration admission and
nested quantified admission share the Static prefix-scope producer. -/
namespace Glorious.Language

theorem BinderDefaultsWellFormed.default {program : Program} {context : Context} {binders : List Binder}
    (defaults : BinderDefaultsWellFormed program context binders) {index : Nat} {binder : Binder} {value : Term}
    (atBinder : binders[index]? = some binder) (selected : binder.defaultValue = some value) :
    WellKinded program (context.bindParameters (binders.take index)) value binder.kind :=
  ⟨defaults.1 index binder value atBinder selected,defaults.2 index binder value atBinder selected⟩

theorem BinderDefaultsKinded.terms_kinded {program : Program} {context : Context} {binders : List Binder}
    (defaults : BinderDefaultsKinded program context binders) :
    ∀ term ∈ binders.flatMap (fun binder => binder.defaultValue.toList), ∃ bound,
      Kinding program { context with binders := bound } term term.kind := by
  intro term member
  obtain ⟨binder,present,selected⟩ := List.mem_flatMap.mp member
  obtain ⟨index,atBinder⟩ := List.mem_iff_getElem?.mp present
  have checked := defaults index binder term atBinder (by simpa using selected)
  exact ⟨_,by simpa only [Context.bindParameters,checked.term_kind] using checked⟩

/-- A default is specialized under exactly the visible owner-and-prefix
binders. A kind-correct source default cannot introduce a future parameter,
a malformed substitution entry or an atom outside the caller's universe. -/
theorem BinderDefaultsKinded.instantiate_default {program : Program} {source target : Context} {binders : List Binder}
    (defaults : BinderDefaultsKinded program source binders) {index : Nat} {binder : Binder} {value : Term}
    (atBinder : binders[index]? = some binder) (selected : binder.defaultValue = some value)
    {arguments : List Term} {substitution : Substitution}
    (instantiated : Instantiates (source.bindParameters (binders.take index)).binders arguments substitution)
    (argumentsKinded : ∀ argument ∈ arguments, Kinding program target argument argument.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands) :
    Kinding program target (value.substitute substitution) binder.kind ∧
      Substitutes substitution value (value.substitute substitution) :=
  (defaults index binder value atBinder selected).instantiate instantiated argumentsKinded levels regions brands

/-- Filling the next omitted generic argument produces the real next
Instantiates prefix, not a parallel default-binding table. The caller may
repeat this theorem to discharge an entire trailing default sequence. -/
theorem Instantiates.default_step {program : Program} {source target : Context} {binders : List Binder}
    (defaults : BinderDefaultsKinded program { source with binders := [] } binders)
    (unique : (binders.map (·.id)).Nodup) {index : Nat} {binder : Binder} {value : Term}
    (atBinder : binders[index]? = some binder) (selected : binder.defaultValue = some value)
    {arguments : List Term} {substitution : Substitution}
    (instantiated : Instantiates (binders.take index) arguments substitution)
    (argumentsKinded : ∀ argument ∈ arguments, Kinding program target argument argument.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands) :
    Substitutes substitution value (value.substitute substitution) ∧
      Kinding program target (value.substitute substitution) binder.kind ∧
      Instantiates (binders.take (index + 1)) (arguments ++ [value.substitute substitution])
        (substitution ++ [(binder.id,value.substitute substitution)]) := by
  have previous : Instantiates (({ source with binders := [] } : Context).bindParameters (binders.take index)).binders
      arguments substitution := by simpa only [Context.bindParameters,List.filter_nil,List.append_nil] using instantiated
  obtain ⟨kinded,graph⟩ := defaults.instantiate_default atBinder selected previous argumentsKinded levels regions brands
  have next : binders.take (index + 1) = binders.take index ++ [binder] := by
    rw [List.take_add_one,atBinder]
    rfl
  have singleton : Instantiates [binder] [value.substitute substitution] [(binder.id,value.substitute substitution)] :=
    ⟨by simp,ListRel.cons kinded.term_kind.symm .nil,rfl⟩
  refine ⟨graph,kinded,?_⟩
  rw [next]
  apply instantiated.append singleton
  rw [← next,List.map_take]
  exact unique.take

end Glorious.Language
