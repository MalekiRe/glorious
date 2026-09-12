import GloriousLanguage.AtomRelations
import GloriousLanguage.SubstitutionKinding

/-! Transport for the interpretation that closes executable lexical names. The
existing atom actions treat `scopedRegion`/`scopedBrand` as fixed, so the
run-time scope map `ScopeInstantiation.term`, which replaces exactly those two
constructors with the regions/brands allocated by actual entry, is not an
`AtomHomomorphism`. This module states the scoped constructor law once and
derives the substitution and row transport from it, so a source-level fact is
read at its actual runtime image without a second semantics. -/
namespace Glorious.Language

/-- The scoped-atom analogue of `AtomHomomorphism`. Parameter, universal,
generative and executable lexical atoms are replaced freely; every other
constructor retains its ordered children. This is exactly the shape consumed
by `Kinding.map_scoped_atoms`. -/
def Term.ScopedHomomorphism (map : Term → Term) : Prop :=
  ∀ term, map term = match term with
    | .parameter id kind => map (.parameter id kind)
    | .rigid id kind level => map (.rigid id kind level)
    | .variable id kind level => map (.variable id kind level)
    | .runtimeRegion id => map (.runtimeRegion id)
    | .scopedRegion id => map (.scopedRegion id)
    | .scopedBrand id => map (.scopedBrand id)
    | other => other.mapChildren map

theorem Term.ScopedHomomorphism.same_or_children {map : Term → Term} (shape : Term.ScopedHomomorphism map)
    {left right : Term} (same : SameHead left right) :
    left = right ∨ (map left = left.mapChildren map ∧ map right = right.mapChildren map) := by
  by_cases identical : left = right
  · exact Or.inl identical
  right
  constructor
  · rw [shape]
    cases left <;> try rfl
    all_goals cases right <;> simp_all [SameHead,Term.mapChildren]
  · rw [shape]
    cases right <;> try rfl
    all_goals cases left <;> simp_all [SameHead,Term.mapChildren]

theorem Term.ScopedHomomorphism.congr_relation {map : Term → Term} (shape : Term.ScopedHomomorphism map)
    {relation : Term → Term → Prop} (reflexive : ∀ term, relation term term)
    (congruent : ∀ {left right}, SameHead left right → ListRel relation left.children right.children → relation left right)
    {left right : Term} (same : SameHead left right)
    (children : ListRel (fun first second => relation (map first) (map second)) left.children right.children) :
    relation (map left) (map right) := by
  rcases shape.same_or_children same with rfl | ⟨first,second⟩
  · exact reflexive _
  · rw [first,second]
    apply congruent
    · exact (PredicateSemantics.Term.sameHead_mapChildren left map).symm.trans
        (same.trans (PredicateSemantics.Term.sameHead_mapChildren right map))
    · rw [Term.mapChildren_children,Term.mapChildren_children]
      generalize left.children = firstList at children ⊢
      generalize right.children = secondList at children ⊢
      induction children with
      | nil => exact .nil
      | cons head _ tail => exact .cons head tail

theorem RowEquivalent.map_scoped_atoms {left right : Term} (equal : RowEquivalent left right)
    (map : Term → Term) (shape : Term.ScopedHomomorphism map) : RowEquivalent (map left) (map right) := by
  refine RowEquivalent.rec
    (motive_1 := fun left right _ => RowEquivalent (map left) (map right))
    (motive_2 := fun left right _ => ListRel (fun first second => RowEquivalent (map first) (map second)) left right)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ equal
  · intros; exact .refl
  · intro _ _ _ ih; exact .symm ih
  · intro _ _ _ _ _ first second; exact .trans first second
  · intro _ _ same _ children
    exact shape.congr_relation (fun _ => .refl) RowEquivalent.congr same children
  · intro _ _ _ _ instances tails
    rw [shape,shape]
    exact .permutation (instances.map _) (tails.map _)
  · intros
    rw [shape,shape]
    simpa only [Term.mapChildren,List.map_cons,List.map_append,shape (.row _ _)] using
      (RowEquivalent.flatten (instances := _) (tails := _) (nested := _) (nestedTails := _))
  · intro _ _ _ _ _ ih
    rw [shape,shape]
    exact .duplicate ih
  · intro _ _ _ _ _ ih
    rw [shape,shape]
    exact .tailDuplicate ih
  · exact .nil
  · intro _ _ _ _ _ _ head tail; exact .cons head tail

namespace ScopeInstantiation

/-- The runtime scope map closes exactly the two executable lexical
constructors and leaves every other constructor structural. -/
theorem scopedHomomorphism (scope : ScopeInstantiation) : Term.ScopedHomomorphism scope.term := by
  intro term
  cases term <;> simp only [ScopeInstantiation.term,Term.mapChildren]

theorem parameter_fixed (scope : ScopeInstantiation) (id : Identity) (kind : Kind) :
    scope.term (.parameter id kind) = .parameter id kind := by
  simp only [ScopeInstantiation.term]

theorem rigid_fixed (scope : ScopeInstantiation) (id : Identity) (kind : Kind) (level : Nat) :
    scope.term (.rigid id kind level) = .rigid id kind level := by
  simp only [ScopeInstantiation.term]

theorem variable_fixed (scope : ScopeInstantiation) (id : Identity) (kind : Kind) (level : Nat) :
    scope.term (.variable id kind level) = .variable id kind level := by
  simp only [ScopeInstantiation.term]

theorem runtimeRegion_fixed (scope : ScopeInstantiation) (id : Identity) :
    scope.term (.runtimeRegion id) = .runtimeRegion id := by
  simp only [ScopeInstantiation.term]

/-- Executable lexical names decode to allocated runtime identities, which no
generic substitution rewrites. -/
theorem scopedRegion_image (scope : ScopeInstantiation) (id : Identity) (substitution : Substitution) :
    (scope.term (.scopedRegion id)).substitute substitution = scope.term (.scopedRegion id) := by
  cases found : scope.regions.get id <;>
    simp only [ScopeInstantiation.term,found,Option.map,Option.getD,Term.substitute]

theorem scopedBrand_image (scope : ScopeInstantiation) (id : Identity) (substitution : Substitution) :
    (scope.term (.scopedBrand id)).substitute substitution = scope.term (.scopedBrand id) := by
  cases found : scope.brands.get id <;>
    simp only [ScopeInstantiation.term,found,Option.map,Option.getD,Term.substitute]

/-- The runtime decoding preserves source kinding: it rewrites exactly the two
executable lexical atoms, each of which is kinded from its allocated identity
in any context, and fixes every other atom in place. -/
theorem map_kinding {program : Program} (scope : ScopeInstantiation)
    {source : Context} {term : Term} {kind : Kind} (kinded : Kinding program source term kind) :
    Kinding program source (scope.term term) kind := by
  refine kinded.map_scoped_atoms scope.term (scopedHomomorphism scope) ?_
  intro atom occurs
  cases atom with
  | parameter id kind => rw [parameter_fixed]; exact kinded.occurrence occurs
  | rigid id kind level => rw [rigid_fixed]; exact kinded.occurrence occurs
  | «variable» id kind level => rw [variable_fixed]; exact kinded.occurrence occurs
  | runtimeRegion id => rw [runtimeRegion_fixed]; exact .runtimeRegion
  | scopedRegion id =>
      cases found : scope.regions.get id <;>
        simp only [ScopeInstantiation.term,found,Option.map,Option.getD]
      · exact kinded.occurrence occurs
      · exact .runtimeRegion
  | scopedBrand id =>
      cases found : scope.brands.get id <;>
        simp only [ScopeInstantiation.term,found,Option.map,Option.getD]
      · exact kinded.occurrence occurs
      · exact .runtimeBrand
  | _ => exact True.intro

/-- A declared alias body is scope-closed, so the runtime decoding fixes it. -/
theorem aliasValue_fixed {program : Program} (valid : ProgramWellFormed program)
    {scope : ScopeInstantiation} {id : DeclId} {declaration : AliasDefinition}
    (found : program.alias id = some declaration) : scope.term declaration.value = declaration.value :=
  term_fixed scope declaration.value (valid.scopeClosed
    (List.mem_of_find?_eq_some (Program.alias_lookup found)) declaration.value (by
      simp only [Definition.terms,List.mem_cons_self]))

theorem atomsFixed (scope : ScopeInstantiation) (term : Term) : term.AtomsFixed scope.term := by
  intro atom occurs
  cases atom <;> try exact True.intro
  all_goals simp only [ScopeInstantiation.term]

theorem term_kind (scope : ScopeInstantiation) (term : Term) : (scope.term term).kind = term.kind :=
  ScopeInstantiation.kind scope term

/-- Substitution commutes with the actual runtime decoding: a source opening is
read at the runtime arguments that generic instantiation already produced.
The hypothesis is exactly the existing declaration-template fixedness. -/
theorem map_substituted_values (scope : ScopeInstantiation) (term : Term) (inner : Substitution)
    (fixed : term.AtomsFixed scope.term) :
    scope.term (term.substitute inner) =
      (scope.term term).substitute (inner.map (fun entry => (entry.1,scope.term entry.2))) := by
  cases term
  case parameter id kind =>
    simp only [Term.substitute,Table.get_map_values,ScopeInstantiation.term]
    cases found : inner.get id <;> simp only [Option.map,Option.getD,ScopeInstantiation.term]
  case rigid => rw [rigid_fixed]; simp only [ScopeInstantiation.term,Term.substitute]
  case «variable» => rw [variable_fixed]; simp only [ScopeInstantiation.term,Term.substitute]
  case runtimeRegion => rw [runtimeRegion_fixed]; simp only [ScopeInstantiation.term,Term.substitute]
  case scopedRegion id => simpa only [ScopeInstantiation.term,Term.substitute] using (scopedRegion_image scope id _).symm
  case scopedBrand id => simpa only [ScopeInstantiation.term,Term.substitute] using (scopedBrand_image scope id _).symm
  all_goals simp only [Term.substitute,ScopeInstantiation.term,List.map_map,Function.comp_def]
  all_goals congr 1
  all_goals
    first
    | (apply List.map_congr_left
       intro child member
       exact map_substituted_values scope child inner
         (fixed.child (by simp only [Term.children]; grind)))
    | (refine map_substituted_values scope _ inner (fixed.child ?_)
       simp only [Term.children]
       simp)
termination_by term

/-- A template that the runtime scope does not reinterpret keeps its own
parameter graph, so the checked substitution edge transports to the runtime
image of its result. -/
theorem substitute_values (scope : ScopeInstantiation) (substitution : Substitution) (before after : Term)
    (graph : Substitutes substitution before after) (fixed : scope.term before = before) :
    Substitutes (substitution.map (fun entry => (entry.1,scope.term entry.2))) before (scope.term after) := by
  refine ⟨by rw [term_kind]; exact graph.1,?_,?_⟩
  · rw [graph.2.1,map_substituted_values scope before substitution (fixed ▸ (atomsFixed scope before)),fixed]
  · intro id kind value occurs found
    rw [Table.get_map_values] at found
    obtain ⟨original,located,rfl⟩ := Option.map_eq_some_iff.mp found
    exact (term_kind scope original).trans (graph.2.2 id kind original occurs located)

theorem substitutes_values (scope : ScopeInstantiation) {substitution : Substitution} {before : List Term}
    {after : List Term} (graphs : ListRel (Substitutes substitution) before after)
    (fixed : ∀ term ∈ before, scope.term term = term) :
    ListRel (Substitutes (substitution.map (fun entry => (entry.1,scope.term entry.2)))) before
      (after.map scope.term) := by
  induction graphs with
  | nil => exact .nil
  | cons head _ tail =>
    exact .cons (substitute_values scope _ _ _ head (fixed _ List.mem_cons_self))
      (tail (fun term member => fixed term (List.mem_cons_of_mem _ member)))

theorem rowEquivalent_term (scope : ScopeInstantiation) {left right : Term} (equal : RowEquivalent left right) :
    RowEquivalent (scope.term left) (scope.term right) :=
  equal.map_scoped_atoms scope.term (scopedHomomorphism scope)

end ScopeInstantiation
end Glorious.Language
