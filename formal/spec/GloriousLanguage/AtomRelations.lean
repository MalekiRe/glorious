import GloriousLanguage.AtomInstantiation
import GloriousLanguage.PredicateInterpretation

/-! Relational consequences of the existing constructor homomorphism.
An atom may become compound; congruence therefore treats an identical atomic
head by reflexivity instead of asserting that every image has the old head. -/
namespace Glorious.Language

open PredicateSemantics

theorem AtomHomomorphism.same_or_children {map : Term → Term} (shape : AtomHomomorphism map)
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

theorem AtomHomomorphism.congr_relation {map : Term → Term} (shape : AtomHomomorphism map)
    {relation : Term → Term → Prop} (reflexive : ∀ term, relation term term)
    (congruent : ∀ {left right}, SameHead left right → ListRel relation left.children right.children → relation left right)
    {left right : Term} (same : SameHead left right)
    (children : ListRel (fun first second => relation (map first) (map second)) left.children right.children) :
    relation (map left) (map right) := by
  rcases shape.same_or_children same with rfl | ⟨first,second⟩
  · exact reflexive _
  · rw [first,second]
    apply congruent
    · exact (Term.sameHead_mapChildren left map).symm.trans (same.trans (Term.sameHead_mapChildren right map))
    · rw [Term.mapChildren_children,Term.mapChildren_children]
      generalize left.children = firstList at children ⊢
      generalize right.children = secondList at children ⊢
      induction children with
      | nil => exact .nil
      | cons head _ tail => exact .cons head tail

theorem AtomHomomorphism.child_head {map : Term → Term} (shape : AtomHomomorphism map)
    {left right child : Term} (same : SameHead left right) (member : child ∈ right.children) :
    SameHead left (map right) ∧ (map right).children = right.children.map map := by
  have mapped : map right = right.mapChildren map := by
    rw [shape]
    cases right <;> try rfl
    all_goals simp [Term.children] at member
  rw [mapped]
  exact ⟨same.trans (Term.sameHead_mapChildren right map),Term.mapChildren_children _ _⟩

theorem AtomHomomorphism.list_at {map : Term → Term} {relation : Term → Term → Prop} {left right : List Term}
    (related : ∀ (index : Nat) first second, left[index]? = some first → right[index]? = some second →
      relation (map first) (map second)) :
    ∀ (index : Nat) first second, (left.map map)[index]? = some first →
      (right.map map)[index]? = some second → relation first second := by
  intro index first second leftAt rightAt
  rw [List.getElem?_map] at leftAt rightAt
  obtain ⟨a,firstAt,rfl⟩ := Option.map_eq_some_iff.mp leftAt
  obtain ⟨b,secondAt,rfl⟩ := Option.map_eq_some_iff.mp rightAt
  exact related index a b firstAt secondAt

theorem Term.map_substituted_values (term : Term) (inner : Substitution) (map : Term → Term)
    (shape : AtomHomomorphism map) (parameters : ∀ id kind, map (.parameter id kind) = .parameter id kind)
    (fixed : term.AtomsFixed map) :
    map (term.substitute inner) = term.substitute (inner.map (fun entry => (entry.1,map entry.2))) := by
  cases term
  case parameter id kind =>
    simp only [Term.substitute,Table.get_map_values]
    cases found : inner.get id <;> simp only [Option.map,Option.getD,parameters]
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
       exact child.map_substituted_values inner map shape parameters
         (fixed.child (by simp only [Term.children,List.mem_append]; grind)))
    | (exact Term.map_substituted_values _ inner map shape parameters
         (fixed.child (by simp [Term.children])))
termination_by term

theorem Substitutes.map_atoms_fixed {before after : Term} {inner : Substitution}
    (graph : Substitutes inner before after) (map : Term → Term) (shape : AtomHomomorphism map)
    (parameters : ∀ id kind, map (.parameter id kind) = .parameter id kind)
    (fixed : before.AtomsFixed map) (kinds : ∀ term, (map term).kind = term.kind) :
    Substitutes (inner.map (fun entry => (entry.1,map entry.2))) before (map after) := by
  refine ⟨by rw [kinds]; exact graph.1,?_,?_⟩
  · rw [graph.2.1]
    exact before.map_substituted_values inner map shape parameters fixed
  · intro id kind value occurs found
    rw [Table.get_map_values] at found
    obtain ⟨original,located,rfl⟩ := Option.map_eq_some_iff.mp found
    exact (kinds original).trans (graph.2.2 id kind original occurs located)

theorem ListRel.map_atoms_fixed {before after : List Term} {inner : Substitution}
    (graphs : ListRel (Substitutes inner) before after) (map : Term → Term) (shape : AtomHomomorphism map)
    (parameters : ∀ id kind, map (.parameter id kind) = .parameter id kind)
    (fixed : ∀ term ∈ before, term.AtomsFixed map) (kinds : ∀ term, (map term).kind = term.kind) :
    ListRel (Substitutes (inner.map (fun entry => (entry.1,map entry.2)))) before (after.map map) := by
  induction graphs with
  | nil => exact .nil
  | cons head _ tail =>
    exact .cons (head.map_atoms_fixed map shape parameters (fixed _ List.mem_cons_self) kinds)
      (tail (fun term member => fixed term (List.mem_cons_of_mem _ member)))

theorem RowEquivalent.map_atoms {left right : Term} (equal : RowEquivalent left right)
    (map : Term → Term) (shape : AtomHomomorphism map) : RowEquivalent (map left) (map right) := by
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

end Glorious.Language
