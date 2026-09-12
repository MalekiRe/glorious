import GloriousLanguage.AtomRelations

/-! Raw invocation openings need not instantiate every declaration binder.
Their mapped table retains every old entry and supplies only missing source
parameters from the actual declaration scope. Fully instantiated declaration
openings continue to use the exact mapped `Instantiates` table instead. -/
namespace Glorious.Language

theorem Table.get_append_choice {α : Type} (left right : Table α) (id : Identity) :
    (left ++ right).get id = match left.get id with | some value => some value | none => right.get id := by
  cases found : left.find? (fun entry => entry.1 == id) <;>
    simp only [Table.get,List.find?_append,found,Option.map,Option.or]

private theorem mapped_binder_lookup {binders : List Binder} (unique : (binders.map (·.id)).Nodup)
    (map : Term → Term) {binder : Binder} (member : binder ∈ binders) :
    Table.get (binders.map (fun entry => (entry.id,map (.parameter entry.id entry.kind)))) binder.id =
      some (map (.parameter binder.id binder.kind)) := by
  induction binders with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons first rest ih =>
    simp only [List.map_cons,List.nodup_cons] at unique
    rcases List.mem_cons.mp member with rfl | present
    · simp only [List.map_cons,Table.get,List.find?_cons,beq_self_eq_true,Option.map_some]
    · have different : first.id ≠ binder.id := by
        intro same
        exact unique.1 (same.symm ▸ List.mem_map.mpr ⟨binder,present,rfl⟩)
      simpa [Table.get,different] using ih unique.2 present

def Binder.completeAtomOpening (binders : List Binder) (inner : Substitution) (map : Term → Term) : Substitution :=
  inner.map (fun entry => (entry.1,map entry.2)) ++
    binders.map (fun binder => (binder.id,map (.parameter binder.id binder.kind)))

theorem Binder.completeAtomOpening_lookup {binders : List Binder} (unique : (binders.map (·.id)).Nodup)
    (inner : Substitution) (map : Term → Term) {binder : Binder} (member : binder ∈ binders) :
    (completeAtomOpening binders inner map).get binder.id =
      some (map ((inner.get binder.id).getD (.parameter binder.id binder.kind))) := by
  rw [completeAtomOpening,Table.get_append_choice,Table.get_map_values]
  cases found : inner.get binder.id <;> simp only [Option.map,Option.getD]
  exact mapped_binder_lookup unique map member

theorem Term.map_opening_values (term : Term) (inner outer : Substitution) (map : Term → Term)
    (shape : AtomHomomorphism map) (fixed : term.AtomsFixed map)
    (parameters : ∀ id kind, Occurs (.parameter id kind) term →
      map ((inner.get id).getD (.parameter id kind)) = (outer.get id).getD (.parameter id kind)) :
    map (term.substitute inner) = term.substitute outer := by
  cases term
  case parameter id kind => simpa only [Term.substitute] using parameters id kind .here
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
       exact child.map_opening_values inner outer map shape
         (fixed.child (by simp only [Term.children,List.mem_append]; grind))
         (fun id kind occurs => parameters id kind (.child (by simp only [Term.children,List.mem_append]; grind) occurs)))
    | (exact Term.map_opening_values _ inner outer map shape
         (fixed.child (by simp [Term.children]))
         (fun id kind occurs => parameters id kind (.child (by simp [Term.children]) occurs)))
termination_by term

theorem Substitutes.map_completed {program : Program} {source : Context} {before after : Term} {kind : Kind}
    {inner : Substitution} (graph : Substitutes inner before after) (kinded : Kinding program source before kind)
    (unique : (source.binders.map (·.id)).Nodup) (map : Term → Term) (shape : AtomHomomorphism map)
    (fixed : before.AtomsFixed map) (kinds : ∀ term, (map term).kind = term.kind) :
    Substitutes (Binder.completeAtomOpening source.binders inner map) before (map after) := by
  refine ⟨by rw [kinds]; exact graph.1,?_,?_⟩
  · rw [graph.2.1]
    apply before.map_opening_values inner _ map shape fixed
    intro id kind occurs
    obtain ⟨binder,member,sameId,sameKind⟩ := kinded.parameter_occurs occurs
    have found := Binder.completeAtomOpening_lookup unique inner map member
    rw [sameId,sameKind] at found
    simp only [found,Option.getD_some]
  · intro id kind value occurs found
    obtain ⟨binder,member,sameId,sameKind⟩ := kinded.parameter_occurs occurs
    have actual := Binder.completeAtomOpening_lookup unique inner map member
    rw [sameId,sameKind,found] at actual
    cases Option.some.inj actual
    rw [kinds]
    cases original : inner.get id with
    | none => simp only [Option.getD_none,Term.kind]
    | some selected => exact graph.2.2 id kind selected occurs original

theorem ListRel.map_completed {program : Program} {source : Context} {before after : List Term} {kind : Kind}
    {inner : Substitution} (graphs : ListRel (Substitutes inner) before after)
    (typed : ∀ term ∈ before, Kinding program source term kind) (unique : (source.binders.map (·.id)).Nodup)
    (map : Term → Term) (shape : AtomHomomorphism map) (fixed : ∀ term ∈ before, term.AtomsFixed map)
    (kinds : ∀ term, (map term).kind = term.kind) :
    ListRel (Substitutes (Binder.completeAtomOpening source.binders inner map)) before (after.map map) := by
  induction graphs with
  | nil => exact .nil
  | cons head _ tail =>
    exact .cons (head.map_completed (typed _ List.mem_cons_self) unique map shape (fixed _ List.mem_cons_self) kinds)
      (tail (fun term member => typed term (List.mem_cons_of_mem _ member))
        (fun term member => fixed term (List.mem_cons_of_mem _ member)))

theorem ListRel.map_instantiated_kinded {program : Program} {source : Context} {before after values : List Term}
    {inner : Substitution} (graphs : ListRel (Substitutes inner) before after)
    (typed : ∀ term ∈ before, Kinding program source term term.kind)
    (instantiated : Instantiates source.binders values inner)
    (map : Term → Term) (shape : AtomHomomorphism map) (fixed : ∀ term ∈ before, term.AtomsFixed map)
    (kinds : ∀ term, (map term).kind = term.kind) :
    ListRel (Substitutes (inner.map (fun entry => (entry.1,map entry.2)))) before (after.map map) := by
  induction graphs with
  | nil => exact .nil
  | cons head _ tail =>
    exact .cons (head.map_instantiated (typed _ List.mem_cons_self) instantiated map shape (fixed _ List.mem_cons_self) kinds)
      (tail (fun term member => typed term (List.mem_cons_of_mem _ member))
        (fun term member => fixed term (List.mem_cons_of_mem _ member)))

end Glorious.Language
