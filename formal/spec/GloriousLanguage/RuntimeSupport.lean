import GloriousLanguage.InstantiationEquivariance

/-! Finite generativity support and its fresh-name permutation extension.
Allocated identities may be expired; these bounds never establish storage
liveness or permission to dereference a raw pointer. -/
namespace Glorious.Language

theorem Term.mapChildren_eq_runtimeRegion (f : Term → Term) {term : Term} {id : Identity}
    (same : term.mapChildren f = .runtimeRegion id) : term = .runtimeRegion id := by
  cases term <;> simp only [Term.mapChildren] at same <;> cases same <;> rfl

theorem Term.RuntimeRegionsBelow.mapChildren {bound : Identity} {term : Term}
    (supported : term.RuntimeRegionsBelow bound) (f : Term → Term)
    (children : ∀ child ∈ term.children, (f child).RuntimeRegionsBelow bound) :
    (term.mapChildren f).RuntimeRegionsBelow bound := by
  intro id occurs
  generalize mapped : term.mapChildren f = result at occurs
  cases occurs with
  | here =>
      have same := Term.mapChildren_eq_runtimeRegion f mapped
      subst term
      exact supported id .here
  | child member nested =>
      rw [← mapped,Term.mapChildren_children] at member
      obtain ⟨original,inOriginal,rfl⟩ := List.mem_map.mp member
      exact children original inOriginal id nested

theorem Term.substitute_runtimeRegionsBelow (substitution : Substitution) (term : Term) (bound : Identity)
    (supported : term.RuntimeRegionsBelow bound)
    (arguments : ∀ id value, substitution.get id = some value → value.RuntimeRegionsBelow bound) :
    (term.substitute substitution).RuntimeRegionsBelow bound := by
  by_cases parameter : ∃ id kind, term = .parameter id kind
  · obtain ⟨id,kind,rfl⟩ := parameter
    cases found : substitution.get id with
    | none => simpa only [Term.substitute,found,Option.getD] using supported
    | some value => simpa only [Term.substitute,found,Option.getD] using arguments id value found
  · rw [Term.substitute_eq_mapChildren substitution (by
      intro id kind same
      exact parameter ⟨id,kind,same⟩)]
    apply supported.mapChildren
    intro child member
    exact child.substitute_runtimeRegionsBelow substitution bound (supported.child member) arguments
termination_by term
decreasing_by exact Term.child_sizeOf member

theorem Instantiates.runtimeRegionsBelow {binders : List Binder} {arguments : List Term} {substitution : Substitution}
    (instantiated : Instantiates binders arguments substitution) {bound : Identity}
    (supported : ∀ argument ∈ arguments, argument.RuntimeRegionsBelow bound) {term : Term}
    (lexical : term.Lexical) : (term.substitute substitution).RuntimeRegionsBelow bound :=
  term.substitute_runtimeRegionsBelow substitution bound (lexical.runtimeRegionsBelow bound)
    (fun _ _ found => supported _ (instantiated.argument_of_get found))

theorem Term.renameRuntimeRegions_comp (outer inner : Identity → Identity) (term : Term) :
    (term.renameRuntimeRegions inner).renameRuntimeRegions outer =
      term.renameRuntimeRegions (fun id => outer (inner id)) := by
  cases term <;> simp only [Term.renameRuntimeRegions]
  all_goals try rfl
  all_goals try simp only [List.map_map,Function.comp_def]
  all_goals
    congr 1
    all_goals first
    | exact Term.renameRuntimeRegions_comp outer inner _
    | apply List.map_congr_left
      intro child _
      exact child.renameRuntimeRegions_comp outer inner
termination_by term

theorem Term.renameRuntimeRegions_id (term : Term) : term.renameRuntimeRegions id = term := by
  cases term <;> simp only [Term.renameRuntimeRegions,id_eq]
  all_goals try rfl
  all_goals
    congr 1
    all_goals first
    | exact Term.renameRuntimeRegions_id _
    | apply List.map_eq_self_of
      intro child _
      exact child.renameRuntimeRegions_id
termination_by term

theorem Term.renameRuntimeRegions_congr (left right : Identity → Identity) (term : Term)
    (agrees : ∀ id, Occurs (.runtimeRegion id) term → left id = right id) :
    term.renameRuntimeRegions left = term.renameRuntimeRegions right := by
  cases term <;> simp only [Term.renameRuntimeRegions]
  case runtimeRegion id => exact congrArg Term.runtimeRegion (agrees id .here)
  all_goals try rfl
  all_goals
    congr 1
    all_goals first
    | apply List.map_congr_left
      intro child member
      exact child.renameRuntimeRegions_congr left right (fun id occurs => agrees id
        (.child (by simp [Term.children,member]) occurs))
    | exact Term.renameRuntimeRegions_congr left right _ (fun id occurs => agrees id
        (.child (by simp [Term.children]) occurs))
termination_by term

theorem Term.renameRuntimeRegions_involutive (rename : Identity → Identity)
    (involutive : ∀ id, rename (rename id) = id) (term : Term) :
    (term.renameRuntimeRegions rename).renameRuntimeRegions rename = term := by
  rw [Term.renameRuntimeRegions_comp]
  have actions : (fun id => rename (rename id)) = id := funext involutive
  rw [actions,term.renameRuntimeRegions_id]

theorem Term.renameRuntimeRegions_injective (rename : Identity → Identity)
    (involutive : ∀ id, rename (rename id) = id) : Function.Injective (Term.renameRuntimeRegions rename) := by
  intro left right same
  have twice := congrArg (Term.renameRuntimeRegions rename) same
  simpa only [Term.renameRuntimeRegions_involutive rename involutive] using twice

theorem Term.renameRuntimeRegions_occurs_preimage (rename : Identity → Identity) {needle term : Term}
    (occurs : Occurs needle (term.renameRuntimeRegions rename)) :
    ∃ original, Occurs original term ∧ original.renameRuntimeRegions rename = needle := by
  generalize renamed : term.renameRuntimeRegions rename = result at occurs
  induction occurs generalizing term with
  | here => exact ⟨term,.here,renamed⟩
  | @child parent child member nested ih =>
      have children : (term.renameRuntimeRegions rename).children = term.children.map (Term.renameRuntimeRegions rename) := by
        cases term <;> simp only [Term.renameRuntimeRegions,Term.children,List.map_cons,List.map_nil,List.map_append]
      rw [← renamed,children] at member
      obtain ⟨original,inOriginal,atChild⟩ := List.mem_map.mp member
      obtain ⟨ancestor,inside,atNeedle⟩ := ih atChild
      exact ⟨ancestor,.child inOriginal inside,atNeedle⟩

theorem Term.renameRuntimeRegions_eq_runtimeRegion (rename : Identity → Identity) {term : Term} {id : Identity}
    (same : term.renameRuntimeRegions rename = .runtimeRegion id) :
    ∃ original, term = .runtimeRegion original ∧ rename original = id := by
  cases term <;> simp only [Term.renameRuntimeRegions] at same <;> cases same
  exact ⟨_,rfl,rfl⟩

theorem Term.RuntimeRegionsBelow.rename {lower upper : Identity} {term : Term}
    (supported : term.RuntimeRegionsBelow lower) (rename : Identity → Identity)
    (bounds : ∀ id, id < lower → rename id < upper) :
    (term.renameRuntimeRegions rename).RuntimeRegionsBelow upper := by
  intro id occurs
  obtain ⟨original,nested,same⟩ := Term.renameRuntimeRegions_occurs_preimage rename occurs
  obtain ⟨source,rfl,rfl⟩ := Term.renameRuntimeRegions_eq_runtimeRegion rename same
  exact bounds source (supported source nested)

namespace Execution

/-- The fresh interval is swapped back, not fixed. On all previously allocated
identities this permutation agrees exactly with the executable relocation. -/
def freshSwap (selected : List Identity) (base id : Identity) : Identity :=
  if id ∈ selected then base + id else
    if base ≤ id ∧ id - base ∈ selected then id - base else id

theorem freshSwap_selected {selected : List Identity} {base id : Identity} (member : id ∈ selected) :
    freshSwap selected base id = base + id := by simp only [freshSwap,if_pos member]

theorem freshSwap_image {selected : List Identity} {base id : Identity}
    (bounded : ∀ item ∈ selected, item < base) (member : id ∈ selected) :
    freshSwap selected base (base+id) = id := by
  have outside : base+id ∉ selected := fun included =>
    Nat.not_lt_of_ge (Nat.le_add_right base id) (bounded (base+id) included)
  simp [freshSwap,outside,member,Nat.le_add_right]

theorem freshSwap_below {selected : List Identity} {base id : Identity} (bound : id < base) :
    freshSwap selected base id = relocateId selected base id := by
  by_cases member : id ∈ selected
  · simp [freshSwap,relocateId,member]
  · simp [freshSwap,relocateId,member,Nat.not_le.mpr bound]

theorem freshSwap_involutive {selected : List Identity} {base : Identity}
    (bounded : ∀ item ∈ selected, item < base) (id : Identity) :
    freshSwap selected base (freshSwap selected base id) = id := by
  by_cases member : id ∈ selected
  · rw [freshSwap_selected member,freshSwap_image bounded member]
  · by_cases image : base ≤ id ∧ id-base ∈ selected
    · have once : freshSwap selected base id = id-base := by simp only [freshSwap,if_neg member,if_pos image]
      rw [once,freshSwap_selected image.2]
      exact Nat.add_sub_of_le image.1
    · simp only [freshSwap,if_neg member,if_neg image]

theorem freshSwap_injective {selected : List Identity} {base : Identity}
    (bounded : ∀ item ∈ selected, item < base) : Function.Injective (freshSwap selected base) := by
  intro left right same
  have twice := congrArg (freshSwap selected base) same
  simpa only [freshSwap_involutive bounded] using twice

theorem freshSwap_surjective {selected : List Identity} {base : Identity}
    (bounded : ∀ item ∈ selected, item < base) : Function.Surjective (freshSwap selected base) :=
  fun id => ⟨freshSwap selected base id,freshSwap_involutive bounded id⟩

theorem Relocation.term_eq_permutation (map : Relocation) {term : Term}
    (supported : term.RuntimeRegionsBelow map.regionBase) :
    map.term term = term.renameRuntimeRegions (freshSwap map.regions map.regionBase) := by
  apply term.renameRuntimeRegions_congr
  intro id occurs
  exact (freshSwap_below (supported id occurs)).symm

theorem Relocation.permutation_involutive (map : Relocation)
    (bounded : ∀ id ∈ map.regions, id < map.regionBase) (term : Term) :
    (term.renameRuntimeRegions (freshSwap map.regions map.regionBase)).renameRuntimeRegions
      (freshSwap map.regions map.regionBase) = term :=
  term.renameRuntimeRegions_involutive _ (freshSwap_involutive bounded)

theorem Relocation.term_runtimeRegionsBelow (map : Relocation) {beforeBound : Identity} {term : Term}
    (supported : term.RuntimeRegionsBelow beforeBound) :
    (map.term term).RuntimeRegionsBelow (map.regionBase+beforeBound) := by
  apply supported.rename map.region
  intro id bound
  by_cases included : id ∈ map.regions
  · simpa only [Relocation.region,relocateId,if_pos included] using Nat.add_lt_add_left bound map.regionBase
  · simpa only [Relocation.region,relocateId,if_neg included] using
      Nat.lt_of_lt_of_le bound (Nat.le_add_left beforeBound map.regionBase)

end Execution
end Glorious.Language
