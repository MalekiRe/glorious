import GloriousLanguage.PredicateHygiene
import GloriousLanguage.SubstitutionKinding

/-! Binding correspondence for the actual freshening operation. Renaming a
predicate's bound parameters and then instantiating those renamed binders
inserts the original caller values unchanged. -/
namespace Glorious.Language

theorem Binder.freshRename_below_injective (binders : List Binder) (seed : Identity)
    {left right : Identity} (leftBound : left < seed) (rightBound : right < seed)
    (same : Binder.freshRename binders seed left = Binder.freshRename binders seed right) : left = right := by
  by_cases first : left ∈ binders.map (·.id)
  · by_cases second : right ∈ binders.map (·.id)
    · simp only [Binder.freshRename,if_pos first,if_pos second] at same
      exact Nat.add_left_cancel same
    · simp only [Binder.freshRename,if_pos first,if_neg second] at same
      have above := Nat.le_add_right seed left
      rw [same] at above
      exact False.elim (Nat.not_lt_of_ge above rightBound)
  · by_cases second : right ∈ binders.map (·.id)
    · simp only [Binder.freshRename,if_neg first,if_pos second] at same
      have above := Nat.le_add_right seed right
      rw [← same] at above
      exact False.elim (Nat.not_lt_of_ge above leftBound)
    · simpa only [Binder.freshRename,if_neg first,if_neg second] using same

theorem Table.get_rename_keys {α : Type} (rename : Identity → Identity) (table : Table α) (id : Identity)
    (separates : ∀ entry ∈ table, rename entry.1 = rename id → entry.1 = id) :
    Table.get (table.map (fun entry => (rename entry.1,entry.2))) (rename id) = table.get id := by
  induction table with
  | nil => rfl
  | cons first rest ih =>
    by_cases found : first.1 = id
    · simp [Table.get,found]
    · have absent : rename first.1 ≠ rename id := fun same => found (separates first List.mem_cons_self same)
      simpa [Table.get,found,absent] using
        ih (fun entry present => separates entry (List.mem_cons_of_mem _ present))

theorem Term.renameParameters_substitute (rename : Identity → Identity) (term : Term)
    {before after : Substitution}
    (agree : ∀ id kind, Occurs (.parameter id kind) term →
      ((after.get (rename id)).getD (.parameter (rename id) kind)) =
        ((before.get id).getD (.parameter id kind))) :
    (term.renameParameters rename).substitute after = term.substitute before := by
  cases term <;> simp only [Term.renameParameters,Term.substitute,List.map_map,Function.comp_def]
  case parameter id kind => exact agree id kind .here
  all_goals try rfl
  all_goals congr 1
  all_goals first
    | apply List.map_congr_left
      intro child present
      exact child.renameParameters_substitute rename (fun id kind occurs => agree id kind
        (.child (by simp [Term.children,present]) occurs))
    | exact Term.renameParameters_substitute rename _ (fun id kind occurs => agree id kind
        (.child (by simp [Term.children]) occurs))
termination_by term

/-- Simultaneous bound-name replacement does not rename values supplied by
the caller. The freshness premise concerns the finite source support only. -/
theorem Instantiates.freshen_term {binders : List Binder} {values : List Term} {substitution : Substitution}
    (instantiated : Instantiates binders values substitution) (term : Term) (seed : Identity)
    (binderBounds : ∀ binder ∈ binders, binder.id < seed)
    (termBounds : ∀ id ∈ term.parameterIds, id < seed) :
    (term.renameParameters (Binder.freshRename binders seed)).substitute
      (substitution.map (fun entry => (Binder.freshRename binders seed entry.1,entry.2))) =
        term.substitute substitution := by
  apply term.renameParameters_substitute
  intro id kind occurs
  have queryBound := termBounds id occurs.parameterIds
  have lookup := Table.get_rename_keys (Binder.freshRename binders seed) substitution id (by
    intro entry present same
    have inZip := present
    rw [instantiated.2.2] at inZip
    obtain ⟨binder,member,equal⟩ := List.mem_map.mp (List.of_mem_zip inZip).1
    have entryBound : entry.1 < seed := equal ▸ binderBounds binder member
    exact Binder.freshRename_below_injective binders seed entryBound queryBound same)
  rw [lookup]
  cases found : substitution.get id with
  | some value => rfl
  | none =>
    have unbound : id ∉ binders.map (·.id) := by
      intro present
      obtain ⟨binder,member,equal⟩ := List.mem_map.mp present
      obtain ⟨value,_,_,actual⟩ := instantiated.binder_lookup member
      rw [equal,found] at actual
      cases actual
    rw [Binder.freshRename_not_mem unbound]

theorem Instantiates.freshen_binders {binders : List Binder} {values : List Term} {substitution : Substitution}
    (instantiated : Instantiates binders values substitution) (seed : Identity) :
    Instantiates (binders.map (Binder.renameParameters (Binder.freshRename binders seed))) values
      (substitution.map (fun entry => (Binder.freshRename binders seed entry.1,entry.2))) := by
  refine ⟨?_,?_,?_⟩
  · have unique := instantiated.1
    change List.Pairwise (fun left right => left ≠ right) _ at unique ⊢
    simp only [List.map_map,List.pairwise_map,Binder.renameParameters,Function.comp_def] at unique ⊢
    exact unique.imp_of_mem (fun first second different same =>
      different (Binder.freshRename_injective_on first second same))
  · have alignment := instantiated.2.1
    generalize Binder.freshRename binders seed = rename
    clear instantiated substitution
    induction alignment with
    | nil => exact .nil
    | cons kind tail ih => exact .cons kind ih
  · rw [instantiated.2.2]
    have maps : Prod.map (Binder.freshRename binders seed) (id : Term → Term) =
        (fun entry => (Binder.freshRename binders seed entry.1,entry.2)) := by
      funext entry
      cases entry
      rfl
    simpa only [maps,List.map_map,Function.comp_def,Binder.renameParameters] using
      (List.zip_map_left (f := Binder.freshRename binders seed) (l₁ := binders.map (·.id)) (l₂ := values)).symm

theorem Instantiates.congr_binders {before after : List Binder} {values : List Term} {substitution : Substitution}
    (instantiated : Instantiates before values substitution)
    (related : ListRel (fun first second => first.id = second.id ∧ first.kind = second.kind) before after) :
    Instantiates after values substitution := by
  have ids : before.map (·.id) = after.map (·.id) := by
    clear instantiated values substitution
    induction related with
    | nil => rfl
    | cons head _ ih => simp only [List.map_cons,head.1,ih]
  refine ⟨ids ▸ instantiated.1,?_,ids ▸ instantiated.2.2⟩
  have alignment := instantiated.2.1
  clear instantiated substitution ids
  induction related generalizing values with
  | nil => cases alignment; exact .nil
  | cons head _ ih =>
    cases alignment with
    | cons kind tail => exact .cons (head.2.symm.trans kind) (ih tail)

private theorem ListRel.map_mapIdx {α β γ : Type} {relation : β → γ → Prop}
    (values : List α) (left : α → β) (right : Nat → α → γ)
    (related : ∀ index value, value ∈ values → relation (left value) (right index value)) :
    ListRel relation (values.map left) (values.mapIdx right) := by
  induction values generalizing right with
  | nil => exact .nil
  | cons first rest ih =>
    simp only [List.map_cons,List.mapIdx_cons]
    exact .cons (related 0 first List.mem_cons_self)
      (ih (fun index value => right (index + 1) value)
        (fun index value member => related (index + 1) value (List.mem_cons_of_mem _ member)))

/-- The binders actually returned by hygienic predicate substitution admit
exactly the original ordered caller arguments under the corresponding fresh
keys. Transformed defaults do not change binder kind or argument position. -/
theorem SubstituteConstraint.quantified_instantiation {substitution argumentsSub : Substitution}
    {binders afterBinders : List Binder} {requirements afterRequirements : List Constraint} {values : List Term}
    (substituted : SubstituteConstraint substitution (.quantified binders requirements)
      (.quantified afterBinders afterRequirements)) (instantiated : Instantiates binders values argumentsSub) :
    Instantiates afterBinders values (argumentsSub.map (fun entry =>
      (Binder.freshRename binders ((Constraint.quantified binders requirements).freshSeed substitution) entry.1,entry.2))) := by
  have graph := substituted.2
  simp only [Constraint.substitute] at graph
  obtain ⟨bindersEqual,_⟩ := Constraint.quantified.inj graph
  rw [bindersEqual]
  apply (instantiated.freshen_binders ((Constraint.quantified binders requirements).freshSeed substitution)).congr_binders
  apply ListRel.map_mapIdx
  intro index binder _
  exact ⟨rfl,rfl⟩

theorem SubstituteConstraint.quantified_binding_correspondence {substitution argumentsSub : Substitution}
    {binders afterBinders : List Binder} {requirements afterRequirements : List Constraint} {values : List Term}
    (substituted : SubstituteConstraint substitution (.quantified binders requirements)
      (.quantified afterBinders afterRequirements)) (instantiated : Instantiates binders values argumentsSub) :
    ∃ freshInstance,
      Instantiates afterBinders values freshInstance ∧
      ∀ (term : Term), (∀ id ∈ term.parameterIds, id ∈ (Constraint.quantified binders requirements).parameterIds) →
        (term.renameParameters (Binder.freshRename binders
          ((Constraint.quantified binders requirements).freshSeed substitution))).substitute freshInstance =
            term.substitute argumentsSub := by
  refine ⟨_,substituted.quantified_instantiation instantiated,?_⟩
  intro term supported
  apply instantiated.freshen_term
  · intro binder member
    apply Constraint.parameter_lt_freshSeed _ substitution
    simp only [Constraint.parameterIds,Constraint.boundIds]
    exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨binder,member,rfl⟩))
  · intro id present
    exact Constraint.parameter_lt_freshSeed _ substitution (supported id present)

end Glorious.Language
