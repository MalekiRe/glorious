import GloriousLanguage.LogicalSubstitution

/-! Atomic predicate congruence is derived from the authoritative hygienic
template rule. The finite table below only witnesses that rule; it is not an
additional source analysis or an alternative logical equality judgment. -/
namespace Glorious.Language

private theorem Table.get_of_functional_member {α : Type} {table : Table α} {key : Identity} {value : α}
    (member : (key,value) ∈ table)
    (functional : ∀ entry ∈ table, entry.1 = key → entry.2 = value) : table.get key = some value := by
  induction table with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons head tail ih =>
    by_cases same : head.1 = key
    · simp only [Table.get,List.find?_cons,same,beq_self_eq_true,Option.map_some]
      exact congrArg some (functional head List.mem_cons_self same)
    · have present : (key,value) ∈ tail := by
        rcases List.mem_cons.mp member with equal | present
        · exact False.elim (same (congrArg Prod.fst equal.symm))
        · exact present
      simpa only [Table.get,List.find?_cons,show (head.1 == key) = false from beq_eq_false_iff_ne.mpr same] using
        ih present (fun entry located => functional entry (List.mem_cons_of_mem _ located))

private def predicateSlots (terms : List Term) : Substitution :=
  terms.mapIdx (fun index term => (index,term))

private theorem predicateSlots_lookup {terms : List Term} {index : Nat} {term : Term}
    (atIndex : terms[index]? = some term) : (predicateSlots terms).get index = some term := by
  apply Table.get_of_functional_member
  · apply List.mem_iff_getElem?.mpr
    exact ⟨index,by simp only [predicateSlots,List.getElem?_mapIdx,atIndex,Option.map_some]⟩
  · intro entry member same
    obtain ⟨position,bound,equal⟩ := List.mem_mapIdx.mp member
    cases equal
    simp only at same
    subst position
    exact (List.getElem?_eq_some_iff.mp atIndex).2

private noncomputable def predicateSlot (terms : List Term) (term : Term) : Identity :=
  open Classical in
  if member : term ∈ terms then Classical.choose (List.mem_iff_getElem?.mp member) else 0

private theorem predicateSlot_lookup {terms : List Term} {term : Term} (member : term ∈ terms) :
    (predicateSlots terms).get (predicateSlot terms term) = some term := by
  unfold predicateSlot
  rw [dif_pos member]
  exact predicateSlots_lookup (Classical.choose_spec (List.mem_iff_getElem?.mp member))

private theorem substitutes_parameter {substitution : Substitution} {id : Identity} {kind : Kind} {value : Term}
    (found : substitution.get id = some value) (kinded : value.kind = kind) :
    Substitutes substitution (.parameter id kind) value := by
  refine ⟨kinded.symm,by simp only [Term.substitute,found,Option.getD_some],?_⟩
  intro other otherKind replacement occurs located
  cases occurs with
  | here => rw [found] at located; cases Option.some.inj located; exact kinded
  | child member _ => exact False.elim (List.not_mem_nil member)

def Constraint.Atomic : Constraint → Prop
  | .quantified .. => False
  | _ => True

private theorem Constraint.atomic_map_substitutes {constraint : Constraint} (atomic : constraint.Atomic)
    {substitution : Substitution} {before after : Term → Term}
    (graphs : ∀ term ∈ constraint.terms, Substitutes substitution (before term) (after term)) :
    SubstituteConstraint substitution (constraint.mapTerms before) (constraint.mapTerms after) := by
  have equal : constraint.terms.map after = constraint.terms.map (fun term => (before term).substitute substitution) :=
    List.map_congr_left (fun term member => (graphs term member).2.1)
  have checked : ∀ term ∈ constraint.terms.map before, Substitutes substitution term (term.substitute substitution) := by
    intro term member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    rw [← (graphs original present).2.1]
    exact graphs original present
  cases constraint <;> simp only [Constraint.Atomic] at atomic
  all_goals try contradiction
  all_goals simp only [Constraint.terms,List.map_cons,List.map_nil,List.cons.injEq] at equal checked
  all_goals try simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    List.mem_map,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂] at checked
  all_goals simp only [SubstituteConstraint,Constraint.mapTerms,Constraint.SubstitutionAdmissible,
    Constraint.substitute,List.mem_cons,List.mem_map,forall_eq_or_imp,forall_exists_index,and_imp,List.map_map,Function.comp_def]
  all_goals constructor
  all_goals try { simpa only [forall_apply_eq_imp_iff₂] using checked }
  all_goals simp_all only [and_true]

/-- Replacing every actual atomic operand by a logically equal term is an
instance of the existing two-substitution predicate rule. Source admission
supplies equality's kind law, including for the auxiliary parameter template. -/
theorem Entails.congr_atomic_map_iff {program : Program} (valid : ProgramWellFormed program)
    {context : Context} (contextKinded : ∀ constraint ∈ context.assumptions, ConstraintKinded program context constraint)
    {constraint : Constraint} (atomic : constraint.Atomic)
    (transform : Term → Term) (equal : ∀ term ∈ constraint.terms, Equal program context term (transform term)) :
    Entails program context constraint ↔ Entails program context (constraint.mapTerms transform) := by
  let original := predicateSlots constraint.terms
  let changed : Substitution := original.map (fun entry => (entry.1,transform entry.2))
  let abstract := fun term : Term => Term.parameter (predicateSlot constraint.terms term) term.kind
  have first : SubstituteConstraint original (constraint.mapTerms abstract) (constraint.mapTerms id) :=
    constraint.atomic_map_substitutes atomic (fun _ member => substitutes_parameter (predicateSlot_lookup member) rfl)
  have second : SubstituteConstraint changed (constraint.mapTerms abstract) (constraint.mapTerms transform) := by
    apply constraint.atomic_map_substitutes atomic
    intro term member
    apply substitutes_parameter
    · rw [Table.get_map_values,predicateSlot_lookup member]
      rfl
    · exact ((equal term member).kind_eq valid contextKinded).symm
  have lookupEqual : ∀ id kind, Equal program context ((original.get id).getD (.parameter id kind))
      ((changed.get id).getD (.parameter id kind)) := by
    intro id kind
    change Equal program context _ ((Table.get (original.map _) id).getD _)
    rw [Table.get_map_values]
    cases found : original.get id with
    | none => exact .refl
    | some term =>
      apply equal term
      obtain ⟨entry,located,entryValue⟩ := Option.map_eq_some_iff.mp found
      obtain ⟨index,bound,entryEqual⟩ := List.mem_mapIdx.mp (List.mem_of_find?_eq_some located)
      rw [← entryValue,← entryEqual]
      exact List.getElem_mem bound
  have identity : constraint.mapTerms id = constraint := by
    cases constraint <;> simp only [Constraint.mapTerms,List.map_id,id_eq]
    exact False.elim atomic
  constructor
  · intro held
    exact .congr (.substitution lookupEqual first second) (identity.symm ▸ held)
  · intro held
    exact identity ▸ Entails.congr (.substitution (fun id kind => (lookupEqual id kind).symm) second first) held

theorem Entails.congr_atomic_map {program : Program} (valid : ProgramWellFormed program)
    {context : Context} (contextKinded : ∀ constraint ∈ context.assumptions, ConstraintKinded program context constraint)
    {constraint : Constraint} (held : Entails program context constraint) (atomic : constraint.Atomic)
    (transform : Term → Term) (equal : ∀ term ∈ constraint.terms, Equal program context term (transform term)) :
    Entails program context (constraint.mapTerms transform) :=
  (Entails.congr_atomic_map_iff valid contextKinded atomic transform equal).mp held

end Glorious.Language
