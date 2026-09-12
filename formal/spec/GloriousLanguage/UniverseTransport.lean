import GloriousLanguage.PredicateAdmission

/-! Universe admission is determined by the levels of atoms that actually
occur. The same kinding producer handles ordinary substitutions, fresh rigid
renamings and lowering into an older universe; this is not logical weakening
of a universally quantified proof. -/
namespace Glorious.Language

theorem Kinding.noLeak {program : Program} {context : Context} {term : Term} {kind : Kind}
    (kinded : Kinding program context term kind) : NoLeak context.universeLevel term :=
  fun _ _ _ occurs => kinded.rigid_level occurs

/-- Lowering an existing kinding derivation needs exactly the actual rigid
and inference-variable bounds, not the old context's maximum level. -/
theorem Kinding.universe {program : Program} {context : Context} {term : Term} {kind : Kind}
    (kinded : Kinding program context term kind) (level : Nat)
    (rigids : NoLeak level term)
    (variables : ∀ id variableKind atomLevel, Occurs (.variable id variableKind atomLevel) term → atomLevel ≤ level) :
    Kinding program { context with universeLevel := level } term kind := by
  apply kinded.map_atoms (target := { context with universeLevel := level }) id (by
    intro term
    cases term <;> simp only [id,Term.mapChildren,List.map_id]) _
    (fun _ member => member) (fun _ member => member)
  intro atom occurs
  cases atom <;> try exact True.intro
  case parameter identity kind =>
    obtain ⟨binder,member,sameId,sameKind⟩ := kinded.parameter_occurs occurs
    simpa only [id,sameId,sameKind] using
      Kinding.parameter (program := program) (context := { context with universeLevel := level }) member
  case rigid id kind atomLevel => exact .rigid (rigids id kind atomLevel occurs)
  case «variable» id kind atomLevel => exact .variable (variables id kind atomLevel occurs)
  case runtimeRegion => exact .runtimeRegion

theorem Kinding.universe_iff {program : Program} {context : Context} {term : Term} {kind : Kind}
    (kinded : Kinding program context term kind) (level : Nat) :
    Kinding program { context with universeLevel := level } term kind ↔
      NoLeak level term ∧
        ∀ id variableKind atomLevel, Occurs (.variable id variableKind atomLevel) term → atomLevel ≤ level :=
  ⟨fun checked => ⟨checked.noLeak,fun _ _ _ occurs => checked.variable_level occurs⟩,
    fun admitted => kinded.universe level admitted.1 admitted.2⟩

theorem Kinding.raiseUniverse {program : Program} {context : Context} {term : Term} {kind : Kind}
    (kinded : Kinding program context term kind) {level : Nat} (higher : context.universeLevel ≤ level) :
    Kinding program { context with universeLevel := level } term kind :=
  kinded.universe level (fun _ _ _ occurs => Nat.le_trans (kinded.rigid_level occurs) higher)
    (fun _ _ _ occurs => Nat.le_trans (kinded.variable_level occurs) higher)

/-- The authoritative predicate term projection retains the actual lexical
binder context of each term, including defaults under their ordered prefix.
No predicate term silently inherits a larger universe. -/
theorem ConstraintKinded.terms_kinded {program : Program} {context : Context} {constraint : Constraint}
    (kinded : ConstraintKinded program context constraint) :
    ∀ term ∈ constraint.terms, ∃ binders,
      Kinding program { context with binders := binders } term term.kind := by
  induction kinded <;> intro term member <;> simp only [Constraint.terms] at member
  case equal left right =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_,by simpa only [left.term_kind] using left⟩
    · have same := List.mem_singleton.mp member
      subst term
      exact ⟨_,by simpa only [right.term_kind] using right⟩
  case outlives left right =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_,by simpa only [left.term_kind] using left⟩
    · have same := List.mem_singleton.mp member
      subst term
      exact ⟨_,by simpa only [right.term_kind] using right⟩
  case typeOutlives left right =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_,by simpa only [left.term_kind] using left⟩
    · have same := List.mem_singleton.mp member
      subst term
      exact ⟨_,by simpa only [right.term_kind] using right⟩
  case rowIncludes left right =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_,by simpa only [left.term_kind] using left⟩
    · have same := List.mem_singleton.mp member
      subst term
      exact ⟨_,by simpa only [right.term_kind] using right⟩
  case implements arguments => exact ⟨_,arguments term member⟩
  case use type _ =>
    have same := List.mem_singleton.mp member
    subst term
    exact ⟨_,by simpa only [type.term_kind] using type⟩
  case callable receiver arguments result effects =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_,by simpa only [receiver.term_kind] using receiver⟩
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_,by simpa only [result.term_kind] using result⟩
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_,by simpa only [effects.term_kind] using effects⟩
    exact ⟨_,by simpa only [(arguments term member).term_kind] using arguments term member⟩
  case runsIn receiver access arguments after =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_,by simpa only [receiver.term_kind] using receiver⟩
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_,by simpa only [access.term_kind] using access⟩
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_,by simpa only [after.term_kind] using after⟩
    exact ⟨_,by simpa only [(arguments term member).term_kind] using arguments term member⟩
  case quantified binders requirements _ defaults _ ih =>
    rcases List.mem_append.mp member with defaultValue | body
    · obtain ⟨binder,present,found⟩ := List.mem_flatMap.mp defaultValue
      obtain ⟨index,atBinder⟩ := List.mem_iff_getElem?.mp present
      have checked := defaults index binder term atBinder (by simpa using found)
      exact ⟨_,by simpa only [checked.term_kind,Context.bindParameters] using checked⟩
    · obtain ⟨requirement,present,nested⟩ := List.mem_flatMap.mp body
      obtain ⟨bound,checked⟩ := ih requirement present term nested
      exact ⟨bound,by simpa only [Context.bindParameters] using checked⟩

theorem ConstraintKinded.levels {program : Program} {context : Context} {constraint : Constraint}
    (kinded : ConstraintKinded program context constraint) :
    ∀ term ∈ constraint.terms, NoLeak context.universeLevel term ∧
      ∀ id variableKind atomLevel, Occurs (.variable id variableKind atomLevel) term → atomLevel ≤ context.universeLevel := by
  intro term member
  obtain ⟨_,checked⟩ := kinded.terms_kinded term member
  exact ⟨checked.noLeak,fun _ _ _ occurs => checked.variable_level occurs⟩

private theorem Kinding.universe_from_terms {program : Program} {context : Context} {term : Term} {kind : Kind}
    (kinded : Kinding program context term kind) (level : Nat) {terms : List Term}
    (bounded : ∀ value ∈ terms, NoLeak level value ∧
      ∀ id variableKind atomLevel, Occurs (.variable id variableKind atomLevel) value → atomLevel ≤ level)
    (member : term ∈ terms) : Kinding program { context with universeLevel := level } term kind :=
  kinded.universe level (bounded term member).1 (bounded term member).2

/-- Nested binder bodies and each preceding-default context keep the same
universe. Lowering therefore checks precisely the published predicate term
projection, including every nested default rather than only atomic goals. -/
theorem ConstraintKinded.universe {program : Program} {context : Context} {constraint : Constraint}
    (kinded : ConstraintKinded program context constraint) (level : Nat)
    (bounded : ∀ term ∈ constraint.terms, NoLeak level term ∧
      ∀ id variableKind atomLevel, Occurs (.variable id variableKind atomLevel) term → atomLevel ≤ level) :
    ConstraintKinded program { context with universeLevel := level } constraint := by
  revert bounded
  induction kinded <;> intro bounded <;> simp only [Constraint.terms] at bounded
  case equal left right =>
    exact .equal (left.universe_from_terms level bounded (by simp))
      (right.universe_from_terms level bounded (by simp))
  case outlives left right =>
    exact .outlives (left.universe_from_terms level bounded (by simp))
      (right.universe_from_terms level bounded (by simp))
  case typeOutlives left right =>
    exact .typeOutlives (left.universe_from_terms level bounded (by simp))
      (right.universe_from_terms level bounded (by simp))
  case rowIncludes left right =>
    exact .rowIncludes (left.universe_from_terms level bounded (by simp))
      (right.universe_from_terms level bounded (by simp))
  case implements found instantiated arguments =>
    exact .implements found instantiated (fun term member =>
      (arguments term member).universe_from_terms level bounded member)
  case use type quantity =>
    exact .use (type.universe_from_terms level bounded (by simp)) quantity
  case callable receiver arguments result effects =>
    exact .callable (receiver.universe_from_terms level bounded (by simp))
      (fun term member => (arguments term member).universe_from_terms level bounded (by simp [member]))
      (result.universe_from_terms level bounded (by simp))
      (effects.universe_from_terms level bounded (by simp))
  case runsIn receiver access arguments after =>
    exact .runsIn (receiver.universe_from_terms level bounded (by simp))
      (access.universe_from_terms level bounded (by simp))
      (fun term member => (arguments term member).universe_from_terms level bounded (by simp [member]))
      (after.universe_from_terms level bounded (by simp))
  case quantified binders requirements unique defaults _ ih =>
    refine .quantified unique ?_ ?_
    · intro index binder value member found
      apply (defaults index binder value member found).universe_from_terms level bounded
      apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨binder,List.mem_of_getElem? member,by simp [found]⟩
    · intro requirement member
      apply ih requirement member
      intro term present
      exact bounded term (List.mem_append_right _ (List.mem_flatMap.mpr ⟨requirement,member,present⟩))

theorem ConstraintKinded.universe_iff {program : Program} {context : Context} {constraint : Constraint}
    (kinded : ConstraintKinded program context constraint) (level : Nat) :
    ConstraintKinded program { context with universeLevel := level } constraint ↔
      ∀ term ∈ constraint.terms, NoLeak level term ∧
        ∀ id variableKind atomLevel, Occurs (.variable id variableKind atomLevel) term → atomLevel ≤ level :=
  ⟨fun checked => checked.levels,kinded.universe level⟩

theorem ConstraintKinded.raiseUniverse {program : Program} {context : Context} {constraint : Constraint}
    (kinded : ConstraintKinded program context constraint) {level : Nat} (higher : context.universeLevel ≤ level) :
    ConstraintKinded program { context with universeLevel := level } constraint := by
  apply kinded.universe level
  intro term member
  have bounded := kinded.levels term member
  exact ⟨fun id kind atomLevel occurs => Nat.le_trans (bounded.1 id kind atomLevel occurs) higher,
    fun id kind atomLevel occurs => Nat.le_trans (bounded.2 id kind atomLevel occurs) higher⟩

/-- The actual hygienic substitution can target an older universe whenever
the source predicate's retained atoms fit there. Its graph, nested freshening
and ordered defaults are supplied by the existing substitution producer. -/
theorem ConstraintKinded.substitutes_at_universe {program : Program} {source target : Context} {constraint : Constraint}
    (kinded : ConstraintKinded program source constraint) (substitution : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute substitution) binder.kind)
    (bounded : ∀ term ∈ constraint.terms, NoLeak target.universeLevel term ∧
      ∀ id variableKind atomLevel, Occurs (.variable id variableKind atomLevel) term → atomLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands) :
    SubstituteConstraint substitution constraint (constraint.substitute substitution) ∧
      ConstraintKinded program target (constraint.substitute substitution) :=
  (kinded.universe target.universeLevel bounded).substitutes substitution parameters (Nat.le_refl _) regions brands

/-- Universal elimination may be supplied values inspected in another
universe. Admission to the actual caller is derived exactly from those
values' atom levels, then the real Static rule and hygienic graph are used.
This theorem does not assume transport of the quantified logical proof. -/
theorem Entails.quantified_instance_lower {program : Program} {context : Context}
    {binders : List Binder} {requirements : List Constraint} {arguments : List Term}
    {substitution : Substitution} {requirement : Constraint} {inspectionLevel : Nat}
    (held : Entails program context (.quantified binders requirements))
    (kinded : ConstraintKinded program context (.quantified binders requirements))
    (instantiated : Instantiates binders arguments substitution)
    (argumentsKinded : ∀ argument ∈ arguments,
      Kinding program { context with universeLevel := inspectionLevel } argument argument.kind)
    (bounded : ∀ argument ∈ arguments, NoLeak context.universeLevel argument ∧
      ∀ id variableKind atomLevel, Occurs (.variable id variableKind atomLevel) argument → atomLevel ≤ context.universeLevel)
    (member : requirement ∈ requirements) :
    SubstituteConstraint substitution requirement (requirement.substitute substitution) ∧
      ConstraintKinded program context (requirement.substitute substitution) ∧
      Entails program context (requirement.substitute substitution) := by
  have caller : ∀ argument ∈ arguments, Kinding program context argument argument.kind := by
    intro argument present
    exact (argumentsKinded argument present).universe context.universeLevel
      (bounded argument present).1 (bounded argument present).2
  have admitted := kinded.quantified_instance instantiated caller member
  exact ⟨admitted.1,admitted.2,Entails.quantifiedInstance held instantiated caller member admitted.1⟩

end Glorious.Language
