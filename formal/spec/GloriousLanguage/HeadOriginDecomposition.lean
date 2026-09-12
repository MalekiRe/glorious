import GloriousLanguage.HeadInferenceSoundness
import GloriousLanguage.HeadInferenceConstruction

/-! A normal form for the existing finite generic-origin evidence. All source
expansions can be moved before the structural path and all query conversions
outside it. The theorem does not normalize terms or assume injectivity of
definitional equality; its source edge remains actual positive reduction. -/
namespace Glorious.Language

private theorem ListRel.set_at {α : Type} {relation : α → α → Prop}
    (reflexive : ∀ value, relation value value) {values : List α} {index : Nat} {before after : α}
    (found : values[index]? = some before) (related : relation before after) :
    ListRel relation values (values.set index after) := by
  induction values generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at found
      subst head
      exact .cons related (.reflexive reflexive tail)
    | succ index => exact .cons (reflexive head) (ih found)

/-- Replacing one ordered child preserves its exact position, even when
several original children happen to be syntactically equal. -/
theorem Term.child_related {relation : Term → Term → Prop}
    (reflexive : ∀ value, relation value value)
    (congruent : ∀ {left right}, SameHead left right → ListRel relation left.children right.children →
      relation left right)
    {parent before after : Term} {index : Nat} (found : parent.children[index]? = some before)
    (related : relation before after) :
    ∃ rebuilt, SameHead parent rebuilt ∧ rebuilt.children[index]? = some after ∧ relation parent rebuilt := by
  obtain ⟨rebuilt,same,children⟩ := parent.children_realizable (parent.children.set index after) (by simp)
  refine ⟨rebuilt,same,?_,congruent same ?_⟩
  · rw [children,List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1]
  · rw [children]
    exact ListRel.set_at reflexive found related

/-- A determining path contains only actual paired, ordered constructor
positions. It is the structural part of an origin proof, not a new matcher. -/
inductive StructuralHeadOrigin (binder : Binder) : Term → Term → Term → Prop where
  | parameter {value} : value.kind = binder.kind →
      StructuralHeadOrigin binder (.parameter binder.id binder.kind) value value
  | child {template query templateChild queryChild value} {index : Nat} :
      template.StructuralHead → SameHead template query →
      template.children[index]? = some templateChild → query.children[index]? = some queryChild →
      StructuralHeadOrigin binder templateChild queryChild value →
      StructuralHeadOrigin binder template query value

theorem StructuralHeadOrigin.infers {program : Program} {sourceContext context : Context}
    {binder : Binder} {template query value : Term} (origin : StructuralHeadOrigin binder template query value) :
    InfersHeadParameter program sourceContext context binder template query value := by
  induction origin with
  | parameter kind => exact .parameter kind
  | child structural same sourceAt queryAt _ ih => exact .child structural same sourceAt queryAt ih

theorem StructuralHeadOrigin.source_occurs {binder : Binder} {template query value : Term}
    (origin : StructuralHeadOrigin binder template query value) :
    Occurs (.parameter binder.id binder.kind) template := by
  induction origin with
  | parameter => exact .here
  | child _ _ sourceAt _ _ ih => exact .child (List.mem_of_getElem? sourceAt) ih

theorem StructuralHeadOrigin.query_occurs {binder : Binder} {template query value : Term}
    (origin : StructuralHeadOrigin binder template query value) : Occurs value query := by
  induction origin with
  | parameter => exact .here
  | child _ _ _ queryAt _ ih => exact .child (List.mem_of_getElem? queryAt) ih

/-- A structural determining path extracts a positive join from a positive
join of the whole instantiated head. This uses the proved constructor
decomposition of actual reductions, not injectivity of convertibility. -/
theorem StructuralHeadOrigin.joinable_value {program : Program} {context : Context}
    {binder : Binder} {template query value : Term} (origin : StructuralHeadOrigin binder template query value)
    (substitution : Substitution)
    (joined : DefinitionallyJoinable program context (template.substitute substitution) query) :
    DefinitionallyJoinable program context ((substitution.get binder.id).getD (.parameter binder.id binder.kind)) value := by
  induction origin with
  | parameter => simpa only [Term.substitute] using joined
  | @child template query templateChild queryChild value index structural same sourceAt queryAt _ ih =>
    have notParameter : ∀ id kind, template ≠ .parameter id kind := by
      intro id kind equal
      subst template
      simp [Term.children] at sourceAt
    have substitutedHead : SameHead template (template.substitute substitution) :=
      (Term.substitute_head notParameter substitution).symm
    have children := (joined.structural_decomposition (substitutedHead.structuralHead_iff.mp structural)
      (same.structuralHead_iff.mp structural)).2
    apply ih
    apply children.at (index := index) (second := queryChild) (rightAt := queryAt)
    rw [Term.substitute_children notParameter]
    simp only [List.getElem?_map,sourceAt,Option.map_some]

/-- Every actual origin decomposes into one positive source expansion and
one whole-query conversion around a purely structural determining path.
Neither the source expansion nor the query conversion is replaced by an
oracle for a normal form, a join, or the desired inferred value. -/
theorem InfersHeadParameter.decompose {program : Program} {sourceContext context : Context}
    {binder : Binder} {template query value : Term}
    (inferred : InfersHeadParameter program sourceContext context binder template query value) :
    ∃ expanded converted, DefinitionalReduction program sourceContext template expanded ∧
      DefinitionallyEqual program context query converted ∧ StructuralHeadOrigin binder expanded converted value := by
  apply InfersHeadParameter.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ => True)
    (motive_8 := fun _ _ _ => True)
    (motive_9 := fun _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ => True)
    (motive_11 := fun _ _ _ _ => True)
    (motive_12 := fun _ _ _ _ => True)
    (motive_13 := fun _ _ _ _ _ => True)
    (motive_14 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_15 := fun sourceContext context binder template query value _ =>
      ∃ expanded converted, DefinitionalReduction program sourceContext template expanded ∧
        DefinitionallyEqual program context query converted ∧ StructuralHeadOrigin binder expanded converted value)
    (motive_16 := fun _ _ _ _ _ _ => True)
    <;> try assumption
  all_goals intros
  all_goals try exact True.intro
  case parameter _ _ _ value kind => exact ⟨_,value,.refl,.refl,.parameter kind⟩
  case child context sourceContext _ template query _ _ _ _ structural same sourceAt queryAt _ ih =>
    obtain ⟨sourceChild,queryChild,sourceReduced,queryEqual,path⟩ := ih
    obtain ⟨expanded,sourceHead,expandedAt,expandedBy⟩ := Term.child_related
      (relation := DefinitionalReduction program sourceContext) (fun _ => .refl)
      (fun head children => .congr head children) sourceAt sourceReduced
    obtain ⟨converted,queryHead,convertedAt,convertedBy⟩ := Term.child_related
      (relation := DefinitionallyEqual program context) (fun _ => .refl)
      (fun head children => .congr head children) queryAt queryEqual
    exact ⟨expanded,converted,expandedBy,convertedBy,
      .child (sourceHead.structuralHead_iff.mp structural) (sourceHead.symm.trans (same.trans queryHead))
        expandedAt convertedAt path⟩
  case sourceReduction _ _ _ _ _ _ _ reduced _ _ ih =>
    obtain ⟨expanded,converted,sourceReduced,queryEqual,path⟩ := ih
    exact ⟨expanded,converted,reduced.trans sourceReduced,queryEqual,path⟩
  case queryConversion _ _ _ _ _ _ _ equal _ _ ih =>
    obtain ⟨expanded,converted,sourceReduced,queryEqual,path⟩ := ih
    exact ⟨expanded,converted,sourceReduced,equal.trans queryEqual,path⟩

theorem InfersHeadParameter.iff_decomposed {program : Program} {sourceContext context : Context}
    {binder : Binder} {template query value : Term} :
    InfersHeadParameter program sourceContext context binder template query value ↔
      ∃ expanded converted, DefinitionalReduction program sourceContext template expanded ∧
        DefinitionallyEqual program context query converted ∧ StructuralHeadOrigin binder expanded converted value :=
  ⟨InfersHeadParameter.decompose,fun ⟨_,_,reduced,equal,path⟩ =>
    .sourceReduction reduced (.queryConversion equal path.infers)⟩

/-- Query conversion cannot manufacture a parameter which no actual positive
expansion of the source template can expose. -/
theorem InfersHeadParameter.source_parameter_reachable {program : Program} {sourceContext context : Context}
    {binder : Binder} {template query value : Term}
    (inferred : InfersHeadParameter program sourceContext context binder template query value) :
    ∃ expanded, DefinitionalReduction program sourceContext template expanded ∧
      Occurs (.parameter binder.id binder.kind) expanded := by
  obtain ⟨expanded,_,reduced,_,path⟩ := inferred.decompose
  exact ⟨expanded,reduced,path.source_occurs⟩

theorem InfersHeadArgument.decompose {program : Program} {context : Context} {implementation : ImplDefinition}
    {arguments : List Term} {binder : Binder} {value : Term}
    (inferred : InfersHeadArgument program context implementation arguments binder value) :
    ∃ (index : Nat) (template query expanded converted : Term),
      implementation.arguments[index]? = some template ∧ arguments[index]? = some query ∧
      DefinitionalReduction program implementation.context template expanded ∧
      DefinitionallyEqual program context query converted ∧ StructuralHeadOrigin binder expanded converted value := by
  cases inferred with
  | argument sourceAt queryAt origin =>
    obtain ⟨expanded,converted,reduced,equal,path⟩ := origin.decompose
    exact ⟨_,_,_,expanded,converted,sourceAt,queryAt,reduced,equal,path⟩

/-- The normalized origin belongs to the actual raw substitution lookup, not
an independently chosen or subsequently normalized generic argument. -/
theorem MatchesImplHead.binding_origin {program : Program} {context : Context}
    {implementation : ImplDefinition} {arguments : List Term} {substitution : Substitution}
    (matched : MatchesImplHead program context implementation arguments substitution)
    {binder : Binder} {value : Term} (member : binder ∈ implementation.generics)
    (found : substitution.get binder.id = some value) :
    InfersHeadArgument program context implementation arguments binder value := by
  cases matched with
  | @inferred _ _ _ values _ _ instantiated _ _ _ _ origins =>
    obtain ⟨index,binderAt⟩ := List.mem_iff_getElem?.mp member
    cases valueAt : values[index]? with
    | none =>
      have bound := (List.getElem?_eq_some_iff.mp binderAt).1
      have beyond := List.getElem?_eq_none_iff.mp valueAt
      have lengths := instantiated.2.1.length_eq
      omega
    | some actual =>
      have actualFound := instantiated.binder_lookup_at binderAt valueAt
      obtain rfl := Option.some.inj (found.symm.trans actualFound)
      exact origins index binder _ binderAt valueAt

/-- Selection exposes the same normalized determining path for every actual
bound parameter. No program-admission or post-selection uniqueness premise is
needed to recover the source of a selected argument. -/
theorem SelectsImpl.binding_origin {program : Program} {context : Context}
    {trait : DeclId} {arguments : List Term} {negative : Bool} {implementation : ImplDefinition}
    {substitution : Substitution}
    (selected : SelectsImpl program context trait arguments negative implementation substitution)
    {binder : Binder} {value : Term} (member : binder ∈ implementation.generics)
    (found : substitution.get binder.id = some value) :
    ∃ (index : Nat) (template query expanded converted : Term),
      implementation.arguments[index]? = some template ∧ arguments[index]? = some query ∧
      DefinitionalReduction program implementation.context template expanded ∧
      DefinitionallyEqual program context query converted ∧ StructuralHeadOrigin binder expanded converted value := by
  cases selected with
  | selected _ _ _ matched _ => exact (matched.binding_origin member found).decompose

end Glorious.Language
