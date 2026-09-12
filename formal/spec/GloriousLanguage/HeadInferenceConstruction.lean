import GloriousLanguage.DefinitionalCoherence

/-! The positive structural-head boundary constructs real inference and
selection evidence under arbitrary lawful substitutions. It does not assume
the desired matcher result or normalize unrelated caller arguments. -/
namespace Glorious.Language

theorem Instantiates.binder_lookup_at {binders : List Binder} {arguments : List Term} {substitution : Substitution}
    (instantiated : Instantiates binders arguments substitution) {index : Nat} {binder : Binder} {value : Term}
    (binderAt : binders[index]? = some binder) (valueAt : arguments[index]? = some value) :
    substitution.get binder.id = some value := by
  rw [instantiated.2.2]
  have unique := instantiated.1
  have aligned := instantiated.2.1
  clear instantiated substitution
  induction aligned generalizing index with
  | nil => simp at binderAt
  | @cons first actual binders arguments kind rest ih =>
    simp only [List.map_cons,List.nodup_cons] at unique
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at binderAt valueAt
      subst_vars
      simp [Table.get]
    | succ index =>
      have different : first.id ≠ binder.id := by
        intro same
        exact unique.1 (same.symm ▸ List.mem_map.mpr ⟨binder,List.mem_of_getElem? binderAt,rfl⟩)
      simpa [Table.get,different] using ih binderAt valueAt unique.2

/-- Existing occurrence evidence is sufficient whenever all visited source
constructors are structural. The inferred value is the actual simultaneous
lookup, and the query is the actual substituted template. -/
theorem InfersHeadParameter.of_structural_occurrence {program : Program} {sourceContext context : Context}
    {binder : Binder} {template : Term} (occurs : Occurs (.parameter binder.id binder.kind) template)
    (structural : ∀ term, Occurs term template → term.StructuralHead) (substitution : Substitution)
    (kind : ((substitution.get binder.id).getD (.parameter binder.id binder.kind)).kind = binder.kind) :
    InfersHeadParameter program sourceContext context binder template (template.substitute substitution)
      ((substitution.get binder.id).getD (.parameter binder.id binder.kind)) := by
  induction occurs with
  | here => simpa only [Term.substitute] using InfersHeadParameter.parameter kind
  | @child parent child present _ ih =>
    obtain ⟨index,childAt⟩ := List.mem_iff_getElem?.mp present
    have notParameter : ∀ id kind, parent ≠ .parameter id kind := by
      intro id kind equal
      subst parent
      simp [Term.children] at present
    apply InfersHeadParameter.child (index := index) (queryChild := child.substitute substitution) (structural parent .here)
    · change parent.mapChildren _ = (parent.substitute substitution).mapChildren _
      exact (Term.substitute_head notParameter substitution).symm
    · exact childAt
    · rw [Term.substitute_children notParameter]
      simp only [List.getElem?_map,childAt,Option.map_some]
    · exact ih (fun term occurs => structural term (.child present occurs))

theorem InfersHeadParameter.self_of_structural_occurrence {program : Program} {sourceContext context : Context}
    {binder : Binder} {template : Term} (occurs : Occurs (.parameter binder.id binder.kind) template)
    (structural : ∀ term, Occurs term template → term.StructuralHead) :
    InfersHeadParameter program sourceContext context binder template template (.parameter binder.id binder.kind) := by
  induction occurs with
  | here => exact .parameter rfl
  | @child parent child present _ ih =>
    obtain ⟨index,childAt⟩ := List.mem_iff_getElem?.mp present
    exact .child (structural parent .here) rfl childAt childAt
      (ih (fun term occurs => structural term (.child present occurs)))

/-- This is source admission constructed from real head positions. It is a
sufficient constructor-headed rule, not a completeness claim for row patterns
or source projections that must first expand. -/
theorem ImplementationHeadDetermined.of_structural_origins {program : Program} {implementation : ImplDefinition}
    (origins : ∀ binder ∈ implementation.generics, ∃ template ∈ implementation.arguments,
      Occurs (.parameter binder.id binder.kind) template ∧
      ∀ term, Occurs term template → term.StructuralHead) : ImplementationHeadDetermined program implementation := by
  intro binder present
  obtain ⟨template,member,occurs,structural⟩ := origins binder present
  obtain ⟨index,templateAt⟩ := List.mem_iff_getElem?.mp member
  exact .argument templateAt templateAt (InfersHeadParameter.self_of_structural_occurrence occurs structural)

theorem MatchesImplHead.of_structural_origins {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {implementation : ImplDefinition} {values arguments : List Term} {substitution : Substitution}
    (declared : Definition.implementation implementation ∈ program.declarations)
    (instantiated : Instantiates implementation.generics values substitution)
    (kinded : ∀ value ∈ values, Kinding program context value value.kind)
    (origins : ∀ binder ∈ implementation.generics, ∃ template ∈ implementation.arguments,
      Occurs (.parameter binder.id binder.kind) template ∧
      ∀ term, Occurs term template → term.StructuralHead)
    (equal : ListRel (DefinitionallyEqual program context)
      (implementation.arguments.map (Term.substitute substitution)) arguments) :
    MatchesImplHead program context implementation arguments substitution := by
  apply MatchesImplHead.congr_query (second := arguments) (equal := equal)
  apply MatchesImplHead.instantiated valid declared instantiated kinded
  intro position binder value binderAt valueAt
  obtain ⟨template,member,occurs,structural⟩ := origins binder (List.mem_of_getElem? binderAt)
  obtain ⟨index,templateAt⟩ := List.mem_iff_getElem?.mp member
  have lookup := instantiated.binder_lookup_at binderAt valueAt
  have kind := (instantiated.2.1.at binderAt valueAt).symm
  have inferred := InfersHeadParameter.of_structural_occurrence (program := program)
    (sourceContext := implementation.context) (context := context) occurs structural substitution (by
      simpa only [lookup,Option.getD_some] using kind)
  rw [lookup] at inferred
  exact .argument templateAt (by simp only [List.getElem?_map,templateAt,Option.map_some]) inferred

/-- End-to-end selection consumes the constructed origin, the actual head
conversion and the actual instantiated requirements. No additional inference
certificate is requested from the caller at this structural boundary. -/
theorem SelectsImpl.of_structural_origins {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {implementation : ImplDefinition} {values arguments : List Term} {substitution : Substitution}
    (declared : Definition.implementation implementation ∈ program.declarations)
    (instantiated : Instantiates implementation.generics values substitution)
    (kinded : ∀ value ∈ values, Kinding program context value value.kind)
    (origins : ∀ binder ∈ implementation.generics, ∃ template ∈ implementation.arguments,
      Occurs (.parameter binder.id binder.kind) template ∧
      ∀ term, Occurs term template → term.StructuralHead)
    (equal : ListRel (DefinitionallyEqual program context)
      (implementation.arguments.map (Term.substitute substitution)) arguments)
    (requirements : ∀ requirement ∈ implementation.requirements, EntailsSubstitution program context substitution requirement) :
    SelectsImpl program context implementation.trait arguments implementation.negative implementation substitution :=
  .selected declared rfl rfl (.of_structural_origins valid declared instantiated kinded origins equal) requirements

end Glorious.Language
