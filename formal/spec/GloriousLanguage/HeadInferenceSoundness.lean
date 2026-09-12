import GloriousLanguage.JoinabilityCongruence

/-! Missing generic origins are rejected by the real matching producer.
The exclusion proofs cover arbitrary programs and queries, including aliases
whose syntactically present arguments are erased by their declared body. -/
namespace Glorious.Language

theorem DefinitionalReduction.preserves_head_invariant {program : Program} {predicate : Term → Prop}
    (heads : ∀ left right, SameHead left right → predicate left → predicate right)
    (steps : ∀ context left right, DefinitionalStep program context left right → predicate left → predicate right)
    (rows : ∀ left right, RowEquivalent left right → predicate left → predicate right)
    {context : Context} {left right : Term} (reduced : DefinitionalReduction program context left right)
    (before : predicate left) : predicate right := by
  apply DefinitionalReduction.rec
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
    (motive_12 := fun _ left right _ => predicate left → predicate right)
    (motive_13 := fun _ _ _ _ _ => True)
    (motive_14 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_15 := fun _ _ _ _ _ _ _ => True)
    (motive_16 := fun _ _ _ _ _ _ => True)
    <;> try assumption
  all_goals intros
  all_goals try exact True.intro
  all_goals try assumption
  case step context left right step _ present => exact steps context left right step present
  case trans _ _ _ _ _ _ first second present => exact second (first present)
  case congrChildren _ left right same _ _ present => exact heads left right same present
  case row _ left right same present => exact rows left right same present

theorem InfersHeadParameter.excludes_head_invariant {program : Program} {predicate : Term → Prop}
    (parameters : ∀ binder : Binder, ¬ predicate (.parameter binder.id binder.kind))
    (leaves : ∀ term, predicate term → term.StructuralHead → term.children = [])
    (reductions : ∀ context left right, DefinitionalReduction program context left right → predicate left → predicate right)
    {sourceContext context : Context} {binder : Binder} {template query value : Term}
    (inferred : InfersHeadParameter program sourceContext context binder template query value) : ¬ predicate template := by
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
    (motive_15 := fun _ _ _ template _ _ _ => ¬ predicate template)
    (motive_16 := fun _ _ _ _ _ _ => True)
    <;> try assumption
  all_goals intros
  all_goals try exact True.intro
  case parameter _ _ binder _ _ => exact parameters binder
  case child _ _ _ template _ _ _ _ _ structural _ sourceAt _ _ _ =>
    intro present
    rw [leaves template present structural] at sourceAt
    simp at sourceAt
  case sourceReduction _ sourceContext _ template reduced _ _ reducedBy _ _ origin =>
    exact fun present => origin (reductions sourceContext template reduced reducedBy present)
  case queryConversion => assumption

/-- The query's syntax cannot turn a source leaf into a generic origin,
even through arbitrary conversion and positive source reductions. -/
theorem InfersHeadParameter.not_structural_leaf {program : Program} {sourceContext context : Context}
    {binder : Binder} {template query value : Term}
    (inferred : InfersHeadParameter program sourceContext context binder template query value)
    (structural : template.StructuralHead) (empty : template.children = [])
    (notParameter : ∀ id kind, template ≠ .parameter id kind) : False := by
  let predicate : Term → Prop := fun term => SameHead template term
  apply inferred.excludes_head_invariant (predicate := predicate) ?_ ?_ ?_ rfl
  · intro other same
    exact notParameter other.id other.kind (Term.parameter_of_sameHead same.symm)
  · intro term same _
    apply List.eq_nil_of_length_eq_zero
    rw [← same.children_length,empty]
    rfl
  · intro _ left right reduced same
    exact same.trans (reduced.structural_decomposition (same.structuralHead_iff.mp structural)).1

/-- This proof predicate consults the actual alias declaration. Alias
arguments may contain the generic syntactically; an erasing body still cannot
expose an injective determining position. -/
def Term.UnitErasingHead (program : Program) : Term → Prop
  | .unit => True
  | .alias id _ => ∃ declaration, program.alias id = some declaration ∧ declaration.value = .unit
  | _ => False

theorem SameHead.unitErasingHead_iff {program : Program} {left right : Term} (same : SameHead left right) :
    left.UnitErasingHead program ↔ right.UnitErasingHead program := by
  have unchanged (term : Term) :
      (term.mapChildren (fun _ => .unit)).UnitErasingHead program = term.UnitErasingHead program := by
    cases term <;> rfl
  have classified := congrArg (Term.UnitErasingHead program) same
  rw [unchanged,unchanged] at classified
  exact Iff.of_eq classified

theorem RowEquivalent.unitErasingHead_iff {program : Program} {left right : Term} (equal : RowEquivalent left right) :
    left.UnitErasingHead program ↔ right.UnitErasingHead program := by
  refine RowEquivalent.rec
    (motive_1 := fun left right _ => left.UnitErasingHead program ↔ right.UnitErasingHead program)
    (motive_2 := fun _ _ _ => True) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ equal
  · intros; rfl
  · intro _ _ _ ih; exact ih.symm
  · intro _ _ _ _ _ first second; exact first.trans second
  · intro _ _ same _ _; exact same.unitErasingHead_iff
  all_goals intros; first | rfl | exact True.intro

theorem DefinitionalStep.unitErasingHead {program : Program} {context : Context} {left right : Term}
    (step : DefinitionalStep program context left right) (erased : left.UnitErasingHead program) :
    right.UnitErasingHead program := by
  cases step with
  | alias found _ _ substituted =>
    obtain ⟨declaration,actualFound,body⟩ := erased
    obtain rfl := Option.some.inj (found.symm.trans actualFound)
    rw [substituted.2.1,body]
    simp [Term.substitute,Term.UnitErasingHead]
  | projection => contradiction
  | defaultProjection => contradiction

theorem InfersHeadParameter.not_unit_erasing {program : Program} {sourceContext context : Context}
    {binder : Binder} {template query value : Term}
    (inferred : InfersHeadParameter program sourceContext context binder template query value) :
    ¬ template.UnitErasingHead program := by
  apply inferred.excludes_head_invariant
  · intro _; exact id
  · intro term erased structural
    cases term <;> simp_all [Term.UnitErasingHead,Term.StructuralHead,Term.children]
  · intro _ _ _ reduced
    exact reduced.preserves_head_invariant (fun _ _ same => same.unitErasingHead_iff.mp)
      (fun _ _ _ step => step.unitErasingHead) (fun _ _ same => same.unitErasingHead_iff.mp)

theorem InfersHeadArgument.not_unit_erasing {program : Program} {context : Context}
    {implementation : ImplDefinition} {arguments : List Term} {binder : Binder} {value : Term}
    (inferred : InfersHeadArgument program context implementation arguments binder value)
    (erased : ∀ template ∈ implementation.arguments, template.UnitErasingHead program) : False := by
  cases inferred with
  | argument sourceAt _ origin => exact origin.not_unit_erasing (erased _ (List.mem_of_getElem? sourceAt))

/-- Actual matching rejects a missing generic origin, not merely publication
of the declaration. No chosen query, inferred substitution or equality proof
can make a unit-erasing head infer a generic argument. -/
theorem MatchesImplHead.unit_erasing_generics_empty {program : Program} {context : Context}
    {implementation : ImplDefinition} {arguments : List Term} {substitution : Substitution}
    (matched : MatchesImplHead program context implementation arguments substitution)
    (erased : ∀ template ∈ implementation.arguments, template.UnitErasingHead program) :
    implementation.generics = [] := by
  cases matched with
  | inferred instantiated _ _ _ _ origins =>
    cases generics : implementation.generics with
    | nil => rfl
    | cons binder rest =>
      have kinds := instantiated.2.1
      rw [generics] at kinds
      cases kinds with
      | cons _ _ =>
        exact False.elim ((origins 0 binder _ (by simp [generics]) rfl).not_unit_erasing erased)

theorem ProgramWellFormed.unit_erasing_implementation_nongeneric {program : Program} (valid : ProgramWellFormed program)
    {implementation : ImplDefinition} (declared : Definition.implementation implementation ∈ program.declarations)
    (erased : ∀ template ∈ implementation.arguments, template.UnitErasingHead program) :
    implementation.generics = [] := by
  have origins := valid.implementation_head_determined declared
  cases generics : implementation.generics with
  | nil => rfl
  | cons binder rest =>
    exact False.elim ((origins binder (by simp [generics])).not_unit_erasing erased)

end Glorious.Language
