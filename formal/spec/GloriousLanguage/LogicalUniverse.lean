import GloriousLanguage.UniverseEmbedding
import GloriousLanguage.DeclarationKinding
import GloriousLanguage.LogicalCut

/-! Universal evidence is parametric in the admitted universe. Finite
source support is fixed by a genuine atom bijection; the actual Static
transport and assumption-cut theorems carry the evidence. -/
namespace Glorious.Language

/-- Context binder defaults are not part of the parameter kinding domain.
Their names and kinds are retained by an atom action, even when an unused
default contains atoms outside the current universe. -/
theorem AtomEmbedding.context_domain (embedding : AtomEmbedding) (program : Program) (context : Context) :
    ∀ term kind, Kinding program (embedding.context context) term kind ↔
      Kinding program { context with universeLevel := embedding.levelMap context.universeLevel } term kind := by
  intro term kind
  constructor
  · intro kinded
    apply kinded.context_transport
    · intro id parameterKind occurs
      obtain ⟨binder,member,sameId,sameKind⟩ := kinded.parameter_occurs occurs
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      change original.id = id at sameId
      change original.kind = parameterKind at sameKind
      simpa only [sameId,sameKind] using Kinding.parameter (program := program)
        (context := { context with universeLevel := embedding.levelMap context.universeLevel }) present
    · exact Nat.le_refl _
    · intro _ member
      exact member
    · intro _ member
      exact member
  · intro kinded
    apply kinded.context_transport
    · intro id parameterKind occurs
      obtain ⟨binder,member,sameId,sameKind⟩ := kinded.parameter_occurs occurs
      have present : embedding.binder binder ∈ (embedding.context context).binders := List.mem_map.mpr ⟨binder,member,rfl⟩
      simpa only [AtomRenaming.binder,sameId,sameKind] using Kinding.parameter (program := program) present
    · exact Nat.le_refl _
    · intro _ member
      exact member
    · intro _ member
      exact member

theorem Entails.raiseUniverse_one {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {constraint : Constraint}
    (held : Entails program context constraint)
    (assumptions : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    (admitted : ConstraintKinded program context constraint) :
    Entails program { context with universeLevel := context.universeLevel + 1 } constraint := by
  let terms := program.declarations.flatMap Definition.terms ++
    context.assumptions.flatMap Constraint.terms ++ constraint.terms
  have bounded : ∀ term ∈ terms, NoLeak context.universeLevel term ∧
      ∀ id kind level, Occurs (.variable id kind level) term → level ≤ context.universeLevel := by
    intro term member
    rcases List.mem_append.mp member with before | goal
    · rcases List.mem_append.mp before with source | assumption
      · obtain ⟨declaration,present,nested⟩ := List.mem_flatMap.mp source
        have levels := valid.term_levels present term nested
        exact ⟨fun id kind level occurs => Nat.le_trans (levels.1 id kind level occurs) (Nat.zero_le _),
          fun id kind level occurs => Nat.le_trans (levels.2 id kind level occurs) (Nat.zero_le _)⟩
      · obtain ⟨requirement,present,nested⟩ := List.mem_flatMap.mp assumption
        exact (assumptions requirement present).levels term nested
    · exact admitted.levels term goal
  let embedding := UniverseEmbedding.embedding context.universeLevel (sizeOf terms)
  have fixed : ∀ term ∈ terms, embedding.term term = term := UniverseEmbedding.fixed_terms _ terms bounded
  have programFixed : embedding.Fixes program := by
    intro declaration member term present
    exact fixed term (List.mem_append_left _ (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨declaration,member,present⟩)))
  have constraintFixed : embedding.constraint constraint = constraint := by
    apply embedding.fixed_constraint
    intro term member
    exact fixed term (List.mem_append_right _ member)
  have assumptionsFixed : context.assumptions.map embedding.constraint = context.assumptions := by
    apply List.map_eq_self_of
    intro requirement present
    apply embedding.fixed_constraint
    intro term member
    exact fixed term (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨requirement,present,member⟩)))
  have raisedLevel : embedding.levelMap context.universeLevel = context.universeLevel + 1 := by
    simp only [embedding,UniverseEmbedding.embedding,UniverseEmbedding.level,Nat.lt_irrefl,if_false]
  have transported := held.renameAtoms embedding programFixed
  rw [constraintFixed] at transported
  apply transported.cut
  · intro term kind
    simpa only [raisedLevel] using embedding.context_domain program context term kind
  · intro requirement member
    change requirement ∈ context.assumptions.map embedding.constraint at member
    rw [assumptionsFixed] at member
    exact .assumed member

/-- A larger admitted universe does not invalidate a well-kinded predicate's
evidence. In particular, actual universal introduction remains valid for
all newly admitted rigid and inference atoms; no closed-value enumeration
or assumed quantifier weakening is used. -/
theorem Entails.raiseUniverse {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {constraint : Constraint}
    (held : Entails program context constraint)
    (assumptions : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    (admitted : ConstraintKinded program context constraint)
    {level : Nat} (higher : context.universeLevel ≤ level) :
    Entails program { context with universeLevel := level } constraint := by
  induction higher with
  | refl => exact held
  | @step level higher ih =>
    exact ih.raiseUniverse_one valid
      (fun requirement member => (assumptions requirement member).raiseUniverse higher)
      (admitted.raiseUniverse higher)

end Glorious.Language
