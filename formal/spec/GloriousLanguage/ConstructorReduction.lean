import GloriousLanguage.ReductionResiduals

/-! Structural heads do not expand, even when their children contain active
aliases or associated projections. Positive reduction therefore has an actual
head/children decomposition. This does not assume conversion is confluent. -/
namespace Glorious.Language

theorem ListRel.swap {α β : Type} {relation : α → β → Prop} {left : List α} {right : List β}
    (related : ListRel relation left right) : ListRel (fun second first => relation first second) right left := by
  induction related with
  | nil => exact .nil
  | cons head _ tail => exact .cons head tail

theorem ListRel.reflexive {α : Type} {relation : α → α → Prop} (reflexive : ∀ value, relation value value)
    (values : List α) : ListRel relation values values := by
  induction values with
  | nil => exact .nil
  | cons value values ih => exact .cons (reflexive value) ih

theorem RowEquivalent.structuralHead_iff {left right : Term} (equivalent : RowEquivalent left right) :
    left.StructuralHead ↔ right.StructuralHead := by
  refine RowEquivalent.rec
    (motive_1 := fun left right _ => left.StructuralHead ↔ right.StructuralHead)
    (motive_2 := fun _ _ _ => True) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ equivalent
  · intros; rfl
  · intro _ _ _ ih; exact ih.symm
  · intro _ _ _ _ _ first second; exact first.trans second
  · intro _ _ same _ _; exact same.structuralHead_iff
  all_goals intros; first | rfl | exact True.intro

/-- All row equations beneath a structural head preserve its actual ordered
child positions. Only a row constructor itself can flatten or lose duplicates. -/
theorem RowEquivalent.structural_decomposition {left right : Term} (equivalent : RowEquivalent left right)
    (structural : left.StructuralHead) :
    SameHead left right ∧ ListRel RowEquivalent left.children right.children := by
  apply RowEquivalent.rec
    (motive_1 := fun left right _ => left.StructuralHead →
      SameHead left right ∧ ListRel RowEquivalent left.children right.children)
    (motive_2 := fun _ _ _ => True)
    <;> try assumption
  · intro term _
    exact ⟨rfl,.reflexive (fun _ => .refl) term.children⟩
  · intro _ _ equivalent ih structural
    obtain ⟨same,children⟩ := ih (equivalent.structuralHead_iff.mpr structural)
    exact ⟨same.symm,children.swap.imp (fun _ _ related => related.symm)⟩
  · intro _ _ _ first _ firstIH secondIH structural
    obtain ⟨firstHead,firstChildren⟩ := firstIH structural
    obtain ⟨secondHead,secondChildren⟩ := secondIH (first.structuralHead_iff.mp structural)
    exact ⟨firstHead.trans secondHead,
      firstChildren.transitive (fun _ _ _ left right => left.trans right) secondChildren⟩
  · intro _ _ same children _ _
    exact ⟨same,children⟩
  · intros; contradiction
  · intros; contradiction
  · intros; contradiction
  · intros; contradiction
  · exact True.intro
  · intros; exact True.intro

theorem DefinitionalStep.not_structural {program : Program} {context : Context} {left right : Term}
    (step : DefinitionalStep program context left right) : ¬ left.StructuralHead := by
  cases step <;> exact id

/-- This is a decomposition of the full positive relation, not only a single
child step. No admission or confluence hypothesis is needed at the preserved
outer constructor. -/
theorem DefinitionalReduction.structural_decomposition {program : Program} {context : Context} {left right : Term}
    (reduced : DefinitionalReduction program context left right) (structural : left.StructuralHead) :
    SameHead left right ∧ ListRel (DefinitionalReduction program context) left.children right.children := by
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
    (motive_12 := fun context left right _ => left.StructuralHead →
      SameHead left right ∧ ListRel (DefinitionalReduction program context) left.children right.children)
    (motive_13 := fun _ _ _ _ _ => True)
    (motive_14 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_15 := fun _ _ _ _ _ _ _ => True)
    (motive_16 := fun _ _ _ _ _ _ => True)
    <;> try assumption
  all_goals intros
  all_goals try exact True.intro
  case refl _ term _ => exact ⟨rfl,.reflexive (fun _ => .refl) term.children⟩
  case step _ _ _ step _ structural => exact False.elim (step.not_structural structural)
  case trans _ _ _ _ _ _ first second structural =>
    obtain ⟨firstHead,firstChildren⟩ := first structural
    obtain ⟨secondHead,secondChildren⟩ := second (firstHead.structuralHead_iff.mp structural)
    exact ⟨firstHead.trans secondHead,
      firstChildren.transitive (fun _ _ _ left right => left.trans right) secondChildren⟩
  case congrChildren _ _ _ same children _ _ => exact ⟨same,ListRel.of_at same.children_length children⟩
  case row _ _ _ same structural =>
    obtain ⟨head,children⟩ := same.structural_decomposition structural
    exact ⟨head,children.imp (fun _ _ related => .row related)⟩

private theorem ListRel.common_reduction {program : Program} {context : Context} {left right common : List Term}
    (first : ListRel (DefinitionalReduction program context) left common)
    (second : ListRel (DefinitionalReduction program context) right common) :
    ListRel (DefinitionallyJoinable program context) left right := by
  induction first generalizing right with
  | nil => cases second; exact .nil
  | cons head _ tail =>
    cases second with
    | cons other remaining => exact .cons ⟨_,head,other⟩ (tail remaining)

/-- Independently joined structural terms agree in their constructor and have
independently joined corresponding children. The children need not themselves
be normal: opaque and reducible generic arguments are both retained. -/
theorem DefinitionallyJoinable.structural_decomposition {program : Program} {context : Context} {left right : Term}
    (joined : DefinitionallyJoinable program context left right)
    (leftStructural : left.StructuralHead) (rightStructural : right.StructuralHead) :
    SameHead left right ∧ ListRel (DefinitionallyJoinable program context) left.children right.children := by
  obtain ⟨common,first,second⟩ := joined
  obtain ⟨firstHead,firstChildren⟩ := first.structural_decomposition leftStructural
  obtain ⟨secondHead,secondChildren⟩ := second.structural_decomposition rightStructural
  exact ⟨firstHead.trans secondHead.symm,firstChildren.common_reduction secondChildren⟩

theorem DefinitionallyJoinable.nominal_injective {program : Program} {context : Context} {first second : DeclId}
    {left right : List Term}
    (joined : DefinitionallyJoinable program context (.nominal first left) (.nominal second right)) :
    first = second ∧ ListRel (DefinitionallyJoinable program context) left right := by
  obtain ⟨head,children⟩ := joined.structural_decomposition True.intro True.intro
  simp only [SameHead,Term.mapChildren,Term.nominal.injEq] at head
  exact ⟨head.1,children⟩

end Glorious.Language
