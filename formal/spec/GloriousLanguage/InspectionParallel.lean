import GloriousLanguage.InspectionPathResiduals
import GloriousLanguage.PredicateInterpretation

/-! Finite parallel development of actual fixed-path roots. This proof-only
relation retains all row equations and does not normalize recursive bodies.
Ordinary admitted roots are not presumed to satisfy its readiness restriction. -/
namespace Glorious.Language

private theorem ListRel.compose_relations {α β γ : Type} {first : α → β → Prop} {second : β → γ → Prop}
    {result : α → γ → Prop} {left : List α} {middle : List β} {right : List γ}
    (before : ListRel first left middle) (after : ListRel second middle right)
    (compose : ∀ a b c, first a b → second b c → result a c) : ListRel result left right := by
  induction before generalizing right with
  | nil => cases after; exact .nil
  | cons head _ ih =>
    cases after with
    | cons next rest => exact .cons (compose _ _ _ head next) (ih rest)

inductive InspectionParallel (program : Program) (valid : ProgramWellFormed program) (context : Context) :
    Term → Term → Prop where
  | congrChildren {left right} : SameHead left right →
      (∀ (index : Nat) first second, left.children[index]? = some first → right.children[index]? = some second →
        InspectionParallel program valid context first second) → InspectionParallel program valid context left right
  | root {left changed right} : SameHead left changed →
      (∀ (index : Nat) first second, left.children[index]? = some first → changed.children[index]? = some second →
        InspectionParallel program valid context first second) →
      (stepped : DefinitionalStep program context changed right) → PathInspectedStep program valid stepped →
      InspectionParallel program valid context left right
  | row {left before after right} : RowEquivalent left before → InspectionParallel program valid context before after →
      RowEquivalent after right → InspectionParallel program valid context left right

theorem InspectionParallel.congr {program : Program} {valid : ProgramWellFormed program} {context : Context}
    {left right : Term} (same : SameHead left right)
    (children : ListRel (InspectionParallel program valid context) left.children right.children) :
    InspectionParallel program valid context left right := .congrChildren same (fun _ _ _ a b => children.at a b)

theorem InspectionParallel.refl {program : Program} {valid : ProgramWellFormed program} {context : Context} (term : Term) :
    InspectionParallel program valid context term term := by
  apply InspectionParallel.congrChildren rfl
  intro index first second firstAt secondAt
  obtain rfl := Option.some.inj (firstAt.symm.trans secondAt)
  exact InspectionParallel.refl first
termination_by sizeOf term
decreasing_by exact Term.child_sizeOf (List.mem_of_getElem? firstAt)

theorem InspectionParallel.positive {program : Program} {valid : ProgramWellFormed program} {context : Context}
    {left right : Term} (parallel : InspectionParallel program valid context left right) :
    DefinitionalReduction program context left right := by
  induction parallel with
  | congrChildren same _ children => exact .congrChildren same children
  | root same _ stepped _ children => exact (DefinitionalReduction.congrChildren same children).trans (.step stepped)
  | row before _ after ih => exact (DefinitionalReduction.row before).trans (ih.trans (.row after))

/-- A structural prefix keeps the same actual parallel reductions at each
ordered child, even across row equations on either side of a development. -/
theorem InspectionParallel.structural_decomposition {program : Program} {valid : ProgramWellFormed program}
    {context : Context} {left right : Term} (parallel : InspectionParallel program valid context left right)
    (structural : left.StructuralHead) :
    SameHead left right ∧ ListRel (InspectionParallel program valid context) left.children right.children := by
  induction parallel with
  | congrChildren same children => exact ⟨same,ListRel.of_at same.children_length children⟩
  | root same _ stepped _ => exact False.elim (stepped.not_structural (same.structuralHead_iff.mp structural))
  | @row left before after right first inner last ih =>
    obtain ⟨firstHead,firstChildren⟩ := first.structural_decomposition structural
    obtain ⟨middleHead,middleChildren⟩ := ih (first.structuralHead_iff.mp structural)
    obtain ⟨lastHead,lastChildren⟩ := last.structural_decomposition
      (middleHead.structuralHead_iff.mp (first.structuralHead_iff.mp structural))
    refine ⟨firstHead.trans (middleHead.trans lastHead),?_⟩
    have prefixed : ListRel (InspectionParallel program valid context) left.children after.children :=
      firstChildren.compose_relations middleChildren (fun _ _ _ a b => InspectionParallel.row a b .refl)
    exact prefixed.compose_relations lastChildren (fun _ _ _ a b => InspectionParallel.row .refl a b)

private def InspectionRoot (program : Program) (valid : ProgramWellFormed program) (context : Context)
    (left right : Term) : Prop := ∃ stepped : DefinitionalStep program context left right, PathInspectedStep program valid stepped

private noncomputable def inspectionContract (program : Program) (valid : ProgramWellFormed program) (context : Context)
    (term : Term) : Term := by
  classical
  exact if available : ∃ value, InspectionRoot program valid context term value then Classical.choose available else term

private theorem inspectionContract.of_root {program : Program} {valid : ProgramWellFormed program} {context : Context}
    {term value : Term} (root : InspectionRoot program valid context term value) :
    inspectionContract program valid context term = value := by
  classical
  unfold inspectionContract
  split
  next available =>
    obtain ⟨_,chosen⟩ := Classical.choose_spec available
    exact chosen.root_equal root.choose_spec
  next absent => exact False.elim (absent ⟨value,root⟩)

private theorem inspectionContract.no_root {program : Program} {valid : ProgramWellFormed program} {context : Context}
    {term : Term} (absent : ¬ ∃ value, InspectionRoot program valid context term value) :
    inspectionContract program valid context term = term := by
  classical
  simp only [inspectionContract,dif_neg absent]

private theorem inspectionContract.row (program : Program) (valid : ProgramWellFormed program) (context : Context)
    (instances tails : List Term) : inspectionContract program valid context (.row instances tails) = .row instances tails := by
  apply inspectionContract.no_root
  rintro ⟨_,stepped,_⟩
  cases stepped

private theorem inspectionContract.rowEquivalent {program : Program} {valid : ProgramWellFormed program} {context : Context}
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    {left right : Term} (equivalent : RowEquivalent left right) :
    RowEquivalent (inspectionContract program valid context left) (inspectionContract program valid context right) := by
  classical
  by_cases available : ∃ value, InspectionRoot program valid context left value
  · obtain ⟨value,stepped,certificate⟩ := available
    obtain ⟨result,residual,related⟩ := certificate.row_residual contextKinded equivalent
    rw [inspectionContract.of_root ⟨stepped,certificate⟩,inspectionContract.of_root residual]
    exact related
  · have absent : ¬ ∃ value, InspectionRoot program valid context right value := by
      rintro ⟨value,stepped,certificate⟩
      obtain ⟨result,residual,_⟩ := certificate.row_residual contextKinded equivalent.symm
      exact available ⟨result,residual⟩
    rw [inspectionContract.no_root available,inspectionContract.no_root absent]
    exact equivalent

/-- Only proper source children are developed recursively; an expanded
declaration body is returned without recursively developing it again. -/
noncomputable def inspectionDevelopment (program : Program) (valid : ProgramWellFormed program) (context : Context)
    (term : Term) : Term := open Classical in
  inspectionContract program valid context (term.mapChildren (fun child =>
    if _member : child ∈ term.children then inspectionDevelopment program valid context child else child))
termination_by sizeOf term
decreasing_by exact Term.child_sizeOf _member

theorem inspectionDevelopment.node (program : Program) (valid : ProgramWellFormed program) (context : Context) (term : Term) :
    inspectionDevelopment program valid context term =
      inspectionContract program valid context (term.mapChildren (inspectionDevelopment program valid context)) := by
  rw [inspectionDevelopment]
  congr 1
  apply Term.mapChildren_congr
  intro child member
  simp only [dif_pos member]

theorem inspectionDevelopment.row (program : Program) (valid : ProgramWellFormed program) (context : Context)
    (instances tails : List Term) :
    inspectionDevelopment program valid context (.row instances tails) =
      .row (instances.map (inspectionDevelopment program valid context)) (tails.map (inspectionDevelopment program valid context)) := by
  rw [inspectionDevelopment.node]
  exact inspectionContract.row program valid context _ _

/-- Finite development respects all structural row equations, including
equivalent duplicates. Declaration roots use the actual shared row residual. -/
theorem inspectionDevelopment.rowEquivalent {program : Program} {valid : ProgramWellFormed program} {context : Context}
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    {left right : Term} (equivalent : RowEquivalent left right) :
    RowEquivalent (inspectionDevelopment program valid context left) (inspectionDevelopment program valid context right) := by
  let develop := inspectionDevelopment program valid context
  refine RowEquivalent.rec
    (motive_1 := fun left right _ => RowEquivalent (develop left) (develop right))
    (motive_2 := fun left right _ => ListRel RowEquivalent (left.map develop) (right.map develop))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ equivalent
  · intro term; exact .refl
  · intro _ _ _ ih; exact ih.symm
  · intro _ _ _ _ _ first second; exact first.trans second
  · intro left right same _ children
    change RowEquivalent (inspectionDevelopment program valid context left) (inspectionDevelopment program valid context right)
    rw [inspectionDevelopment.node,inspectionDevelopment.node]
    apply inspectionContract.rowEquivalent contextKinded
    apply RowEquivalent.congr
    · exact (PredicateSemantics.Term.sameHead_mapChildren left develop).symm.trans
        (same.trans (PredicateSemantics.Term.sameHead_mapChildren right develop))
    · simpa only [Term.mapChildren_children] using children
  · intro _ _ _ _ instances tails
    simp only [develop,inspectionDevelopment.row]
    exact .permutation (instances.map _) (tails.map _)
  · intros
    simp only [develop,inspectionDevelopment.row,List.map_cons,List.map_append]
    exact .flatten
  · intro _ _ _ _ _ ih
    simp only [develop,inspectionDevelopment.row,List.map_cons]
    exact .duplicate ih
  · intro _ _ _ _ _ ih
    simp only [develop,inspectionDevelopment.row,List.map_cons]
    exact .tailDuplicate ih
  · exact .nil
  · intro _ _ _ _ _ _ head tail; exact .cons head tail

private theorem ListRel.reverse_development {relation : Term → Term → Prop} {develop : Term → Term}
    {left right : List Term} (children : ListRel (fun first second => relation second (develop first)) left right) :
    ListRel relation right (left.map develop) := by
  induction children with
  | nil => exact .nil
  | cons head _ tail => exact .cons head tail

private theorem inspectionContract.parallel {program : Program} {valid : ProgramWellFormed program} {context : Context}
    {left changed : Term} (same : SameHead left changed)
    (children : ListRel (InspectionParallel program valid context) left.children changed.children) :
    InspectionParallel program valid context left (inspectionContract program valid context changed) := by
  classical
  by_cases available : ∃ value, InspectionRoot program valid context changed value
  · obtain ⟨value,stepped,certificate⟩ := available
    rw [inspectionContract.of_root ⟨stepped,certificate⟩]
    exact .root same (fun _ _ _ first second => children.at first second) stepped certificate
  · rw [inspectionContract.no_root available]
    exact .congr same children

/-- Every finite parallel development reaches the same complete-development
target in one more parallel step. This is independent of normalization and
retains all row equations; new declaration bodies are never recursively
normalized by the complete-development function. -/
theorem InspectionParallel.triangle {program : Program} {valid : ProgramWellFormed program} {context : Context}
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    {left right : Term} (parallel : InspectionParallel program valid context left right) :
    InspectionParallel program valid context right (inspectionDevelopment program valid context left) := by
  induction parallel with
  | @congrChildren left right same _ ih =>
    rw [inspectionDevelopment.node]
    apply inspectionContract.parallel (same.symm.trans
      (PredicateSemantics.Term.sameHead_mapChildren left (inspectionDevelopment program valid context)))
    rw [Term.mapChildren_children]
    exact (ListRel.of_at same.children_length ih).reverse_development
  | @root left changed right same _ stepped certificate ih =>
    have nextHead := same.symm.trans
      (PredicateSemantics.Term.sameHead_mapChildren left (inspectionDevelopment program valid context))
    have nextChildren : ListRel (InspectionParallel program valid context) changed.children
        (left.mapChildren (inspectionDevelopment program valid context)).children := by
      rw [Term.mapChildren_children]
      exact (ListRel.of_at same.children_length ih).reverse_development
    obtain ⟨result,residual,related⟩ := certificate.children_relation contextKinded
      (fun term => InspectionParallel.refl term) (fun _ _ reduced => reduced.positive.equal)
      (fun _ _ reduced structural => reduced.structural_decomposition structural)
      (fun term _ _ agree => term.substitutions_related InspectionParallel.congr agree) nextHead nextChildren
    rw [inspectionDevelopment.node,inspectionContract.of_root residual]
    exact related
  | row before _ after ih =>
    exact .row after.symm ih (inspectionDevelopment.rowEquivalent contextKinded before.symm)

theorem InspectionParallel.development {program : Program} {valid : ProgramWellFormed program} {context : Context}
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement) (term : Term) :
    InspectionParallel program valid context term (inspectionDevelopment program valid context term) :=
  (InspectionParallel.refl term).triangle contextKinded

/-- The canonical parallel relation has the diamond property, with one
specific actual common reduct for every peak. Ordinary head-matching
completeness is established separately in `DefinitionalChurchRosser`. -/
theorem InspectionParallel.diamond {program : Program} {valid : ProgramWellFormed program} {context : Context}
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    {source left right : Term} (first : InspectionParallel program valid context source left)
    (second : InspectionParallel program valid context source right) :
    ∃ common, InspectionParallel program valid context left common ∧ InspectionParallel program valid context right common :=
  ⟨inspectionDevelopment program valid context source,first.triangle contextKinded,second.triangle contextKinded⟩

end Glorious.Language
