import GloriousLanguage.ReductionResiduals

/-! Endpoint rigidity of the actual positive reduction relation. Normality
means absence of a declared expansion at every actual subterm, not failure of
a search procedure. Row equations remain permitted and are handled explicitly. -/
namespace Glorious.Language

def ExpansionNormal (program : Program) (context : Context) (term : Term) : Prop :=
  ∀ redex, Occurs redex term → ∀ result, ¬ DefinitionalStep program context redex result

theorem ExpansionNormal.root {program : Program} {context : Context} {term result : Term}
    (normal : ExpansionNormal program context term) : ¬ DefinitionalStep program context term result :=
  normal term .here result

theorem ExpansionNormal.child {program : Program} {context : Context} {term child : Term}
    (normal : ExpansionNormal program context term) (present : child ∈ term.children) :
    ExpansionNormal program context child :=
  fun redex occurs result => normal redex (.child present occurs) result

theorem ExpansionNormal.of_root_children {program : Program} {context : Context} {term : Term}
    (root : ∀ result, ¬ DefinitionalStep program context term result)
    (children : ∀ child ∈ term.children, ExpansionNormal program context child) :
    ExpansionNormal program context term := by
  intro redex occurs result
  cases occurs with
  | here => exact root result
  | child present occurs => exact children _ present redex occurs result

theorem ExpansionNormal.row_iff {program : Program} {context : Context} {instances tails : List Term} :
    ExpansionNormal program context (.row instances tails) ↔
      (∀ term ∈ instances, ExpansionNormal program context term) ∧
      (∀ term ∈ tails, ExpansionNormal program context term) := by
  constructor
  · intro normal
    exact ⟨fun _ present => normal.child (List.mem_append_left _ present),
      fun _ present => normal.child (List.mem_append_right _ present)⟩
  · rintro ⟨instancesNormal,tailsNormal⟩
    apply ExpansionNormal.of_root_children
    · intro result step; cases step
    · simpa only [Term.children,List.forall_mem_append] using And.intro instancesNormal tailsNormal

private theorem ListRel.normal_iff {program : Program} {context : Context} {left right : List Term}
    (related : ListRel (fun first second => ExpansionNormal program context first ↔
      ExpansionNormal program context second) left right) :
    (∀ term ∈ left, ExpansionNormal program context term) ↔
      (∀ term ∈ right, ExpansionNormal program context term) := by
  induction related with
  | nil => rfl
  | cons head _ tail => simpa only [List.forall_mem_cons] using and_congr head tail

/-- Row equations preserve actual expansion-normality, even when they
duplicate, erase duplicates, or move nested row tails. -/
theorem RowEquivalent.expansionNormal_iff {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Term} (equivalent : RowEquivalent left right) :
    ExpansionNormal program context left ↔ ExpansionNormal program context right := by
  refine RowEquivalent.rec
    (motive_1 := fun left right _ => ExpansionNormal program context left ↔ ExpansionNormal program context right)
    (motive_2 := fun left right _ => ListRel (fun first second =>
      ExpansionNormal program context first ↔ ExpansionNormal program context second) left right)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ equivalent
  · intros; rfl
  · intro _ _ _ ih; exact ih.symm
  · intro _ _ _ _ _ first second; exact first.trans second
  · intro _ _ same children related
    constructor
    · intro normal
      apply ExpansionNormal.of_root_children
      · intro result step
        obtain ⟨value,before,_⟩ := step.row_residual valid (RowEquivalent.congr same children).symm
        exact normal.root before
      · exact related.normal_iff.mp (fun _ present => normal.child present)
    · intro normal
      apply ExpansionNormal.of_root_children
      · intro result step
        obtain ⟨value,before,_⟩ := step.row_residual valid (RowEquivalent.congr same children)
        exact normal.root before
      · exact related.normal_iff.mpr (fun _ present => normal.child present)
  · intro instances tails instances' tails' instanceOrder tailOrder
    simp only [ExpansionNormal.row_iff]
    constructor
    · rintro ⟨instances,tails⟩
      exact ⟨fun term present => instances term (instanceOrder.mem_iff.mpr present),
        fun term present => tails term (tailOrder.mem_iff.mpr present)⟩
    · rintro ⟨instances,tails⟩
      exact ⟨fun term present => instances term (instanceOrder.mem_iff.mp present),
        fun term present => tails term (tailOrder.mem_iff.mp present)⟩
  · intros
    simp only [ExpansionNormal.row_iff,List.forall_mem_cons,List.forall_mem_append,and_assoc]
  · intro left right rest tails _ ih
    simp only [ExpansionNormal.row_iff,List.forall_mem_cons]
    constructor
    · rintro ⟨⟨left,_,rest⟩,tails⟩; exact ⟨⟨left,rest⟩,tails⟩
    · rintro ⟨⟨left,rest⟩,tails⟩; exact ⟨⟨left,ih.mp left,rest⟩,tails⟩
  · intro instances left right tails _ ih
    simp only [ExpansionNormal.row_iff,List.forall_mem_cons]
    constructor
    · rintro ⟨instances,left,_,tails⟩; exact ⟨instances,left,tails⟩
    · rintro ⟨instances,left,tails⟩; exact ⟨instances,left,ih.mp left,tails⟩
  · exact .nil
  · intro _ _ _ _ _ _ head tail; exact .cons head tail

private theorem ListRel.apply_left {α β : Type} {predicate : α → Prop} {relation : α → β → Prop}
    {left : List α} {right : List β}
    (related : ListRel (fun first second => predicate first → relation first second) left right)
    (available : ∀ value ∈ left, predicate value) : ListRel relation left right := by
  induction related with
  | nil => exact .nil
  | cons head _ tail =>
    exact .cons (head (available _ List.mem_cons_self))
      (tail (fun _ present => available _ (List.mem_cons_of_mem _ present)))

/-- A term with no actual expansion redex can only move within its row
equivalence class under the full contextual and transitive positive closure. -/
theorem DefinitionalReduction.normal_rowEquivalent {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Term} (reduced : DefinitionalReduction program context left right)
    (normal : ExpansionNormal program context left) : RowEquivalent left right := by
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
    (motive_12 := fun context left right _ => ExpansionNormal program context left → RowEquivalent left right)
    (motive_13 := fun _ _ _ _ _ => True)
    (motive_14 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_15 := fun _ _ _ _ _ _ _ => True)
    (motive_16 := fun _ _ _ _ _ _ => True)
    <;> try assumption
  all_goals intros
  all_goals try exact True.intro
  case refl => exact .refl
  case step _ _ _ step _ normal => exact False.elim (normal.root step)
  case trans _ _ _ _ _ _ first second normal =>
    have same := first normal
    exact same.trans (second ((same.expansionNormal_iff valid).mp normal))
  case congrChildren _ _ _ same _ children normal =>
    exact .congr same ((ListRel.of_at same.children_length children).apply_left (fun _ present => normal.child present))
  case row _ _ _ same _ => exact same

theorem DefinitionallyJoinable.normal_unique {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Term} (joined : DefinitionallyJoinable program context left right)
    (leftNormal : ExpansionNormal program context left) (rightNormal : ExpansionNormal program context right) :
    RowEquivalent left right := by
  obtain ⟨common,first,second⟩ := joined
  exact (first.normal_rowEquivalent valid leftNormal).trans (second.normal_rowEquivalent valid rightNormal).symm

theorem ExpansionNormal.scalar (program : Program) (context : Context) (scalar : Scalar) :
    ExpansionNormal program context (.scalar scalar) := by
  intro redex occurs result step
  cases occurs with
  | here => cases step
  | child present _ => simp only [Term.children,List.not_mem_nil] at present

theorem DefinitionallyJoinable.scalar_injective {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Scalar}
    (joined : DefinitionallyJoinable program context (.scalar left) (.scalar right)) : left = right :=
  Option.some.inj ((joined.normal_unique valid (.scalar program context left)
    (.scalar program context right)).scalarDiscriminator_eq)

theorem SubstitutionsJoinable.scalar_lookup_unique {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Substitution} (joined : SubstitutionsJoinable program context left right)
    {id : Identity} {first second : Scalar} (leftFound : left.get id = some (.scalar first))
    (rightFound : right.get id = some (.scalar second)) : first = second := by
  have values := joined.substitution_getD_related (fun term => ⟨term,.refl,.refl⟩) id .type
  simp only [leftFound,rightFound,Option.getD] at values
  exact values.scalar_injective valid

end Glorious.Language
