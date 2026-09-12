import GloriousLanguage.InspectionParallel

/-! Transitive canonical developments have actual common reducts. This closes
the canonical Church–Rosser boundary, not the separate simulation of ordinary
admitted head matching into fixed-path inspection. -/
namespace Glorious.Language

inductive PositiveClosure {α : Type} (relation : α → α → Prop) : α → α → Prop where
  | refl {value} : PositiveClosure relation value value
  | cons {left middle right} : relation left middle → PositiveClosure relation middle right → PositiveClosure relation left right

theorem PositiveClosure.single {α : Type} {relation : α → α → Prop} {left right : α}
    (step : relation left right) : PositiveClosure relation left right := .cons step .refl

theorem PositiveClosure.trans {α : Type} {relation : α → α → Prop} {left middle right : α}
    (first : PositiveClosure relation left middle) (second : PositiveClosure relation middle right) :
    PositiveClosure relation left right := by
  induction first with
  | refl => exact second
  | cons head _ tail => exact .cons head (tail second)

theorem PositiveClosure.map {α β : Type} {relation : α → α → Prop} {target : β → β → Prop}
    (f : α → β) (preserves : ∀ left right, relation left right → target (f left) (f right))
    {left right : α} (reduced : PositiveClosure relation left right) : PositiveClosure target (f left) (f right) := by
  induction reduced with
  | refl => exact .refl
  | cons head _ tail => exact .cons (preserves _ _ head) tail

theorem ListRel.positive_closure {α : Type} {relation : α → α → Prop}
    (reflexive : ∀ value, relation value value) {left right : List α}
    (children : ListRel (PositiveClosure relation) left right) : PositiveClosure (ListRel relation) left right := by
  induction children with
  | nil => exact .refl
  | @cons first second left right head _ tail =>
    exact (head.map (fun value => value :: left)
      (fun _ _ related => .cons related (.reflexive reflexive left))).trans
      (tail.map (List.cons second) (fun _ _ related => .cons (reflexive second) related))

abbrev InspectionReduction (program : Program) (valid : ProgramWellFormed program) (context : Context) :=
  PositiveClosure (InspectionParallel program valid context)

def InspectionJoinable (program : Program) (valid : ProgramWellFormed program) (context : Context) (left right : Term) : Prop :=
  ∃ common, InspectionReduction program valid context left common ∧ InspectionReduction program valid context right common

theorem InspectionReduction.positive {program : Program} {valid : ProgramWellFormed program} {context : Context}
    {left right : Term} (reduced : InspectionReduction program valid context left right) :
    DefinitionalReduction program context left right := by
  induction reduced with
  | refl => exact .refl
  | cons head _ tail => exact head.positive.trans tail

theorem InspectionReduction.root {program : Program} {valid : ProgramWellFormed program} {context : Context}
    {left right : Term} {stepped : DefinitionalStep program context left right} (certificate : PathInspectedStep program valid stepped) :
    InspectionReduction program valid context left right := by
  apply PositiveClosure.single
  apply InspectionParallel.root rfl _ stepped certificate
  intro index first second firstAt secondAt
  obtain rfl := Option.some.inj (firstAt.symm.trans secondAt)
  exact .refl first

theorem InspectionReduction.row {program : Program} {valid : ProgramWellFormed program} {context : Context}
    {left right : Term} (equivalent : RowEquivalent left right) : InspectionReduction program valid context left right :=
  .single (.row equivalent (.refl right) .refl)

private theorem InspectionReduction.congr_sequence {program : Program} {valid : ProgramWellFormed program} {context : Context}
    {before after : List Term}
    (children : PositiveClosure (ListRel (InspectionParallel program valid context)) before after) :
    ∀ left right, SameHead left right → left.children = before → right.children = after →
      InspectionReduction program valid context left right := by
  induction children with
  | refl =>
    intro left right same first last
    apply PositiveClosure.single
    apply InspectionParallel.congr same
    rw [first,last]
    exact .reflexive (fun term => .refl term) _
  | @cons before middle after head _ tail =>
    intro left right same first last
    obtain ⟨changed,nextHead,nextChildren⟩ := left.children_realizable middle (by rw [first]; exact head.length_eq.symm)
    apply PositiveClosure.cons
    · exact InspectionParallel.congr nextHead (by rw [first,nextChildren]; exact head)
    · exact tail changed right (nextHead.symm.trans same) nextChildren last

theorem InspectionReduction.congr {program : Program} {valid : ProgramWellFormed program} {context : Context}
    {left right : Term} (same : SameHead left right)
    (children : ListRel (InspectionReduction program valid context) left.children right.children) :
    InspectionReduction program valid context left right :=
  InspectionReduction.congr_sequence (children.positive_closure (fun term => .refl term)) left right same rfl rfl

/-- A single parallel step commutes past an arbitrary finite canonical
development. The far edge remains one parallel step. -/
theorem InspectionReduction.strip {program : Program} {valid : ProgramWellFormed program} {context : Context}
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    {source left right : Term} (first : InspectionParallel program valid context source left)
    (second : InspectionReduction program valid context source right) :
    ∃ common, InspectionReduction program valid context left common ∧ InspectionParallel program valid context right common := by
  induction second generalizing left with
  | refl => exact ⟨left,.refl,first⟩
  | cons head _ tail =>
    obtain ⟨middle,leftMiddle,nextMiddle⟩ := first.diamond contextKinded head
    obtain ⟨common,middleCommon,rightCommon⟩ := tail nextMiddle
    exact ⟨common,.cons leftMiddle middleCommon,rightCommon⟩

/-- Canonical confluence is derived from the proved parallel diamond, without
a normal-form existence assumption or a termination argument. -/
theorem InspectionReduction.confluence {program : Program} {valid : ProgramWellFormed program} {context : Context}
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    {source left right : Term} (first : InspectionReduction program valid context source left)
    (second : InspectionReduction program valid context source right) : InspectionJoinable program valid context left right := by
  induction first generalizing right with
  | refl => exact ⟨right,second,.refl⟩
  | cons head _ tail =>
    obtain ⟨middle,nextMiddle,rightMiddle⟩ := InspectionReduction.strip contextKinded head second
    obtain ⟨common,leftCommon,middleCommon⟩ := tail nextMiddle
    exact ⟨common,leftCommon,.cons rightMiddle middleCommon⟩

theorem InspectionJoinable.refl {program : Program} {valid : ProgramWellFormed program} {context : Context} (term : Term) :
    InspectionJoinable program valid context term term := ⟨term,.refl,.refl⟩

theorem InspectionJoinable.symm {program : Program} {valid : ProgramWellFormed program} {context : Context}
    {left right : Term} (joined : InspectionJoinable program valid context left right) :
    InspectionJoinable program valid context right left := by
  obtain ⟨common,first,second⟩ := joined
  exact ⟨common,second,first⟩

theorem InspectionJoinable.trans {program : Program} {valid : ProgramWellFormed program} {context : Context}
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    {left middle right : Term} (first : InspectionJoinable program valid context left middle)
    (second : InspectionJoinable program valid context middle right) : InspectionJoinable program valid context left right := by
  obtain ⟨a,leftA,middleA⟩ := first
  obtain ⟨b,middleB,rightB⟩ := second
  obtain ⟨common,aCommon,bCommon⟩ := middleA.confluence contextKinded middleB
  exact ⟨common,leftA.trans aCommon,rightB.trans bCommon⟩

theorem InspectionJoinable.positive {program : Program} {valid : ProgramWellFormed program} {context : Context}
    {left right : Term} (joined : InspectionJoinable program valid context left right) : DefinitionallyJoinable program context left right := by
  obtain ⟨common,first,second⟩ := joined
  exact ⟨common,first.positive,second.positive⟩

theorem ListRel.inspection_common {program : Program} {valid : ProgramWellFormed program} {context : Context}
    {left right : List Term} (children : ListRel (InspectionJoinable program valid context) left right) :
    ∃ common, ListRel (InspectionReduction program valid context) left common ∧
      ListRel (InspectionReduction program valid context) right common := by
  induction children with
  | nil => exact ⟨[],.nil,.nil⟩
  | cons head _ tail =>
    obtain ⟨common,first,second⟩ := head
    obtain ⟨rest,leftRest,rightRest⟩ := tail
    exact ⟨common :: rest,.cons first leftRest,.cons second rightRest⟩

theorem InspectionJoinable.congr {program : Program} {valid : ProgramWellFormed program} {context : Context}
    {left right : Term} (same : SameHead left right)
    (children : ListRel (InspectionJoinable program valid context) left.children right.children) :
    InspectionJoinable program valid context left right := by
  obtain ⟨common,first,second⟩ := children.inspection_common
  obtain ⟨changed,nextHead,nextChildren⟩ := left.children_realizable common first.length_eq.symm
  exact ⟨changed,InspectionReduction.congr nextHead (by rw [nextChildren]; exact first),
    InspectionReduction.congr (same.symm.trans nextHead) (by rw [nextChildren]; exact second)⟩

theorem InspectionReduction.structural_decomposition {program : Program} {valid : ProgramWellFormed program}
    {context : Context} {left right : Term} (reduced : InspectionReduction program valid context left right)
    (structural : left.StructuralHead) :
    SameHead left right ∧ ListRel (InspectionReduction program valid context) left.children right.children := by
  induction reduced with
  | refl => exact ⟨rfl,.reflexive (fun _ => .refl) _⟩
  | cons head _ tail =>
    obtain ⟨firstHead,firstChildren⟩ := head.structural_decomposition structural
    obtain ⟨lastHead,lastChildren⟩ := tail (firstHead.structuralHead_iff.mp structural)
    exact ⟨firstHead.trans lastHead,(firstChildren.imp (fun _ _ parallel => PositiveClosure.single parallel)).transitive
      (fun _ _ _ first second => first.trans second) lastChildren⟩

theorem ListRel.inspection_confluence {program : Program} {valid : ProgramWellFormed program} {context : Context}
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    {source left right : List Term} (first : ListRel (InspectionReduction program valid context) source left)
    (second : ListRel (InspectionReduction program valid context) source right) :
    ListRel (InspectionJoinable program valid context) left right := by
  induction first generalizing right with
  | nil => cases second; exact .nil
  | cons head _ tail =>
    cases second with
    | cons next rest => exact .cons (head.confluence contextKinded next) (tail rest)

/-- Finitely many alternative source exposures have one actual common query
development. Their distinct ordered positions are retained, including when
different binders use different positive exposures of the same argument. -/
theorem ListRel.inspection_common_family {program : Program} {valid : ProgramWellFormed program} {context : Context}
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    (base : List Term) (variants : List (List Term))
    (joined : ∀ variant ∈ variants, ListRel (InspectionJoinable program valid context) base variant) :
    ∃ common, ListRel (InspectionReduction program valid context) base common ∧
      ∀ variant ∈ variants, ListRel (InspectionReduction program valid context) variant common := by
  induction variants with
  | nil => exact ⟨base,.reflexive (fun _ => .refl) _,fun _ absent => False.elim (List.not_mem_nil absent)⟩
  | cons variant rest ih =>
    obtain ⟨first,baseFirst,variantFirst⟩ := (joined variant List.mem_cons_self).inspection_common
    obtain ⟨second,baseSecond,restSecond⟩ := ih (fun value member => joined value (List.mem_cons_of_mem _ member))
    obtain ⟨common,firstCommon,secondCommon⟩ := (baseFirst.inspection_confluence contextKinded baseSecond).inspection_common
    refine ⟨common,baseFirst.transitive (fun _ _ _ a b => a.trans b) firstCommon,?_⟩
    intro value member
    rcases List.mem_cons.mp member with rfl | inside
    · exact variantFirst.transitive (fun _ _ _ a b => a.trans b) firstCommon
    · exact (restSecond value inside).transitive (fun _ _ _ a b => a.trans b) secondCommon

end Glorious.Language
