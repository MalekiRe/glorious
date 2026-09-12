import GloriousLanguage.DefinitionalSeparation
import GloriousLanguage.LayoutValidity
import GloriousLanguage.LogicalEvidence

/-! Uniqueness of actual target layouts. The proof compares the existing
layout derivations and their real declaration substitutions; it does not add
another layout evaluator or assume constructor separation. -/
namespace Glorious.Language

theorem FieldsLayout.unique {start : Nat} {fields : List Layout} {left right : List Nat} {first second : Nat}
    (before : FieldsLayout start fields left first) (after : FieldsLayout start fields right second) :
    left = right ∧ first = second := by
  induction before generalizing right second with
  | nil => cases after; exact ⟨rfl,rfl⟩
  | cons _ _ ih =>
    cases after with
    | cons _ rest =>
      obtain ⟨rfl,rfl⟩ := ih rest
      exact ⟨rfl,rfl⟩

theorem AggregateLayout.unique {fields : List Layout} {left right : Layout}
    (first : AggregateLayout fields left) (second : AggregateLayout fields right) : left = right := by
  obtain ⟨_,firstFields,firstAlignment,firstSize,firstTag,firstPayload,firstVariants⟩ := first
  obtain ⟨_,secondFields,secondAlignment,secondSize,secondTag,secondPayload,secondVariants⟩ := second
  obtain ⟨offsets,stop⟩ := firstFields.unique secondFields
  cases left; cases right
  simp_all

theorem ArrayLayout.unique {element : Layout} {length : Nat} {left right : Layout}
    (first : ArrayLayout element length left) (second : ArrayLayout element length right) : left = right :=
  first.2.trans second.2.symm

theorem CRecordLayout.unique {target : TargetProfile} {fields : List Layout} {left right : Layout}
    (first : CRecordLayout target fields left) (second : CRecordLayout target fields right) : left = right :=
  first.2.1.trans second.2.1.symm

theorem EnumLayout.unique {variants : List Layout} {left right : Layout}
    (first : EnumLayout variants left) (second : EnumLayout variants right) : left = right := by
  obtain ⟨_,_,firstTag,firstEnough,firstLeast,firstAlignment,firstPayload,firstSize,firstOffsets,firstVariants⟩ := first
  obtain ⟨_,_,secondTag,secondEnough,secondLeast,secondAlignment,secondPayload,secondSize,secondOffsets,secondVariants⟩ := second
  have tags : left.tagBytes = right.tagBytes := by
    apply Nat.le_antisymm
    · by_cases larger : left.tagBytes ≤ right.tagBytes
      · exact larger
      have smaller := firstLeast right.tagBytes secondTag (by omega)
      omega
    · by_cases larger : right.tagBytes ≤ left.tagBytes
      · exact larger
      have smaller := secondLeast left.tagBytes firstTag (by omega)
      omega
  cases left; cases right
  simp_all

private theorem ListRel.common_source {α β γ : Type} {first : α → β → Prop} {second : α → γ → Prop}
    {relation : β → γ → Prop} {source : List α} {left : List β} {right : List γ}
    (before : ListRel first source left) (after : ListRel second source right)
    (combine : ∀ a b c, first a b → second a c → relation b c) : ListRel relation left right := by
  induction before generalizing right with
  | nil => cases after; exact .nil
  | cons head _ ih =>
    cases after with
    | cons other tail => exact .cons (combine _ _ _ head other) (ih tail)

private theorem List.unique_nonzero_layout {layouts : List Layout} {first second : Nat} {left right : Layout}
    (before : layouts[first]? = some left)
    (zero : ∀ index layout, layouts[index]? = some layout → index ≠ first → layout.size = 0)
    (after : layouts[second]? = some right) (positive : 0 < right.size) : left = right := by
  by_cases same : second = first
  · subst second
    exact Option.some.inj (before.symm.trans after)
  · have empty := zero second right after same
    omega

private def LayoutDetermines (program : Program) (context : Context) (source : Term) (layout : Layout) : Prop :=
  ∀ target result, DefinitionallyEqual program context source target → LayoutOf program context target result → layout = result

private def CLayoutDetermines (program : Program) (context : Context) (source : Term) (layout : Layout) : Prop :=
  ∀ target result, DefinitionallyEqual program context source target → CCompatible program context target result → layout = result

private theorem ListRel.determined_values {α β : Type} {relation : α → α → Prop} {judgment : α → β → Prop}
    {source target : List α} {first second : List β}
    (determined : ListRel (fun source first => ∀ target second, relation source target → judgment target second → first = second) source first)
    (arguments : ListRel relation source target) (layouts : ListRel judgment target second) : first = second := by
  induction determined generalizing target second with
  | nil => cases arguments; cases layouts; rfl
  | cons determined _ ih =>
    cases arguments with
    | cons equal rest =>
      cases layouts with
      | cons layout tail => rw [determined _ _ equal layout,ih rest tail]

theorem LayoutOf.scalar_unique {program : Program} (valid : ProgramWellFormed program)
    {context : Context} (closed : context.assumptions = []) {type : Term} {layout : Layout} {scalar : Scalar}
    (derived : LayoutOf program context type layout) (converted : DefinitionallyEqual program context type (.scalar scalar)) :
    layout = ⟨scalar.bytes program.input.target,program.input.target.scalarAlignment scalar,[],0,0,[]⟩ := by
  have contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement := by
    intro requirement member; rw [closed] at member; cases member
  apply LayoutOf.rec
    (motive_1 := fun type layout _ => DefinitionallyEqual program context type (.scalar scalar) →
      layout = ⟨scalar.bytes program.input.target,program.input.target.scalarAlignment scalar,[],0,0,[]⟩)
    (motive_2 := fun _ _ _ => True) (motive_3 := fun _ _ _ => True)
    (motive_4 := fun _ _ _ => True) (motive_5 := fun _ _ _ => True) (motive_6 := fun _ _ _ => True)
    <;> try assumption
  all_goals intros
  all_goals try exact True.intro
  all_goals try {
    rename_i equal
    have head := (equal.structural_decomposition valid contextKinded True.intro True.intro).1
    cases head <;> rfl }
  case alias _ _ _ equal _ ih converted => exact ih ((equal.closed_definitional closed).trans converted)

theorem LayoutOf.unique_convertible {program : Program} (valid : ProgramWellFormed program)
    {context : Context} (closed : context.assumptions = []) {source target : Term} {left right : Layout}
    (first : LayoutOf program context source left) (equal : DefinitionallyEqual program context source target)
    (second : LayoutOf program context target right) : left = right := by
  have contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement := by
    intro requirement member; rw [closed] at member; cases member
  have determined : LayoutDetermines program context source left := by
    apply LayoutOf.rec
      (motive_1 := fun type layout _ => LayoutDetermines program context type layout)
      (motive_2 := fun types layout _ => ∀ others result,
        ListRel (DefinitionallyEqual program context) types others → FieldsHaveLayout program context others result → layout = result)
      (motive_3 := fun type layout _ => CLayoutDetermines program context type layout)
      (motive_4 := fun types layouts _ => ListRel (LayoutDetermines program context) types layouts)
      (motive_5 := fun types layouts _ => ListRel (fun types layout => ∀ others result,
        ListRel (DefinitionallyEqual program context) types others → FieldsHaveLayout program context others result → layout = result) types layouts)
      (motive_6 := fun types layouts _ => ListRel (CLayoutDetermines program context) types layouts)
      <;> try assumption
    all_goals intros
    all_goals try exact ListRel.nil
    all_goals try exact ListRel.cons (by assumption) (by assumption)
    case alias _ _ _ equal _ ih => exact fun _ _ converted next => ih _ _ ((equal.closed_definitional closed).trans converted) next
    case alias _ _ _ equal _ ih => exact fun _ _ converted next => ih _ _ ((equal.closed_definitional closed).trans converted) next
    case fields _ _ _ _ aggregate ih _ _ converted next =>
      cases next with
      | fields layouts other =>
        have tables := ListRel.determined_values ih converted layouts
        subst tables
        exact aggregate.unique other
    all_goals simp only [LayoutDetermines,CLayoutDetermines]
    all_goals intro other result converted derived
    all_goals revert converted
    all_goals first
      | induction derived using LayoutOf.rec
          (motive_2 := fun _ _ _ => True) (motive_3 := fun _ _ _ => True)
          (motive_4 := fun _ _ _ => True) (motive_5 := fun _ _ _ => True) (motive_6 := fun _ _ _ => True)
      | induction derived using CCompatible.rec
          (motive_1 := fun _ _ _ => True) (motive_2 := fun _ _ _ => True)
          (motive_4 := fun _ _ _ => True) (motive_5 := fun _ _ _ => True) (motive_6 := fun _ _ _ => True)
    all_goals intros
    all_goals try exact True.intro
    all_goals try {
      rename_i equal _ ih converted
      exact ih (converted.trans (equal.closed_definitional closed).symm) }
    all_goals try {
      rename_i converted
      have parts := converted.structural_decomposition valid contextKinded True.intro True.intro
      cases parts.1 <;> rfl }
    all_goals try rfl
    case tuple.tuple =>
      rename_i _ _ _ _ aggregate ih _ _ _ layouts nextAggregate _ converted
      have children := (converted.structural_decomposition valid contextKinded True.intro True.intro).2
      have same := ListRel.determined_values ih children layouts
      rw [same] at aggregate
      exact aggregate.unique nextAggregate
    case bindings.bindings =>
      rename_i _ _ _ _ _ _ aggregate ih _ _ _ _ _ layouts nextAggregate _ converted
      have children := (converted.structural_decomposition valid contextKinded True.intro True.intro).2
      cases children with
      | cons _ tail =>
        cases tail with
        | cons _ fields =>
          have same := ListRel.determined_values ih fields layouts
          rw [same] at aggregate
          exact aggregate.unique nextAggregate
    case environment.environment =>
      rename_i _ _ _ _ _ _ aggregate ih _ _ _ _ _ layouts nextAggregate _ converted
      have children := (converted.structural_decomposition valid contextKinded True.intro True.intro).2
      cases children with
      | cons _ tail =>
        cases tail with
        | cons _ fields =>
          have same := ListRel.determined_values ih fields layouts
          rw [same] at aggregate
          exact aggregate.unique nextAggregate
    case callable.callable =>
      rename_i id _ _ _ _ declared _ aggregate ih nextId _ _ _ _ nextDeclared layouts nextAggregate _ converted
      obtain ⟨head,arguments⟩ := converted.structural_decomposition valid contextKinded True.intro True.intro
      have identity : id = nextId := (Term.callable.inj head).1
      subst nextId
      have captures := declared.convertible nextDeclared arguments
      have same := ListRel.determined_values ih captures layouts
      rw [same] at aggregate
      exact aggregate.unique nextAggregate
    case array.array =>
      rename_i _ _ _ _ _ _ _ _ _ array ih _ _ _ _ _ _ _ _ layout nextArray _ converted
      have children := (converted.structural_decomposition valid contextKinded True.intro True.intro).2
      cases children with
      | cons elements tail =>
        cases tail with
        | cons lengths _ =>
          have constants := (lengths.structural_decomposition valid contextKinded True.intro True.intro).1
          have values := Term.constant.inj constants
          cases values
          have same := ih _ _ elements layout
          rw [same] at array
          exact array.unique nextArray
    all_goals try {
      rename_i converted
      exact (show LayoutDetermines program context _ _ from by assumption) _ _ converted (by assumption) }
    all_goals try {
      rename_i converted
      exact (show CLayoutDetermines program context _ _ from by assumption) _ _ converted (by assumption) }
    all_goals
      rename_i converted
      obtain ⟨rfl,arguments⟩ := converted.nominal_injective valid contextKinded
      simp_all
    case nominal.nominal =>
      rename_i _ _ inst graph _ choices _ ih nextInst nextGraph nextLayouts nextChoices _ _
      have tables := inst.convertible_tables nextInst arguments
      have fields := graph.common_source nextGraph (fun _ _ _ before after => before.substituted_conversion after tables)
      have same := ListRel.determined_values ih fields nextLayouts
      rw [same] at choices
      rcases choices with ⟨enumeration,layout⟩ | ⟨record,single⟩
      · rcases nextChoices with ⟨_,otherLayout⟩ | ⟨record,_⟩
        · exact layout.unique otherLayout
        · cases enumeration.symm.trans record
      · rcases nextChoices with ⟨enumeration,_⟩ | ⟨_,otherSingle⟩
        · cases enumeration.symm.trans record
        · exact (List.cons.inj (single.symm.trans otherSingle)).1
    case record.record =>
      rename_i _ _ _ _ inst graph _ record ih _ nextInst nextGraph nextLayouts nextRecord _
      have tables := inst.convertible_tables nextInst arguments
      have fields := graph.substituted_conversion nextGraph tables
      have same := ListRel.determined_values ih fields nextLayouts
      rw [same] at record
      exact record.unique nextRecord
    case transparent.transparent =>
      rename_i _ _ _ _ _ inst graph _ selectedAt _ zeros ih _ _ nextInst nextGraph nextLayouts nextAt positive _ _ _
      have tables := inst.convertible_tables nextInst arguments
      have fields := graph.substituted_conversion nextGraph tables
      have same := ListRel.determined_values ih fields nextLayouts
      rw [same] at selectedAt zeros
      have represented := List.unique_nonzero_layout selectedAt (fun _ _ found different => (zeros _ _ found different).1) nextAt positive
      rw [represented]
      exact ⟨rfl,rfl⟩
  exact determined target right equal second

theorem LayoutOf.unique {program : Program} (valid : ProgramWellFormed program)
    {context : Context} (closed : context.assumptions = []) {type : Term} {left right : Layout}
    (first : LayoutOf program context type left) (second : LayoutOf program context type right) : left = right :=
  first.unique_convertible valid closed .refl second

theorem LayoutOf.equal_unique {program : Program} (valid : ProgramWellFormed program)
    {context : Context} (closed : context.assumptions = []) {source target : Term} {left right : Layout}
    (first : LayoutOf program context source left) (equal : Equal program context source target)
    (second : LayoutOf program context target right) : left = right :=
  first.unique_convertible valid closed (equal.closed_definitional closed) second

theorem CCompatible.unique_convertible {program : Program} (valid : ProgramWellFormed program)
    {context : Context} (closed : context.assumptions = []) {source target : Term} {left right : Layout}
    (first : CCompatible program context source left) (equal : DefinitionallyEqual program context source target)
    (second : CCompatible program context target right) : left = right :=
  first.layoutOf.unique_convertible valid closed equal second.layoutOf

theorem CCompatible.unique {program : Program} (valid : ProgramWellFormed program)
    {context : Context} (closed : context.assumptions = []) {type : Term} {left right : Layout}
    (first : CCompatible program context type left) (second : CCompatible program context type right) : left = right :=
  first.unique_convertible valid closed .refl second

theorem FieldsHaveLayout.unique_convertible {program : Program} (valid : ProgramWellFormed program)
    {context : Context} (closed : context.assumptions = []) {source target : List Term} {left right : Layout}
    (first : FieldsHaveLayout program context source left)
    (equal : ListRel (DefinitionallyEqual program context) source target)
    (second : FieldsHaveLayout program context target right) : left = right := by
  cases first with
  | fields layouts aggregate =>
    cases second with
    | fields others result =>
      have head : SameHead (.tuple source) (.tuple target) := by
        change Term.tuple (source.map (fun _ => .unit)) = Term.tuple (target.map (fun _ => .unit))
        simp only [List.map_const',equal.length_eq]
      exact (LayoutOf.tuple layouts aggregate).unique_convertible valid closed (.congr head equal) (.tuple others result)

end Glorious.Language
