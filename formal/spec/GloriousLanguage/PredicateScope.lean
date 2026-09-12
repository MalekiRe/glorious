import GloriousLanguage.PredicateInterpretation
import GloriousLanguage.ProjectionKinding

/-! Equality preserves executable lexical scope because admitted assumptions
and actual declaration reductions preserve it. Quantified predicates consume
the shared hygienic interpretation, not a prospective output-scope premise. -/
namespace Glorious.Language

theorem Term.Scoped.iff_head_children (scope : LexicalScope) (term : Term) :
    term.Scoped scope ↔ (term.mapChildren (fun _ => .unit)).Scoped scope ∧
      ∀ child ∈ term.children, child.Scoped scope := by
  constructor
  · intro admitted
    refine ⟨admitted.mapChildren _ ?_,fun _ member => admitted.child member⟩
    intro _ _
    apply Term.Scoped.of_children
    · intro id same; cases same
    · intro id same; cases same
    · intro child member; cases member
  · rintro ⟨head,children⟩
    apply Term.Scoped.of_children _ _ children
    · intro id same
      subst term
      exact head.1 id .here
    · intro id same
      subst term
      exact head.2 id .here

namespace PredicateSemantics

def scopeValuation : Valuation Prop := fun _ _ => True

/-- Non-equality atoms do not assert type scoping. Only equality can change
the lexical names of a type viewed by a source consumer. -/
def scopeAlgebra (scope : LexicalScope) : PredicateAlgebra Prop where
  node := fun term children => (term.mapChildren (fun _ => .unit)).Scoped scope ∧ ∀ child ∈ children, child
  sameHead := by intro left right same children; rw [same]
  outlives := fun _ _ => True
  typeOutlives := fun _ _ => True
  rows := fun _ _ => True
  implements := fun _ _ _ => True
  use := fun _ _ => True
  callable := fun _ _ _ _ _ => True
  runsIn := fun _ _ _ _ _ => True

theorem scopeAlgebra_eval (scope : LexicalScope) (term : Term) :
    (scopeAlgebra scope).eval scopeValuation term = term.Scoped scope := by
  by_cases parameter : ∃ id kind, term = .parameter id kind
  · obtain ⟨id,kind,rfl⟩ := parameter
    rw [TermAlgebra.eval_parameter]
    apply propext
    change True ↔ _
    refine ⟨fun _ => ?_,fun _ => True.intro⟩
    apply Term.Scoped.of_children
    · intro id same; cases same
    · intro id same; cases same
    · intro child member; cases member
  · rw [TermAlgebra.eval_node _ _ (fun id kind same => parameter ⟨id,kind,same⟩)]
    apply propext
    rw [Term.Scoped.iff_head_children]
    change (_ ∧ ∀ child ∈ term.children.map ((scopeAlgebra scope).eval scopeValuation), child) ↔ _
    apply and_congr Iff.rfl
    constructor
    · intro held child member
      rw [← scopeAlgebra_eval scope child]
      exact held _ (List.mem_map.mpr ⟨child,member,rfl⟩)
    · intro held property member
      obtain ⟨child,present,rfl⟩ := List.mem_map.mp member
      rw [scopeAlgebra_eval scope child]
      exact held child present
termination_by term
decreasing_by all_goals exact Term.child_sizeOf ‹_ ∈ term.children›

theorem scopeAlgebra_bind {program : Program} {context : Context} {binders : List Binder}
    {values : List Term} {substitution : Substitution}
    (instantiated : Instantiates binders values substitution)
    (kinded : ∀ value ∈ values, Kinding program context value value.kind) :
    (scopeAlgebra context.scope).bindValuation scopeValuation scopeValuation substitution = scopeValuation := by
  funext id kind
  cases found : substitution.get id with
  | none => simp only [TermAlgebra.bindValuation,found,Option.map_none,Option.getD_none]
  | some value =>
    simp only [TermAlgebra.bindValuation,found,Option.map_some,Option.getD_some,scopeAlgebra_eval]
    apply propext
    exact ⟨fun _ => True.intro,fun _ => (kinded value (instantiated.argument_of_get found)).scoped⟩

end PredicateSemantics

/-- Scope admission inspects the predicate already published by the source
context, including defaults and recursively quantified requirements. -/
def Constraint.Scoped (scope : LexicalScope) (constraint : Constraint) : Prop :=
  ∀ term ∈ constraint.terms, term.Scoped scope

def Context.AssumptionsScoped (context : Context) : Prop :=
  ∀ constraint ∈ context.assumptions, constraint.Scoped context.scope

theorem Constraint.Scoped.mono {first second : LexicalScope} {constraint : Constraint}
    (admitted : constraint.Scoped first)
    (regions : ∀ id ∈ first.regions, id ∈ second.regions)
    (brands : ∀ id ∈ first.brands, id ∈ second.brands) : constraint.Scoped second :=
  fun term member => ⟨fun id occurs => regions id ((admitted term member).1 id occurs),
    fun id occurs => brands id ((admitted term member).2 id occurs)⟩

theorem Context.AssumptionsScoped.bindBrand {context : Context} (admitted : context.AssumptionsScoped) (id : Identity) :
    ({ context with scope := context.scope.bindBrand id } : Context).AssumptionsScoped :=
  fun _ member => (admitted _ member).mono (fun _ present => present) (fun _ present => List.mem_cons_of_mem _ present)

theorem Context.AssumptionsScoped.bindRegion {context : Context} (admitted : context.AssumptionsScoped) (id : Identity) :
    ({ context with scope := context.scope.bindRegion id } : Context).AssumptionsScoped :=
  fun _ member => (admitted _ member).mono (fun _ present => List.mem_cons_of_mem _ present) (fun _ present => present)

def Constraint.ScopeMeaning (program : Program) (context : Context) (constraint : Constraint) : Prop :=
  (PredicateSemantics.scopeAlgebra context.scope).Holds program context
    PredicateSemantics.scopeValuation PredicateSemantics.scopeValuation constraint

theorem Constraint.Scoped.scopeMeaning {program : Program} {context : Context} {constraint : Constraint}
    (admitted : constraint.Scoped context.scope) : constraint.ScopeMeaning program context := by
  unfold Constraint.ScopeMeaning
  cases constraint <;> rw [PredicateSemantics.PredicateAlgebra.Holds]
  all_goals try trivial
  case equal left right =>
    rw [PredicateSemantics.scopeAlgebra_eval,PredicateSemantics.scopeAlgebra_eval]
    exact propext ⟨fun _ => admitted right (by simp [Constraint.terms]),
      fun _ => admitted left (by simp [Constraint.terms])⟩
  case quantified binders requirements =>
    intro values substitution instantiated kinded requirement member
    rw [PredicateSemantics.scopeAlgebra_bind instantiated kinded]
    apply Constraint.Scoped.scopeMeaning
    intro term present
    apply admitted term
    simp only [Constraint.terms,List.mem_append,List.mem_flatMap]
    exact Or.inr ⟨requirement,member,present⟩
termination_by constraint.quantifierCount
decreasing_by
  subst constraint
  simp only [Constraint.quantifierCount]
  have smaller := List.nat_le_sum_of_mem (List.mem_map_of_mem (f := Constraint.quantifierCount) member)
  omega

private theorem ListRel.forall_iff {α β : Type} {first : α → Prop} {second : β → Prop}
    {left : List α} {right : List β} (related : ListRel (fun a b => first a ↔ second b) left right) :
    (∀ a ∈ left, first a) ↔ ∀ b ∈ right, second b := by
  induction related with
  | nil => simp
  | cons head _ tail => simp only [List.forall_mem_cons,head,tail]

theorem SameHead.scoped_iff {scope : LexicalScope} {left right : Term} (same : SameHead left right)
    (children : ListRel (fun a b => a.Scoped scope ↔ b.Scoped scope) left.children right.children) :
    left.Scoped scope ↔ right.Scoped scope := by
  rw [Term.Scoped.iff_head_children scope left,Term.Scoped.iff_head_children scope right,same]
  exact and_congr Iff.rfl children.forall_iff

theorem Term.Scoped.row_iff {scope : LexicalScope} {instances tails : List Term} :
    (Term.row instances tails).Scoped scope ↔
      (∀ instanceTerm ∈ instances, instanceTerm.Scoped scope) ∧ (∀ tail ∈ tails, tail.Scoped scope) := by
  constructor
  · intro admitted
    exact ⟨fun _ member => admitted.child (List.mem_append_left _ member),
      fun _ member => admitted.child (List.mem_append_right _ member)⟩
  · rintro ⟨instances,tails⟩
    apply Term.Scoped.of_children
    · intro id same; cases same
    · intro id same; cases same
    · intro child member
      rcases List.mem_append.mp member with member | member
      · exact instances child member
      · exact tails child member

theorem RowEquivalent.scoped_iff {left right : Term} (equal : RowEquivalent left right) (scope : LexicalScope) :
    left.Scoped scope ↔ right.Scoped scope := by
  refine RowEquivalent.rec
    (motive_1 := fun left right _ => left.Scoped scope ↔ right.Scoped scope)
    (motive_2 := fun left right _ => ListRel (fun a b => a.Scoped scope ↔ b.Scoped scope) left right)
    ?refl ?symm ?trans ?congr ?permutation ?flatten ?duplicate ?tailDuplicate ?nil ?cons equal
  · intro term; exact Iff.rfl
  · intro _ _ _ ih; exact ih.symm
  · intro _ _ _ _ _ first second; exact first.trans second
  · intro _ _ same _ children; exact same.scoped_iff children
  · intro instances tails instances' tails' first second
    rw [Term.Scoped.row_iff,Term.Scoped.row_iff]
    exact and_congr
      ⟨fun held term member => held term (first.mem_iff.mpr member),
        fun held term member => held term (first.mem_iff.mp member)⟩
      ⟨fun held term member => held term (second.mem_iff.mpr member),
        fun held term member => held term (second.mem_iff.mp member)⟩
  · intros
    simp only [Term.Scoped.row_iff,List.forall_mem_cons,List.forall_mem_append]
    simp only [and_assoc,and_left_comm,and_comm]
  · intro left right rest tails _ ih
    simp only [Term.Scoped.row_iff,List.forall_mem_cons,ih,and_self_left]
  · intro instances left right tails _ ih
    simp only [Term.Scoped.row_iff,List.forall_mem_cons,ih,and_self_left]
  · exact .nil
  · intro _ _ _ _ _ _ head tail; exact .cons head tail

/-- Logical equality cannot introduce an executable lexical name. Its
quantified cases use actual kinded instances in this context; this theorem
does not assert universal context weakening or inference-variable leak safety. -/
theorem Entails.scopeMeaning {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {constraint : Constraint} (held : Entails program context constraint)
    (assumptions : context.AssumptionsScoped) : constraint.ScopeMeaning program context := by
  refine Entails.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun context left right _ => context.AssumptionsScoped →
      (left.Scoped context.scope ↔ right.Scoped context.scope))
    (motive_4 := fun _ _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ => True)
    (motive_8 := fun context constraint _ => context.AssumptionsScoped → constraint.ScopeMeaning program context)
    (motive_9 := fun context substitution constraint _ => context.AssumptionsScoped →
      (constraint.substitute substitution).ScopeMeaning program context)
    (motive_10 := fun _ _ _ _ => True)
    (motive_11 := fun context left right _ => left.Scoped context.scope ↔ right.Scoped context.scope)
    (motive_12 := fun _ _ _ _ => True)
    (motive_13 := fun _ _ _ _ _ => True)
    (motive_14 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_15 := fun _ _ _ _ _ _ _ => True)
    (motive_16 := fun _ _ _ _ _ _ => True)
    ?capStructural ?capLogical ?capEqual ?capEquation ?capEvidence ?capExpansion
    ?refl ?symm ?trans ?congr ?assumed ?equalEntailed ?definitional
    ?rowDuplicate ?tailDuplicate ?selected ?head ?tail ?equal ?empty ?assumed_1 ?same ?trans_1 ?instances ?rowEntailed
    ?assumed_2 ?scalar ?unit ?pointer ?reference ?bottom ?tuple ?array ?nominal ?callable ?label ?environment
    ?available ?bindings ?equal_1 ?typeEntailed ?checkedCallable ?checkedRunsIn ?assumed_3 ?constraintCongr ?equality
    ?outlivesRefl ?outlivesStatic ?outlivesTrans ?typeOutlives
    ?rows ?implementation ?use ?quantified ?quantifiedInstance ?instantiated
    ?stepAlias ?stepProjection ?stepDefault
    ?defRefl ?defSymm ?defTrans ?defCongr ?defStep ?defRow
    ?redRefl ?redStep ?redTrans ?redCongr ?redRow
    ?matched ?domainValid ?inferParameter ?inferChild ?inferSource ?inferQuery ?inferArgument held assumptions
  all_goals intros
  all_goals try exact True.intro
  all_goals try (solve | unfold Constraint.ScopeMeaning; rw [PredicateSemantics.PredicateAlgebra.Holds]; exact True.intro)
  case refl => exact Iff.rfl
  case symm _ ih admitted => exact (ih admitted).symm
  case trans _ _ first second admitted => exact (first admitted).trans (second admitted)
  case congr same _ children admitted =>
    exact same.scoped_iff (ListRel.of_at same.children_length
      (fun index first second leftAt rightAt => children index first second leftAt rightAt admitted))
  case assumed member admitted =>
    exact ⟨fun _ => admitted _ member _ (by simp [Constraint.terms]),
      fun _ => admitted _ member _ (by simp [Constraint.terms])⟩
  case equalEntailed _ ih admitted =>
    have interpreted := ih admitted
    unfold Constraint.ScopeMeaning at interpreted
    rw [PredicateSemantics.PredicateAlgebra.Holds,PredicateSemantics.scopeAlgebra_eval,
      PredicateSemantics.scopeAlgebra_eval] at interpreted
    exact Iff.of_eq interpreted
  case definitional _ ih _ => exact ih
  case rowDuplicate _ ih admitted =>
    simp only [Term.Scoped.row_iff,List.forall_mem_cons,ih admitted,and_self_left]
  case tailDuplicate _ ih admitted =>
    simp only [Term.Scoped.row_iff,List.forall_mem_cons,ih admitted,and_self_left]
  case assumed_3 member admitted => exact (admitted _ member).scopeMeaning
  case constraintCongr context template before after leftSub rightSub _ left right _ equal held admitted =>
    exact (PredicateSemantics.PredicateAlgebra.holds_substitution_congr
      (PredicateSemantics.scopeAlgebra context.scope) program context
      PredicateSemantics.scopeValuation PredicateSemantics.scopeValuation
      (fun id kind => by
        rw [PredicateSemantics.scopeAlgebra_eval,PredicateSemantics.scopeAlgebra_eval]
        exact propext (equal id kind admitted)) left right).mp (held admitted)
  case equality _ ih admitted =>
    unfold Constraint.ScopeMeaning
    rw [PredicateSemantics.PredicateAlgebra.Holds,PredicateSemantics.scopeAlgebra_eval,
      PredicateSemantics.scopeAlgebra_eval]
    exact propext (ih admitted)
  case quantified context binders requirements _ instances admitted =>
    apply PredicateSemantics.PredicateAlgebra.holds_quantified
    intro values substitution instantiated kinded requirement member
    exact instances values substitution instantiated kinded requirement member admitted
  case quantifiedInstance context binders requirements values substitution requirement result _ instantiated kinded member graph ih admitted =>
    exact PredicateSemantics.PredicateAlgebra.holds_quantifiedInstance
      (PredicateSemantics.scopeAlgebra context.scope) program context PredicateSemantics.scopeValuation
      (ih admitted) instantiated kinded member graph
  case instantiated graph _ ih admitted => simpa only [graph.2] using ih admitted
  case defRefl => exact Iff.rfl
  case defSymm _ ih => exact ih.symm
  case defTrans _ _ first second => exact first.trans second
  case defCongr same _ children => exact same.scoped_iff (ListRel.of_at same.children_length children)
  case defStep step _ =>
    obtain ⟨left,right⟩ := step.kinding valid
    exact ⟨fun _ => right.scoped,fun _ => left.scoped⟩
  case defRow row => exact row.scoped_iff _

theorem Equal.scoped_iff {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Term} (equal : Equal program context left right)
    (assumptions : context.AssumptionsScoped) : left.Scoped context.scope ↔ right.Scoped context.scope := by
  have interpreted := (Entails.equality equal).scopeMeaning valid assumptions
  unfold Constraint.ScopeMeaning at interpreted
  rw [PredicateSemantics.PredicateAlgebra.Holds,PredicateSemantics.scopeAlgebra_eval,
    PredicateSemantics.scopeAlgebra_eval] at interpreted
  exact Iff.of_eq interpreted

end Glorious.Language
