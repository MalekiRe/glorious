import GloriousLanguage.QuotientInterpretation

/-! Logical equality preserves actual source kinding when its assumptions
are admitted predicates. Quantified assumptions use their real hygienic
instances; the model does not silently drop nested equality requirements. -/
namespace Glorious.Language

theorem Constraint.quantifierCount_substitute (substitution : Substitution) (constraint : Constraint) :
    (constraint.substitute substitution).quantifierCount = constraint.quantifierCount := by
  cases constraint <;> simp only [Constraint.substitute,Constraint.quantifierCount]
  case quantified binders requirements =>
    simp only [List.map_map,Function.comp_def]
    apply congrArg (fun values : List Nat => 1 + values.sum)
    calc
      _ = requirements.attach.map (fun requirement => requirement.val.quantifierCount) := by
        apply List.map_congr_left
        intro requirement _
        rw [Constraint.quantifierCount_substitute,Constraint.quantifierCount_renameParameters]
      _ = _ := by simp
termination_by constraint.quantifierCount
decreasing_by
  simp only [Constraint.quantifierCount_renameParameters,Constraint.quantifierCount]
  have smaller := List.nat_le_sum_of_mem (List.mem_map_of_mem (f := Constraint.quantifierCount) requirement.property)
  omega

namespace KindingQuotient

def Related (program : Program) (context : Context) (left right : Term) : Prop :=
  left.kind = right.kind ∧ ∀ kind, Kinding program context left kind ↔ Kinding program context right kind

theorem Related.refl (program : Program) (context : Context) (term : Term) : Related program context term term :=
  ⟨rfl,fun _ => Iff.rfl⟩

theorem Related.symm {program : Program} {context : Context} {left right : Term}
    (related : Related program context left right) : Related program context right left :=
  ⟨related.1.symm,fun kind => (related.2 kind).symm⟩

theorem Related.trans {program : Program} {context : Context} {left middle right : Term}
    (first : Related program context left middle) (second : Related program context middle right) :
    Related program context left right := ⟨first.1.trans second.1,fun kind => (first.2 kind).trans (second.2 kind)⟩

def setoid (program : Program) (context : Context) : Setoid Term where
  r := Related program context
  iseqv := ⟨Related.refl program context,Related.symm,Related.trans⟩

theorem congr {program : Program} {context : Context} {left right : Term} (same : SameHead left right)
    (children : ListRel (Related program context) left.children right.children) : Related program context left right := by
  refine ⟨sameHead_kind same,fun kind => ?_⟩
  exact ⟨fun kinded => kinded.congr_children same (children.imp (fun _ _ related kind => (related.2 kind).mp)),
    fun kinded => kinded.congr_children same.symm (children.swap.imp (fun _ _ related kind => (related.2 kind).mpr))⟩

theorem of_kinded {program : Program} {context : Context} {left right : Term} {kind : Kind}
    (first : Kinding program context left kind) (second : Kinding program context right kind) :
    Related program context left right := by
  refine ⟨first.term_kind.trans second.term_kind.symm,fun other => ?_⟩
  constructor
  · intro typed
    obtain rfl := first.term_kind.symm.trans typed.term_kind
    exact second
  · intro typed
    obtain rfl := second.term_kind.symm.trans typed.term_kind
    exact first

abbrev Class (program : Program) (context : Context) := PredicateSemantics.TermQuotient.Class (setoid program context)

def ofTerm {program : Program} {context : Context} (term : Term) : Class program context :=
  PredicateSemantics.TermQuotient.ofTerm term

theorem ofTerm_eq {program : Program} {context : Context} {left right : Term} :
    (ofTerm left : Class program context) = ofTerm right ↔ Related program context left right :=
  PredicateSemantics.TermQuotient.ofTerm_eq

noncomputable def algebra (program : Program) (context : Context) : PredicateSemantics.PredicateAlgebra (Class program context) :=
  PredicateSemantics.TermQuotient.algebra (setoid program context) congr

def canonical {program : Program} {context : Context} : PredicateSemantics.Valuation (Class program context) :=
  PredicateSemantics.TermQuotient.canonical

theorem eval_canonical {program : Program} {context : Context} (term : Term) :
    (algebra program context).eval canonical term = ofTerm term :=
  PredicateSemantics.TermQuotient.eval_canonical (setoid := setoid program context) congr term

def Holds (program : Program) (context : Context) (constraint : Constraint) : Prop :=
  (algebra program context).Holds program context canonical canonical constraint

theorem holds_equal {program : Program} {context : Context} {left right : Term} :
    Holds program context (.equal left right) ↔ Related program context left right := by
  unfold Holds PredicateSemantics.PredicateAlgebra.Holds
  rw [eval_canonical,eval_canonical,ofTerm_eq]

theorem Related.rowDuplicate {program : Program} {context : Context} {left right : Term}
    {rest tails : List Term} (equal : Related program context left right) :
    Related program context (.row (left :: right :: rest) tails) (.row (left :: rest) tails) := by
  have changed : Related program context (.row (left :: right :: rest) tails) (.row (left :: left :: rest) tails) := by
    apply KindingQuotient.congr (by rfl)
    exact (ListRel.cons (.refl _ _ _) (.cons equal.symm
      (.reflexive (Related.refl program context) rest))).append (.reflexive (Related.refl program context) tails)
  refine ⟨rfl,fun kind => ?_⟩
  exact (changed.2 kind).trans ((RowEquivalent.duplicate (left := left) (right := left) (rest := rest)
    (tails := tails) .refl).kinding_iff kind)

theorem Related.tailDuplicate {program : Program} {context : Context} {left right : Term}
    {instances tails : List Term} (equal : Related program context left right) :
    Related program context (.row instances (left :: right :: tails)) (.row instances (left :: tails)) := by
  have changed : Related program context (.row instances (left :: right :: tails)) (.row instances (left :: left :: tails)) := by
    apply KindingQuotient.congr (by rfl)
    exact (ListRel.reflexive (Related.refl program context) instances).append
      (.cons (.refl _ _ _) (.cons equal.symm (.reflexive (Related.refl program context) tails)))
  refine ⟨rfl,fun kind => ?_⟩
  exact (changed.2 kind).trans ((RowEquivalent.tailDuplicate (left := left) (right := left) (instances := instances)
    (tails := tails) .refl).kinding_iff kind)

end KindingQuotient

/-- Admission supplies the entire semantic equality invariant, including
every nested quantified requirement at its actual kinded arguments. -/
theorem ConstraintKinded.kinding_meaning {program : Program} {context : Context} {constraint : Constraint}
    (admitted : ConstraintKinded program context constraint) : KindingQuotient.Holds program context constraint := by
  cases constraint
  all_goals try { solve | simp only [KindingQuotient.Holds,PredicateSemantics.PredicateAlgebra.Holds,
    KindingQuotient.algebra,PredicateSemantics.TermQuotient.algebra] }
  case equal left right =>
    apply KindingQuotient.holds_equal.mpr
    cases admitted with
    | equal first second => exact KindingQuotient.of_kinded first second
  case quantified binders requirements =>
    apply (KindingQuotient.algebra program context).holds_quantified program context KindingQuotient.canonical
    intro values substitution instantiated kinded requirement member
    obtain ⟨_,instanceKinded⟩ := admitted.quantified_instance instantiated kinded member
    exact instanceKinded.kinding_meaning
termination_by constraint.quantifierCount
decreasing_by
  subst constraint
  simp only [Constraint.quantifierCount_substitute,Constraint.quantifierCount]
  have smaller := List.nat_le_sum_of_mem (List.mem_map_of_mem (f := Constraint.quantifierCount) member)
  omega

theorem Equal.kinding_related {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Term} (equal : Equal program context left right)
    (admitted : ∀ constraint ∈ context.assumptions, ConstraintKinded program context constraint) :
    KindingQuotient.Related program context left right := by
  apply Equal.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun context left right _ =>
      (∀ constraint ∈ context.assumptions, ConstraintKinded program context constraint) →
        KindingQuotient.Related program context left right)
    (motive_4 := fun _ _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ => True)
    (motive_8 := fun context constraint _ =>
      (∀ constraint ∈ context.assumptions, ConstraintKinded program context constraint) →
        KindingQuotient.Holds program context constraint)
    (motive_9 := fun context substitution constraint _ =>
      (∀ constraint ∈ context.assumptions, ConstraintKinded program context constraint) →
        KindingQuotient.Holds program context (constraint.substitute substitution))
    (motive_10 := fun _ _ _ _ => True)
    (motive_11 := fun _ _ _ _ => True)
    (motive_12 := fun _ _ _ _ => True)
    (motive_13 := fun _ _ _ _ _ => True)
    (motive_14 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_15 := fun _ _ _ _ _ _ _ => True)
    (motive_16 := fun _ _ _ _ _ _ => True)
    <;> try assumption
  all_goals intros
  all_goals try exact True.intro
  all_goals try {
    rename_i member admitted
    exact (admitted _ member).kinding_meaning }
  all_goals try {
    rename_i member admitted
    exact KindingQuotient.holds_equal.mp ((admitted _ member).kinding_meaning) }
  all_goals try { solve | simp only [KindingQuotient.Holds,PredicateSemantics.PredicateAlgebra.Holds,
    KindingQuotient.algebra,PredicateSemantics.TermQuotient.algebra] }
  case refl => exact .refl _ _ _
  case symm _ _ _ _ ih admitted => exact (ih admitted).symm
  case trans _ _ _ _ _ _ first second admitted => exact (first admitted).trans (second admitted)
  case congrChildren _ _ _ same _ children admitted =>
    exact KindingQuotient.congr same (ListRel.of_at same.children_length
      (fun index first second leftAt rightAt => children index first second leftAt rightAt admitted))
  case entailed _ _ _ _ ih admitted => exact KindingQuotient.holds_equal.mp (ih admitted)
  case definitional _ _ _ equal _ _ => exact ⟨equal.kind_eq valid,equal.kinding_iff valid⟩
  case rowDuplicate _ _ _ _ _ _ ih admitted => exact (ih admitted).rowDuplicate
  case tailDuplicate _ _ _ _ _ _ ih admitted => exact (ih admitted).tailDuplicate
  case congrSubstitution context _ _ _ _ _ _ before after _ equal held admitted =>
    exact ((KindingQuotient.algebra program context).holds_substitution_congr program context
      KindingQuotient.canonical KindingQuotient.canonical
      (fun id kind => by
        rw [KindingQuotient.eval_canonical,KindingQuotient.eval_canonical]
        exact KindingQuotient.ofTerm_eq.mpr (equal id kind admitted)) before after).mp (held admitted)
  case equality _ _ _ _ ih admitted => exact KindingQuotient.holds_equal.mpr (ih admitted)
  case quantified context _ _ _ instances admitted =>
    exact (KindingQuotient.algebra program context).holds_quantified program context KindingQuotient.canonical
      (fun values substitution instantiated kinded requirement member =>
        instances values substitution instantiated kinded requirement member admitted)
  case quantifiedInstance context _ _ _ _ _ _ _ instantiated kinded member graph held admitted =>
    exact (KindingQuotient.algebra program context).holds_quantifiedInstance program context KindingQuotient.canonical
      (held admitted) instantiated kinded member graph
  case instantiated _ _ _ _ graph _ held admitted =>
    rw [← graph.2]
    exact held admitted

/-- Kinded source assumptions cannot make a kinded type equal to an
ill-kinded type. This includes every logical congruence and quantified rule,
not just the declaration-only definitional subsystem. -/
theorem Equal.kinding_iff {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Term} (equal : Equal program context left right)
    (admitted : ∀ constraint ∈ context.assumptions, ConstraintKinded program context constraint) (kind : Kind) :
    Kinding program context left kind ↔ Kinding program context right kind :=
  (equal.kinding_related valid admitted).2 kind

theorem Equal.kind_eq {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Term} (equal : Equal program context left right)
    (admitted : ∀ constraint ∈ context.assumptions, ConstraintKinded program context constraint) :
    left.kind = right.kind := (equal.kinding_related valid admitted).1

end Glorious.Language
