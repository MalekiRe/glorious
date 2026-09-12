import GloriousLanguage.JoinabilityCongruence
import GloriousLanguage.PredicateInterpretation

/-! An assumption-free logical equality has no authority beyond actual
definitional conversion. The shared predicate interpretation handles hygienic
substitution and quantifiers; no normalization or confluence is assumed. -/
namespace Glorious.Language

namespace DefinitionalQuotient

def setoid (program : Program) (context : Context) : Setoid Term where
  r := DefinitionallyEqual program context
  iseqv := ⟨fun _ => .refl,fun equal => .symm equal,fun first second => .trans first second⟩

abbrev Class (program : Program) (context : Context) := Quotient (setoid program context)

def ofTerm {program : Program} {context : Context} (term : Term) : Class program context :=
  Quotient.mk _ term

theorem ofTerm_eq {program : Program} {context : Context} {left right : Term} :
    (ofTerm left : Class program context) = ofTerm right ↔ DefinitionallyEqual program context left right :=
  ⟨Quotient.exact,fun equal => Quotient.sound equal⟩

private theorem represented {program : Program} {context : Context} (value : Class program context) :
    ∃ term, ofTerm term = value := by
  induction value using Quotient.ind with
  | _ term => exact ⟨term,rfl⟩

noncomputable def representative {program : Program} {context : Context} (value : Class program context) : Term :=
  Classical.choose (represented value)

theorem representative_eq {program : Program} {context : Context} (value : Class program context) :
    ofTerm (representative value) = value := Classical.choose_spec (represented value)

noncomputable def rebuild (head : Term) (children : List Term) (lengths : children.length = head.children.length) : Term :=
  Classical.choose (head.children_realizable children lengths)

theorem rebuild_spec (head : Term) (children : List Term) (lengths : children.length = head.children.length) :
    SameHead head (rebuild head children lengths) ∧ (rebuild head children lengths).children = children :=
  Classical.choose_spec (head.children_realizable children lengths)

noncomputable def node {program : Program} {context : Context} (head : Term) (children : List (Class program context)) :
    Class program context :=
  if lengths : children.length = head.children.length then
    ofTerm (rebuild head (children.map representative) (by simpa only [List.length_map] using lengths))
  else ofTerm .unit

theorem node_spec {program : Program} {context : Context} (head : Term) (children : List (Class program context))
    (lengths : children.length = head.children.length) :
    ∃ rebuilt, SameHead head rebuilt ∧ rebuilt.children = children.map representative ∧ node head children = ofTerm rebuilt := by
  unfold node
  rw [dif_pos lengths]
  exact ⟨_,(rebuild_spec _ _ _).1,(rebuild_spec _ _ _).2,rfl⟩

theorem node_sameHead {program : Program} {context : Context} {left right : Term} (same : SameHead left right)
    (children : List (Class program context)) : node left children = node right children := by
  by_cases lengths : children.length = left.children.length
  · obtain ⟨first,firstHead,firstChildren,firstNode⟩ := node_spec left children lengths
    obtain ⟨second,secondHead,secondChildren,secondNode⟩ := node_spec right children (lengths.trans same.children_length)
    rw [firstNode,secondNode]
    apply ofTerm_eq.mpr
    apply DefinitionallyEqual.congr (firstHead.symm.trans (same.trans secondHead))
    rw [firstChildren,secondChildren]
    exact .reflexive (fun _ => .refl) _
  · have otherLengths : children.length ≠ right.children.length := by rw [← same.children_length]; exact lengths
    simp only [node,dif_neg lengths,dif_neg otherLengths]

noncomputable def algebra (program : Program) (context : Context) : PredicateSemantics.PredicateAlgebra (Class program context) where
  node := node
  sameHead := node_sameHead
  outlives := fun _ _ => True
  typeOutlives := fun _ _ => True
  rows := fun _ _ => True
  implements := fun _ _ _ => True
  use := fun _ _ => True
  callable := fun _ _ _ _ _ => True
  runsIn := fun _ _ _ _ _ => True

def canonical {program : Program} {context : Context} : PredicateSemantics.Valuation (Class program context) :=
  fun id kind => ofTerm (.parameter id kind)

theorem eval_canonical {program : Program} {context : Context} (term : Term) :
    (algebra program context).eval canonical term = ofTerm term := by
  by_cases parameter : ∃ id kind, term = .parameter id kind
  · obtain ⟨id,kind,rfl⟩ := parameter
    exact PredicateSemantics.TermAlgebra.eval_parameter _ _ _ _
  · have notParameter : ∀ id kind, term ≠ .parameter id kind := fun id kind equal => parameter ⟨id,kind,equal⟩
    rw [PredicateSemantics.TermAlgebra.eval_node _ _ notParameter]
    have children : term.children.map ((algebra program context).eval canonical) = term.children.map ofTerm := by
      apply List.map_congr_left
      intro child _
      exact eval_canonical child
    rw [children]
    obtain ⟨rebuilt,same,reconstructed,node⟩ := node_spec term (term.children.map (ofTerm (program := program) (context := context))) (by simp)
    change DefinitionalQuotient.node term (term.children.map ofTerm) = ofTerm term
    rw [node]
    apply ofTerm_eq.mpr
    apply DefinitionallyEqual.congr same.symm
    rw [reconstructed,List.map_map]
    simpa only [List.map_id,Function.comp_def] using ListRel.maps term.children (fun term => representative (ofTerm term)) id (by
      intro child _
      exact ofTerm_eq.mp (representative_eq (ofTerm child)))
termination_by term
decreasing_by exact Term.child_sizeOf ‹_ ∈ term.children›

def Holds (program : Program) (context : Context) (constraint : Constraint) : Prop :=
  (algebra program context).Holds program context canonical canonical constraint

theorem holds_equal {program : Program} {context : Context} {left right : Term} :
    Holds program context (.equal left right) ↔ DefinitionallyEqual program context left right := by
  unfold Holds PredicateSemantics.PredicateAlgebra.Holds
  rw [eval_canonical,eval_canonical,ofTerm_eq]

end DefinitionalQuotient

theorem DefinitionallyEqual.rowDuplicate {program : Program} {context : Context} {left right : Term}
    {rest tails : List Term} (equal : DefinitionallyEqual program context left right) :
    DefinitionallyEqual program context (.row (left :: right :: rest) tails) (.row (left :: rest) tails) := by
  apply DefinitionallyEqual.trans (middle := .row (left :: left :: rest) tails)
  · apply DefinitionallyEqual.congr
    · rfl
    · exact (ListRel.cons .refl (.cons equal.symm (.reflexive (fun _ => .refl) rest))).append (.reflexive (fun _ => .refl) tails)
  · exact .row (.duplicate .refl)

theorem DefinitionallyEqual.tailDuplicate {program : Program} {context : Context} {left right : Term}
    {instances tails : List Term} (equal : DefinitionallyEqual program context left right) :
    DefinitionallyEqual program context (.row instances (left :: right :: tails)) (.row instances (left :: tails)) := by
  apply DefinitionallyEqual.trans (middle := .row instances (left :: left :: tails))
  · apply DefinitionallyEqual.congr
    · rfl
    · exact (ListRel.reflexive (fun _ => DefinitionallyEqual.refl (program := program) (context := context)) instances).append
        (.cons .refl (.cons equal.symm (.reflexive (fun _ => .refl) tails)))
  · exact .row (.tailDuplicate .refl)

/-- No lexical equality or universal predicate assumption is available in
this judgment. The concrete definitional quotient interprets every actual
logical constructor, including hygienic quantified instantiation. -/
theorem Equal.closed_definitional {program : Program} {context : Context} {left right : Term}
    (equal : Equal program context left right) (closed : context.assumptions = []) :
    DefinitionallyEqual program context left right := by
  apply Equal.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun context left right _ => context.assumptions = [] → DefinitionallyEqual program context left right)
    (motive_4 := fun _ _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ => True)
    (motive_8 := fun context constraint _ => context.assumptions = [] → DefinitionalQuotient.Holds program context constraint)
    (motive_9 := fun context substitution constraint _ => context.assumptions = [] →
      DefinitionalQuotient.Holds program context (constraint.substitute substitution))
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
  all_goals try contradiction
  all_goals try { assumption }
  all_goals try { exact DefinitionalQuotient.holds_equal.mpr (by assumption) }
  all_goals try {
    rename_i member closed
    rw [closed] at member
    exact False.elim (List.not_mem_nil member) }
  case refl => exact .refl
  case symm _ _ _ _ ih closed => exact (ih closed).symm
  case trans _ _ _ _ _ _ first second closed => exact (first closed).trans (second closed)
  case congrChildren _ _ _ same _ children closed =>
    exact .congrChildren same (fun index first second leftAt rightAt => children index first second leftAt rightAt closed)
  case entailed _ _ _ _ ih closed => exact DefinitionalQuotient.holds_equal.mp (ih closed)
  case rowDuplicate _ _ _ _ _ _ ih closed => exact (ih closed).rowDuplicate
  case tailDuplicate _ _ _ _ _ _ ih closed => exact (ih closed).tailDuplicate
  case checkedCallable => simp only [DefinitionalQuotient.Holds,PredicateSemantics.PredicateAlgebra.Holds,DefinitionalQuotient.algebra]
  case checkedRunsIn => simp only [DefinitionalQuotient.Holds,PredicateSemantics.PredicateAlgebra.Holds,DefinitionalQuotient.algebra]
  case congrSubstitution context _ _ _ _ _ _ before after _ equal held closed =>
    exact ((DefinitionalQuotient.algebra program context).holds_substitution_congr program context
      DefinitionalQuotient.canonical DefinitionalQuotient.canonical
      (fun id kind => by
        rw [DefinitionalQuotient.eval_canonical,DefinitionalQuotient.eval_canonical]
        exact DefinitionalQuotient.ofTerm_eq.mpr (equal id kind closed)) before after).mp (held closed)
  case equality _ _ _ _ ih closed => exact DefinitionalQuotient.holds_equal.mpr (ih closed)
  case outlivesRefl => simp only [DefinitionalQuotient.Holds,PredicateSemantics.PredicateAlgebra.Holds,DefinitionalQuotient.algebra]
  case outlivesStatic => simp only [DefinitionalQuotient.Holds,PredicateSemantics.PredicateAlgebra.Holds,DefinitionalQuotient.algebra]
  case outlivesTrans => simp only [DefinitionalQuotient.Holds,PredicateSemantics.PredicateAlgebra.Holds,DefinitionalQuotient.algebra]
  case typeOutlives => simp only [DefinitionalQuotient.Holds,PredicateSemantics.PredicateAlgebra.Holds,DefinitionalQuotient.algebra]
  case rows => simp only [DefinitionalQuotient.Holds,PredicateSemantics.PredicateAlgebra.Holds,DefinitionalQuotient.algebra]
  case implementation => simp only [DefinitionalQuotient.Holds,PredicateSemantics.PredicateAlgebra.Holds,DefinitionalQuotient.algebra]
  case use => simp only [DefinitionalQuotient.Holds,PredicateSemantics.PredicateAlgebra.Holds,DefinitionalQuotient.algebra]
  case quantified context _ _ _ instances closed =>
    exact (DefinitionalQuotient.algebra program context).holds_quantified program context DefinitionalQuotient.canonical
      (fun values substitution instantiated kinded requirement member =>
        instances values substitution instantiated kinded requirement member closed)
  case quantifiedInstance context _ _ _ _ _ _ _ instantiated kinded member graph held closed =>
    exact (DefinitionalQuotient.algebra program context).holds_quantifiedInstance program context DefinitionalQuotient.canonical
      (held closed) instantiated kinded member graph
  case instantiated _ _ _ _ graph _ held closed =>
    rw [← graph.2]
    exact held closed

theorem Equal.closed_iff_definitional {program : Program} {context : Context} {left right : Term}
    (closed : context.assumptions = []) :
    Equal program context left right ↔ DefinitionallyEqual program context left right :=
  ⟨fun equal => equal.closed_definitional closed,Equal.definitional⟩

theorem Entails.closed_definitional_equal {program : Program} {context : Context} {left right : Term}
    (held : Entails program context (.equal left right)) (closed : context.assumptions = []) :
    DefinitionallyEqual program context left right :=
  (Equal.entailed held).closed_definitional closed

end Glorious.Language
