import GloriousLanguage.JoinabilityCongruence
import GloriousLanguage.PredicateInterpretation

/-! A constructor-congruent quotient supplies the shared predicate algebra.
The node is built from actual ordered children; its arbitrary arity-mismatch
value is never used by evaluation, whose child arity is proved exactly. -/
namespace Glorious.Language.PredicateSemantics.TermQuotient

abbrev Class (setoid : Setoid Term) := Quotient setoid

def ofTerm {setoid : Setoid Term} (term : Term) : Class setoid := Quotient.mk _ term

theorem ofTerm_eq {setoid : Setoid Term} {left right : Term} :
    (ofTerm left : Class setoid) = ofTerm right ↔ setoid.r left right :=
  ⟨Quotient.exact,Quotient.sound⟩

private theorem represented {setoid : Setoid Term} (value : Class setoid) :
    ∃ term, ofTerm term = value := by
  induction value using Quotient.ind with
  | _ term => exact ⟨term,rfl⟩

noncomputable def representative {setoid : Setoid Term} (value : Class setoid) : Term :=
  Classical.choose (represented value)

theorem representative_eq {setoid : Setoid Term} (value : Class setoid) :
    ofTerm (representative value) = value := Classical.choose_spec (represented value)

noncomputable def rebuild (head : Term) (children : List Term) (lengths : children.length = head.children.length) : Term :=
  Classical.choose (head.children_realizable children lengths)

theorem rebuild_spec (head : Term) (children : List Term) (lengths : children.length = head.children.length) :
    SameHead head (rebuild head children lengths) ∧ (rebuild head children lengths).children = children :=
  Classical.choose_spec (head.children_realizable children lengths)

noncomputable def node {setoid : Setoid Term} (head : Term) (children : List (Class setoid)) : Class setoid :=
  if lengths : children.length = head.children.length then
    ofTerm (rebuild head (children.map representative) (by simpa only [List.length_map] using lengths))
  else ofTerm .unit

theorem node_spec {setoid : Setoid Term} (head : Term) (children : List (Class setoid))
    (lengths : children.length = head.children.length) :
    ∃ rebuilt, SameHead head rebuilt ∧ rebuilt.children = children.map representative ∧ node head children = ofTerm rebuilt := by
  unfold node
  rw [dif_pos lengths]
  exact ⟨_,(rebuild_spec _ _ _).1,(rebuild_spec _ _ _).2,rfl⟩

theorem node_sameHead {setoid : Setoid Term}
    (congruent : ∀ {left right}, SameHead left right → ListRel setoid.r left.children right.children → setoid.r left right)
    {left right : Term} (same : SameHead left right) (children : List (Class setoid)) :
    node left children = node right children := by
  by_cases lengths : children.length = left.children.length
  · obtain ⟨first,firstHead,firstChildren,firstNode⟩ := node_spec left children lengths
    obtain ⟨second,secondHead,secondChildren,secondNode⟩ := node_spec right children (lengths.trans same.children_length)
    rw [firstNode,secondNode]
    apply ofTerm_eq.mpr
    apply congruent (firstHead.symm.trans (same.trans secondHead))
    rw [firstChildren,secondChildren]
    exact .reflexive setoid.refl _
  · have otherLengths : children.length ≠ right.children.length := by rw [← same.children_length]; exact lengths
    simp only [node,dif_neg lengths,dif_neg otherLengths]

noncomputable def algebra (setoid : Setoid Term)
    (congruent : ∀ {left right}, SameHead left right → ListRel setoid.r left.children right.children → setoid.r left right) :
    PredicateAlgebra (Class setoid) where
  node := node
  sameHead := node_sameHead congruent
  outlives := fun _ _ => True
  typeOutlives := fun _ _ => True
  rows := fun _ _ => True
  implements := fun _ _ _ => True
  use := fun _ _ => True
  callable := fun _ _ _ _ _ => True
  runsIn := fun _ _ _ _ _ => True

def canonical {setoid : Setoid Term} : Valuation (Class setoid) := fun id kind => ofTerm (.parameter id kind)

theorem eval_canonical {setoid : Setoid Term}
    (congruent : ∀ {left right}, SameHead left right → ListRel setoid.r left.children right.children → setoid.r left right)
    (term : Term) : (algebra setoid congruent).eval canonical term = ofTerm term := by
  by_cases parameter : ∃ id kind, term = .parameter id kind
  · obtain ⟨id,kind,rfl⟩ := parameter
    exact TermAlgebra.eval_parameter _ _ _ _
  · have notParameter : ∀ id kind, term ≠ .parameter id kind := fun id kind equal => parameter ⟨id,kind,equal⟩
    rw [TermAlgebra.eval_node _ _ notParameter]
    have children : term.children.map ((algebra setoid congruent).eval canonical) = term.children.map ofTerm := by
      apply List.map_congr_left
      intro child _
      exact eval_canonical congruent child
    rw [children]
    obtain ⟨rebuilt,same,reconstructed,node⟩ := node_spec term (term.children.map (ofTerm (setoid := setoid))) (by simp)
    change TermQuotient.node term (term.children.map ofTerm) = ofTerm term
    rw [node]
    apply ofTerm_eq.mpr
    apply congruent same.symm
    rw [reconstructed,List.map_map]
    simpa only [List.map_id,Function.comp_def] using ListRel.maps term.children (fun term => representative (ofTerm term)) id (by
      intro child _
      exact ofTerm_eq.mp (representative_eq (ofTerm child)))
termination_by term
decreasing_by exact Term.child_sizeOf ‹_ ∈ term.children›

end Glorious.Language.PredicateSemantics.TermQuotient
