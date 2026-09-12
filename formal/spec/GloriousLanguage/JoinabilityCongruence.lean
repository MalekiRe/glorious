import GloriousLanguage.ConstructorReduction

/-! Positive joins compose through the existing ordered child projection.
Rebuilding preserves every actual constructor annotation and argument-group
boundary; repeated equal source children are still distinct positions. -/
namespace Glorious.Language

private theorem List.constant_map_of_length {α β : Type} (value : β) {left right : List α}
    (lengths : left.length = right.length) : left.map (fun _ => value) = right.map (fun _ => value) := by
  induction left generalizing right with
  | nil =>
    have empty := List.eq_nil_of_length_eq_zero lengths.symm
    subst right
    rfl
  | cons first left ih =>
    cases right with
    | nil => simp at lengths
    | cons second right => exact congrArg (List.cons value) (ih (Nat.succ.inj lengths))

private theorem List.head_tail_of_length {α : Type} {values : List α} {length : Nat}
    (sized : values.length = length + 1) :
    ∃ head tail, values = head :: tail ∧ tail.length = length := by
  cases values with
  | nil => simp at sized
  | cons head tail => exact ⟨head,tail,rfl,Nat.succ.inj sized⟩

private theorem List.repartition_constant_maps {left right replacement : List Term}
    (sized : replacement.length = (left ++ right).length) :
    left.map (fun _ => Term.unit) = (replacement.take left.length).map (fun _ => Term.unit) ∧
    right.map (fun _ => Term.unit) = (replacement.drop left.length).map (fun _ => Term.unit) := by
  have enough : left.length ≤ replacement.length := by rw [sized,List.length_append]; omega
  constructor
  · apply List.constant_map_of_length
    rw [List.length_take,Nat.min_eq_left enough]
  · apply List.constant_map_of_length
    rw [List.length_drop,sized,List.length_append]
    omega

/-- Any replacement list of exactly the authoritative child arity can be
realized with the same head. No source operand is conflated with another
position merely because their original terms are equal. -/
theorem Term.children_realizable (term : Term) (replacement : List Term)
    (sized : replacement.length = term.children.length) :
    ∃ rebuilt, SameHead term rebuilt ∧ rebuilt.children = replacement := by
  cases term <;> simp only [Term.children,List.length_cons,List.length_nil] at sized
  all_goals try {
    have empty := List.eq_nil_of_length_eq_zero sized
    subst replacement
    exact ⟨_,rfl,rfl⟩ }
  case tuple fields =>
    exact ⟨.tuple replacement,congrArg Term.tuple (List.constant_map_of_length Term.unit sized.symm),rfl⟩
  case nominal id arguments =>
    exact ⟨.nominal id replacement,congrArg (Term.nominal id) (List.constant_map_of_length Term.unit sized.symm),rfl⟩
  case alias id arguments =>
    exact ⟨.alias id replacement,congrArg (Term.alias id) (List.constant_map_of_length Term.unit sized.symm),rfl⟩
  case callable id arguments =>
    exact ⟨.callable id replacement,congrArg (Term.callable id) (List.constant_map_of_length Term.unit sized.symm),rfl⟩
  case effect id arguments =>
    exact ⟨.effect id replacement,congrArg (Term.effect id) (List.constant_map_of_length Term.unit sized.symm),rfl⟩
  case constantTuple fields =>
    exact ⟨.constantTuple replacement,congrArg Term.constantTuple (List.constant_map_of_length Term.unit sized.symm),rfl⟩
  case rawPointer mode referent =>
    obtain ⟨first,rest,rfl,restLength⟩ := List.head_tail_of_length sized
    have empty := List.eq_nil_of_length_eq_zero restLength
    subst rest
    exact ⟨.rawPointer mode first,rfl,rfl⟩
  case array element length =>
    obtain ⟨first,tail1,rfl,length1⟩ := List.head_tail_of_length sized
    obtain ⟨second,tail2,rfl,length2⟩ := List.head_tail_of_length length1
    have empty := List.eq_nil_of_length_eq_zero length2
    subst tail2
    exact ⟨.array first second,rfl,rfl⟩
  case reference mode region referent =>
    obtain ⟨first,tail1,rfl,length1⟩ := List.head_tail_of_length sized
    obtain ⟨second,tail2,rfl,length2⟩ := List.head_tail_of_length length1
    have empty := List.eq_nil_of_length_eq_zero length2
    subst tail2
    exact ⟨.reference mode first second,rfl,rfl⟩
  case label brand region result =>
    obtain ⟨first,tail1,rfl,length1⟩ := List.head_tail_of_length sized
    obtain ⟨second,tail2,rfl,length2⟩ := List.head_tail_of_length length1
    obtain ⟨third,tail3,rfl,length3⟩ := List.head_tail_of_length length2
    have empty := List.eq_nil_of_length_eq_zero length3
    subst tail3
    exact ⟨.label first second third,rfl,rfl⟩
  case continuation brand argument answer effects quantity =>
    obtain ⟨first,tail1,rfl,length1⟩ := List.head_tail_of_length sized
    obtain ⟨second,tail2,rfl,length2⟩ := List.head_tail_of_length length1
    obtain ⟨third,tail3,rfl,length3⟩ := List.head_tail_of_length length2
    obtain ⟨fourth,tail4,rfl,length4⟩ := List.head_tail_of_length length3
    have empty := List.eq_nil_of_length_eq_zero length4
    subst tail4
    exact ⟨.continuation first second third fourth quantity,rfl,rfl⟩
  case environment brand region residents =>
    obtain ⟨first,tail1,rfl,length1⟩ := List.head_tail_of_length sized
    obtain ⟨second,rest,rfl,length2⟩ := List.head_tail_of_length length1
    refine ⟨.environment first second rest,?_,rfl⟩
    exact congrArg (Term.environment .unit .unit) (List.constant_map_of_length Term.unit length2.symm)
  case available brand region residents =>
    obtain ⟨first,tail1,rfl,length1⟩ := List.head_tail_of_length sized
    obtain ⟨second,rest,rfl,length2⟩ := List.head_tail_of_length length1
    refine ⟨.available first second rest,?_,rfl⟩
    exact congrArg (Term.available .unit .unit) (List.constant_map_of_length Term.unit length2.symm)
  case bindings brand region arguments =>
    obtain ⟨first,tail1,rfl,length1⟩ := List.head_tail_of_length sized
    obtain ⟨second,rest,rfl,length2⟩ := List.head_tail_of_length length1
    refine ⟨.bindings first second rest,?_,rfl⟩
    exact congrArg (Term.bindings .unit .unit) (List.constant_map_of_length Term.unit length2.symm)
  case row instances tails =>
    refine ⟨.row (replacement.take instances.length) (replacement.drop instances.length),?_,?_⟩
    · simpa only [SameHead,Term.mapChildren,Term.row.injEq] using List.repartition_constant_maps sized
    · exact List.take_append_drop _ replacement
  case projection trait member owners items kind =>
    refine ⟨.projection trait member (replacement.take owners.length) (replacement.drop owners.length) kind,?_,?_⟩
    · simpa only [SameHead,Term.mapChildren,Term.projection.injEq,true_and,and_true] using
        List.repartition_constant_maps sized
    · exact List.take_append_drop _ replacement
  case constantConstructor id arguments fields =>
    refine ⟨.constantConstructor id (replacement.take arguments.length) (replacement.drop arguments.length),?_,?_⟩
    · simpa only [SameHead,Term.mapChildren,Term.constantConstructor.injEq,true_and] using
        List.repartition_constant_maps sized
    · exact List.take_append_drop _ replacement

theorem ListRel.common {program : Program} {context : Context} {left right : List Term}
    (joined : ListRel (DefinitionallyJoinable program context) left right) :
    ∃ common, ListRel (DefinitionalReduction program context) left common ∧
      ListRel (DefinitionalReduction program context) right common := by
  induction joined with
  | nil => exact ⟨[],.nil,.nil⟩
  | cons head _ tail =>
    obtain ⟨common,left,right⟩ := head
    obtain ⟨rest,leftRest,rightRest⟩ := tail
    exact ⟨common :: rest,.cons left leftRest,.cons right rightRest⟩

/-- Positive common-reduct witnesses compose at every actual term constructor,
including aliases/projections with separately ordered owner and GAT arguments. -/
theorem DefinitionallyJoinable.congr {program : Program} {context : Context} {left right : Term}
    (same : SameHead left right)
    (children : ListRel (DefinitionallyJoinable program context) left.children right.children) :
    DefinitionallyJoinable program context left right := by
  obtain ⟨common,leftChildren,rightChildren⟩ := children.common
  obtain ⟨rebuilt,leftHead,rebuildChildren⟩ := left.children_realizable common leftChildren.length_eq.symm
  refine ⟨rebuilt,.congr leftHead ?_,.congr (same.symm.trans leftHead) ?_⟩
  · rw [rebuildChildren]; exact leftChildren
  · rw [rebuildChildren]; exact rightChildren

/-- Constructor-headed joining has an exact compositional characterization,
not just a one-directional preservation fact. -/
theorem DefinitionallyJoinable.structural_iff {program : Program} {context : Context} {left right : Term}
    (leftStructural : left.StructuralHead) (rightStructural : right.StructuralHead) :
    DefinitionallyJoinable program context left right ↔ SameHead left right ∧
      ListRel (DefinitionallyJoinable program context) left.children right.children :=
  ⟨fun joined => joined.structural_decomposition leftStructural rightStructural,
    fun ⟨same,children⟩ => .congr same children⟩

private theorem ListRel.join_peaks {program : Program} {context : Context} {source left right : List Term}
    (first : ListRel (DefinitionalReduction program context) source left)
    (second : ListRel (DefinitionalReduction program context) source right)
    (join : ∀ term ∈ source, ∀ left right, DefinitionalReduction program context term left →
      DefinitionalReduction program context term right → DefinitionallyJoinable program context left right) :
    ListRel (DefinitionallyJoinable program context) left right := by
  induction first generalizing right with
  | nil => cases second; exact .nil
  | cons head _ tail =>
    cases second with
    | cons other remaining =>
      exact .cons (join _ List.mem_cons_self _ _ head other)
        (tail remaining (fun term present => join term (List.mem_cons_of_mem _ present)))

/-- The entire structural-constructor confluence boundary is compositional:
arbitrary reduction paths from the parent join whenever arbitrary paths from
its actual children join. Only the proper child obligations are assumed. -/
theorem DefinitionalReduction.structural_join {program : Program} {context : Context} {source left right : Term}
    (structural : source.StructuralHead)
    (childrenJoin : ∀ child ∈ source.children, ∀ first second,
      DefinitionalReduction program context child first → DefinitionalReduction program context child second →
        DefinitionallyJoinable program context first second)
    (first : DefinitionalReduction program context source left)
    (second : DefinitionalReduction program context source right) :
    DefinitionallyJoinable program context left right := by
  obtain ⟨firstHead,firstChildren⟩ := first.structural_decomposition structural
  obtain ⟨secondHead,secondChildren⟩ := second.structural_decomposition structural
  exact .congr (firstHead.symm.trans secondHead) (firstChildren.join_peaks secondChildren childrenJoin)

end Glorious.Language
