import GloriousLanguage.HeadInference

/-! Constructive coherence of actual declared reductions. This module does not
infer global confluence from local peaks or assume normalization terminates. -/
namespace Glorious.Language

theorem ListRel.transitive {α : Type} {relation : α → α → Prop}
    (transitive : ∀ a b c, relation a b → relation b c → relation a c)
    {first middle last : List α} (left : ListRel relation first middle) (right : ListRel relation middle last) :
    ListRel relation first last := by
  induction left generalizing last with
  | nil => cases right; exact .nil
  | cons head _ ih =>
    cases right with
    | cons other tail => exact .cons (transitive _ _ _ head other) (ih tail)

/-- A declaration's actual instantiated head is always a matching witness,
including opaque associated terms. Source kinding supplies every checked
substitution edge; no argument-normalization algorithm is involved. -/
theorem MatchesImplHead.instantiated {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {implementation : ImplDefinition} {values : List Term} {substitution : Substitution}
    (declared : Definition.implementation implementation ∈ program.declarations)
    (instantiated : Instantiates implementation.generics values substitution)
    (valuesKinded : ∀ value ∈ values, Kinding program context value value.kind)
    (inferred : ∀ (index : Nat) binder value, implementation.generics[index]? = some binder → values[index]? = some value →
      InfersHeadArgument program context implementation (implementation.arguments.map (Term.substitute substitution)) binder value) :
    MatchesImplHead program context implementation (implementation.arguments.map (Term.substitute substitution)) substitution := by
  have declaration := (valid.2.2.2.2.1 _ declared).2.1
  obtain ⟨_,trait,_,_,_,_,_,signature,_⟩ := declaration
  obtain ⟨_,_,ownerSub,_,headKinded,_,_⟩ := signature
  refine .matched (specialized := implementation.arguments.map (Term.substitute substitution)) instantiated valuesKinded ?_ ?_ inferred
  · simpa only [List.map_id] using
      (ListRel.maps implementation.arguments id (Term.substitute substitution) (by
        intro argument member
        exact ((headKinded argument member).1.instantiate instantiated valuesKinded (Nat.zero_le _)
          (fun _ present => False.elim (List.not_mem_nil present))
          (fun _ present => False.elim (List.not_mem_nil present))).2))
  · simpa only [List.map_id] using
      (ListRel.maps (implementation.arguments.map (Term.substitute substitution)) id id (fun _ _ =>
        DefinitionallyEqual.refl (program := program) (context := context)))

theorem SelectsImpl.instantiated_head {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {implementation : ImplDefinition} {values : List Term} {substitution : Substitution}
    (declared : Definition.implementation implementation ∈ program.declarations)
    (instantiated : Instantiates implementation.generics values substitution)
    (valuesKinded : ∀ value ∈ values, Kinding program context value value.kind)
    (inferred : ∀ (index : Nat) binder value, implementation.generics[index]? = some binder → values[index]? = some value →
      InfersHeadArgument program context implementation (implementation.arguments.map (Term.substitute substitution)) binder value)
    (requirements : ∀ requirement ∈ implementation.requirements, EntailsSubstitution program context substitution requirement) :
    SelectsImpl program context implementation.trait (implementation.arguments.map (Term.substitute substitution))
      implementation.negative implementation substitution :=
  .selected declared rfl rfl (.instantiated valid declared instantiated valuesKinded inferred) requirements

theorem MatchesImplHead.congr_query {program : Program} {context : Context} {implementation : ImplDefinition}
    {first second : List Term} {substitution : Substitution}
    (matched : MatchesImplHead program context implementation first substitution)
    (equal : ListRel (DefinitionallyEqual program context) first second) :
    MatchesImplHead program context implementation second substitution := by
  cases matched with
  | inferred instantiated kinded specialized lengths head inferred =>
    exact .matched instantiated kinded specialized
      (ListRel.transitive (relation := DefinitionallyEqual program context)
        (fun _ _ _ first second => DefinitionallyEqual.trans first second) (ListRel.of_at lengths head) equal)
      (fun index binder value sourceAt valueAt => (inferred index binder value sourceAt valueAt).congr_query equal)

/-- Alias/row/associated convertibility transports the existing selection and
its requirements without changing inferred source arguments or consulting
logical assumed equality. -/
theorem SelectsImpl.congr_query {program : Program} {context : Context} {trait : DeclId} {first second : List Term}
    {negative : Bool} {implementation : ImplDefinition} {substitution : Substitution}
    (selected : SelectsImpl program context trait first negative implementation substitution)
    (equal : ListRel (DefinitionallyEqual program context) first second) :
    SelectsImpl program context trait second negative implementation substitution := by
  cases selected with
  | selected member trait negative matched requirements =>
    exact .selected member trait negative (matched.congr_query equal) requirements

theorem SelectsImpl.convertible_unique {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {trait : DeclId} {firstArguments secondArguments : List Term}
    {firstNegative secondNegative : Bool} {first second : ImplDefinition} {firstSub secondSub : Substitution}
    (left : SelectsImpl program context trait firstArguments firstNegative first firstSub)
    (right : SelectsImpl program context trait secondArguments secondNegative second secondSub)
    (equal : ListRel (DefinitionallyEqual program context) firstArguments secondArguments) :
    first = second ∧ SubstitutionsConvertible program context firstSub secondSub :=
  (left.congr_query equal).unique valid right

theorem Term.substitutions_reduce (program : Program) (context : Context) (term : Term)
    {left right : Substitution}
    (agree : ∀ id kind, DefinitionalReduction program context ((left.get id).getD (.parameter id kind))
      ((right.get id).getD (.parameter id kind))) :
    DefinitionalReduction program context (term.substitute left) (term.substitute right) :=
  term.substitutions_related DefinitionalReduction.congr agree

theorem SubstitutionsJoinable.common {program : Program} {context : Context} {left right : Substitution}
    (joinable : SubstitutionsJoinable program context left right) :
    ∃ common : Substitution,
      (∀ id kind, DefinitionalReduction program context ((left.get id).getD (.parameter id kind))
        ((common.get id).getD (.parameter id kind))) ∧
      (∀ id kind, DefinitionalReduction program context ((right.get id).getD (.parameter id kind))
        ((common.get id).getD (.parameter id kind))) := by
  induction joinable with
  | nil => exact ⟨[],fun _ _ => .refl,fun _ _ => .refl⟩
  | @cons first second left right head _ ih =>
    rcases first with ⟨key,first⟩
    rcases second with ⟨otherKey,second⟩
    obtain ⟨same,value,firstReduces,secondReduces⟩ := head
    simp only at same firstReduces secondReduces
    subst otherKey
    obtain ⟨common,leftReduces,rightReduces⟩ := ih
    refine ⟨(key,value) :: common,?_,?_⟩
    · intro id kind
      by_cases found : key = id
      · simpa [Table.get,found] using firstReduces
      · simpa [Table.get,found] using leftReduces id kind
    · intro id kind
      by_cases found : key = id
      · simpa [Table.get,found] using secondReduces
      · simpa [Table.get,found] using rightReduces id kind

theorem SubstitutionsJoinable.refl (program : Program) (context : Context) (substitution : Substitution) :
    SubstitutionsJoinable program context substitution substitution := by
  induction substitution with
  | nil => exact .nil
  | cons entry rest ih => exact .cons ⟨rfl,entry.2,.refl,.refl⟩ ih

theorem SubstitutionsJoinable.append {program : Program} {context : Context}
    {firstLeft firstRight secondLeft secondRight : Substitution}
    (first : SubstitutionsJoinable program context firstLeft firstRight)
    (second : SubstitutionsJoinable program context secondLeft secondRight) :
    SubstitutionsJoinable program context (firstLeft ++ secondLeft) (firstRight ++ secondRight) :=
  ListRel.append first second

theorem SubstitutionsJoinable.substitute {program : Program} {context : Context} {left right : Substitution}
    (joinable : SubstitutionsJoinable program context left right) (term : Term) :
    DefinitionallyJoinable program context (term.substitute left) (term.substitute right) := by
  obtain ⟨common,first,second⟩ := joinable.common
  exact ⟨term.substitute common,term.substitutions_reduce program context first,
    term.substitutions_reduce program context second⟩

end Glorious.Language
