import GloriousLanguage.ProjectionKinding

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
    (valuesKinded : ∀ value ∈ values, Kinding program context value value.kind) :
    MatchesImplHead program context implementation (implementation.arguments.map (Term.substitute substitution)) substitution := by
  have declaration := (valid.2.2.2.2.1 _ declared).2.1
  obtain ⟨_,trait,_,_,_,_,_,signature⟩ := declaration
  obtain ⟨_,ownerSub,_,headKinded,_,_⟩ := signature
  refine .matched (specialized := implementation.arguments.map (Term.substitute substitution)) instantiated valuesKinded ?_ ?_
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
    (requirements : ∀ requirement ∈ implementation.requirements, EntailsSubstitution program context substitution requirement) :
    SelectsImpl program context implementation.trait (implementation.arguments.map (Term.substitute substitution))
      implementation.negative implementation substitution :=
  .selected declared rfl rfl (.instantiated valid declared instantiated valuesKinded) requirements

theorem MatchesImplHead.congr_query {program : Program} {context : Context} {implementation : ImplDefinition}
    {first second : List Term} {substitution : Substitution}
    (matched : MatchesImplHead program context implementation first substitution)
    (equal : ListRel (DefinitionallyEqual program context) first second) :
    MatchesImplHead program context implementation second substitution := by
  cases matched with
  | matched instantiated kinded specialized head =>
    exact .matched instantiated kinded specialized
      (ListRel.transitive (relation := DefinitionallyEqual program context)
        (fun _ _ _ first second => DefinitionallyEqual.trans first second) head equal)

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
    first = second ∧ SubstitutionsJoinable program context firstSub secondSub :=
  (left.congr_query equal).unique valid right

theorem Term.substitutions_reduce (program : Program) (context : Context) (term : Term)
    {left right : Substitution}
    (agree : ∀ id kind, DefinitionalReduction program context ((left.get id).getD (.parameter id kind))
      ((right.get id).getD (.parameter id kind))) :
    DefinitionalReduction program context (term.substitute left) (term.substitute right) := by
  cases term
  case parameter id kind => simpa only [Term.substitute] using agree id kind
  all_goals apply DefinitionalReduction.congr
  all_goals first
    | simp only [SameHead,Term.substitute,Term.mapChildren,List.map_map,Function.comp_def]
    | skip
  all_goals simp only [Term.children]
  all_goals first
    | exact .nil
    | apply ListRel.maps; intro child _; exact child.substitutions_reduce program context agree
    | apply ListRel.append
      all_goals apply ListRel.maps; intro child _; exact child.substitutions_reduce program context agree
    | repeat' apply ListRel.cons
      all_goals first
        | exact .nil
        | exact Term.substitutions_reduce program context _ agree
        | apply ListRel.maps; intro child _; exact child.substitutions_reduce program context agree
termination_by term

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

/-- Common redexes select the same declaration and join their inferred
arguments. Simultaneous substitution transports those witnesses to the actual
associated body; no associated-result equality is an admission premise. -/
theorem DefinitionalStep.root_joinable {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {term first second : Term}
    (left : DefinitionalStep program context term first) (right : DefinitionalStep program context term second) :
    DefinitionallyJoinable program context first second := by
  cases left with
  | alias found instantiated _ substituted =>
    cases right with
    | alias otherFound otherInstance _ otherSubstitution =>
      have sameDeclaration := Option.some.inj (found.symm.trans otherFound)
      subst_vars
      have sameSubstitution := instantiated.2.2.trans otherInstance.2.2.symm
      subst_vars
      have sameResult := substituted.2.1.trans otherSubstitution.2.1.symm
      subst_vars
      exact ⟨_,.refl,.refl⟩
  | @projection trait member owners items associated ownerSub itemSub implementation implSub body value
      domain selected memberBody substituted =>
    generalize kindEquality : associated.kind = projectionKind at right
    cases right with
    | projection otherDomain otherSelected otherMember otherSubstitution =>
      obtain ⟨rfl,rfl,rfl⟩ := domain.unique otherDomain
      obtain ⟨rfl,arguments⟩ := selected.unique valid otherSelected
      have sameBody := List.pair_value_unique (valid.associated_members_unique selected.declaration) memberBody otherMember
      subst_vars
      rw [substituted.2.1,otherSubstitution.2.1]
      exact (arguments.append (.refl program context itemSub)).substitute _
    | defaultProjection otherDomain otherSelected missing _ _ =>
      obtain ⟨rfl,rfl,rfl⟩ := domain.unique otherDomain
      obtain ⟨rfl,_⟩ := selected.unique valid otherSelected
      exact False.elim (missing _ memberBody)
  | @defaultProjection trait member owners items associated ownerSub itemSub implementation implSub body value
      domain selected missing default substituted =>
    generalize kindEquality : associated.kind = projectionKind at right
    cases right with
    | projection otherDomain otherSelected otherMember _ =>
      obtain ⟨rfl,rfl,rfl⟩ := domain.unique otherDomain
      obtain ⟨rfl,_⟩ := selected.unique valid otherSelected
      exact False.elim (missing _ otherMember)
    | defaultProjection otherDomain _ _ otherDefault otherSubstitution =>
      obtain ⟨rfl,rfl,rfl⟩ := domain.unique otherDomain
      have sameBody := Option.some.inj (default.symm.trans otherDefault)
      subst_vars
      have sameResult := substituted.2.1.trans otherSubstitution.2.1.symm
      subst_vars
      exact ⟨_,.refl,.refl⟩

end Glorious.Language
