import GloriousLanguage.BinderDefaults
import GloriousLanguage.UniverseTransport
import GloriousLanguage.LogicalKinding

/-! Every term in the authoritative declaration projection inherits kinding
from its actual source admission. Generic defaults retain ordered scope;
constant constructors retain their actual admitted generic arguments. -/
namespace Glorious.Language

theorem ScalarValue.Valid.type_valid {target : TargetProfile} {value : ScalarValue}
    (valid : value.Valid target) : value.type.Valid target := by
  cases value with
  | integer => exact valid.1
  | floating => exact True.intro
  | character => exact True.intro

/-- Constant typing is not permission to smuggle an unkinded generic
argument into a published source value. Logical result conversion consumes
the actual admitted equality-preservation theorem. -/
theorem ConstantType.kinding {program : Program} (valid : ProgramWellFormed program) {context : Context}
    (assumptions : ∀ constraint ∈ context.assumptions, ConstraintKinded program context constraint)
    {value type : Term} (typed : ConstantType program context value type) :
    Kinding program context value .constant ∧ Kinding program context type .type := by
  refine ConstantType.rec
    (motive_1 := fun value type _ => Kinding program context value .constant ∧ Kinding program context type .type)
    (motive_2 := fun values types _ => ListRel (fun value type =>
      Kinding program context value .constant ∧ Kinding program context type .type) values types)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
  · intro value admitted
    exact ⟨.scalarConstant admitted,.scalar admitted.type_valid⟩
  · exact ⟨.tupleConstant (by simp),.unit⟩
  · intro fields types _ checked
    constructor
    · apply Kinding.tupleConstant
      intro field member
      obtain ⟨_,_,kinded⟩ := checked.member_left member
      exact kinded.1
    · apply Kinding.tuple
      intro type member
      obtain ⟨_,_,kinded⟩ := checked.swap.member_left member
      exact kinded.2
  · intro constructor data variant arguments values substitution types found instantiated argumentsKinded graph typed checked
    refine ⟨.constructorConstant found instantiated argumentsKinded ?_ ?_,.nominal found.1 instantiated argumentsKinded⟩
    · simpa only [List.length_map] using typed.length_eq.trans graph.length_eq.symm
    · intro value member
      obtain ⟨_,_,kinded⟩ := checked.member_left member
      exact kinded.1
  · intro value before after _ equal checked
    exact ⟨checked.1,(equal.kinding_iff valid assumptions .type).mp checked.2⟩
  · exact .nil
  · intro value type values types _ _ checked rest
    exact .cons checked rest

private theorem Kinding.source_term {program : Program} {context : Context} {term : Term} {kind : Kind}
    (kinded : Kinding program context term kind) (level : context.universeLevel = 0) :
    ∃ actual, actual.universeLevel = 0 ∧ Kinding program actual term term.kind :=
  ⟨context,level,by simpa only [kinded.term_kind] using kinded⟩

private theorem ConstraintKinded.source_terms {program : Program} {context : Context} {constraint : Constraint}
    (kinded : ConstraintKinded program context constraint) (level : context.universeLevel = 0) :
    ∀ term ∈ constraint.terms, ∃ actual, actual.universeLevel = 0 ∧ Kinding program actual term term.kind := by
  intro term member
  obtain ⟨binders,checked⟩ := kinded.terms_kinded term member
  exact checked.source_term level

private theorem BinderDefaultsKinded.source_terms {program : Program} {context : Context} {binders : List Binder}
    (defaults : BinderDefaultsKinded program context binders) (level : context.universeLevel = 0) :
    ∀ term ∈ binders.flatMap (fun binder => binder.defaultValue.toList),
      ∃ actual, actual.universeLevel = 0 ∧ Kinding program actual term term.kind := by
  intro term member
  obtain ⟨bound,checked⟩ := defaults.terms_kinded term member
  exact checked.source_term level

private theorem SignatureWellFormed.source_terms {program : Program} {module : ModuleId} {signature : Signature}
    (signatureKinded : SignatureWellFormed program module signature)
    (constraints : ∀ constraint ∈ signature.constraints,
      ConstraintKinded program ⟨signature.generics,signature.constraints,0,module,false,{}⟩ constraint) :
    ∀ term ∈ signature.terms, ∃ actual, actual.universeLevel = 0 ∧ Kinding program actual term term.kind := by
  intro term member
  simp only [Signature.terms,List.mem_append,List.mem_cons] at member
  rcases member with ((rfl | rfl | parameter) | requirement) | defaultValue
  · exact signatureKinded.2.2.1.1.source_term rfl
  · exact signatureKinded.2.2.2.1.1.source_term rfl
  · exact (signatureKinded.2.1 term parameter).1.source_term rfl
  · obtain ⟨constraint,present,nested⟩ := List.mem_flatMap.mp requirement
    exact (constraints constraint present).source_terms rfl term nested
  · exact signatureKinded.2.2.2.2.1.source_terms rfl term defaultValue

/-- This is a projection of actual source admission, not an additional
program certificate. It covers captures, quantity sources, associated
bodies, invocation contracts, nested constraints and every ordered default. -/
theorem ProgramWellFormed.terms_kinded {program : Program} (valid : ProgramWellFormed program)
    {declaration : Definition} (declared : declaration ∈ program.declarations) :
    ∀ term ∈ declaration.terms, ∃ context, context.universeLevel = 0 ∧ Kinding program context term term.kind := by
  have shape := (valid.2.2.2.2.1 declaration declared).2.1
  have predicates := valid.constraintsKinded declared
  cases declaration <;> intro term member <;> simp only [Definition.terms] at member
  case data data =>
    rcases List.mem_append.mp member with before | defaults
    · rcases List.mem_append.mp before with before | requirement
      · rcases List.mem_append.mp before with fieldMember | quantity
        · obtain ⟨field,present,rfl⟩ := List.mem_map.mp fieldMember
          obtain ⟨variant,inVariants,inFields⟩ := List.mem_flatMap.mp present
          exact ((shape.2.2.2.1 variant inVariants).2 field inFields).1.1.source_term rfl
        · have selected : data.quantitySource = some term := by simpa using quantity
          exact (shape.2.2.2.2.2.2.1 term selected).1.1.source_term rfl
      · obtain ⟨constraint,present,nested⟩ := List.mem_flatMap.mp requirement
        exact (predicates constraint present).source_terms rfl term nested
    · exact shape.2.2.2.2.2.2.2.1.source_terms rfl term defaults
  case alias alias =>
    rcases List.mem_cons.mp member with rfl | defaults
    · exact shape.2.1.1.source_term rfl
    · exact shape.2.2.1.source_terms rfl term defaults
  case function function =>
    rcases List.mem_append.mp member with before | invocation
    · rcases List.mem_append.mp before with signature | capture
      · exact shape.1.source_terms predicates.1 term signature
      · exact (shape.2.2.2.2.2.2 term capture).1.source_term rfl
    · obtain ⟨relation,present,nested⟩ := List.mem_flatMap.mp invocation
      have contracts := predicates.2 relation present
      simp only [InvocationRelation.terms,List.mem_cons] at nested
      rcases nested with rfl | rfl | rfl | rfl | rfl | argument
      · exact contracts.1.source_terms rfl _ (by simp [Constraint.terms])
      · exact contracts.2.source_terms rfl _ (by simp [Constraint.terms])
      · exact contracts.1.source_terms rfl _ (by simp [Constraint.terms])
      · exact contracts.1.source_terms rfl _ (by simp [Constraint.terms])
      · exact contracts.2.source_terms rfl _ (by simp [Constraint.terms])
      · exact contracts.1.source_terms rfl _ (by simp [Constraint.terms,argument])
  case trait trait =>
    rcases List.mem_append.mp member with requirement | defaults
    · obtain ⟨constraint,present,nested⟩ := List.mem_flatMap.mp requirement
      exact (predicates constraint present).source_terms rfl term nested
    · exact shape.2.2.2.1.source_terms rfl term defaults
  case associated associated =>
    obtain ⟨owner,_,_,_,bodies,defaults⟩ := shape
    rcases List.mem_append.mp member with before | genericDefault
    · rcases List.mem_append.mp before with body | requirement
      · exact (bodies term (by simpa using body)).1.source_term rfl
      · obtain ⟨owner,_,kinded⟩ := predicates
        obtain ⟨constraint,present,nested⟩ := List.mem_flatMap.mp requirement
        exact (kinded constraint present).source_terms rfl term nested
    · exact defaults.1.source_terms rfl term genericDefault
  case implementation implementation =>
    obtain ⟨_,owner,_,_,_,_,_,signature,defaults⟩ := shape
    obtain ⟨_,_,ownerSub,_,arguments,_,bodies⟩ := signature
    rcases List.mem_append.mp member with before | genericDefault
    · rcases List.mem_append.mp before with before | requirement
      · rcases List.mem_append.mp before with argument | bodyMember
        · exact (arguments term argument).1.source_term rfl
        · obtain ⟨entry,present,same⟩ := List.mem_map.mp bodyMember
          rcases entry with ⟨id,body⟩
          cases same
          obtain ⟨_,_,_,_,_,_,_,kinded⟩ := bodies id body present
          exact kinded.1.source_term rfl
      · obtain ⟨constraint,present,nested⟩ := List.mem_flatMap.mp requirement
        exact (predicates constraint present).source_terms rfl term nested
    · exact defaults.1.source_terms rfl term genericDefault
  case effect effect =>
    rcases List.mem_append.mp member with requirement | defaults
    · obtain ⟨constraint,present,nested⟩ := List.mem_flatMap.mp requirement
      exact (predicates constraint present).source_terms rfl term nested
    · exact shape.2.2.2.1.source_terms rfl term defaults
  case operation operation => exact shape.1.source_terms predicates term member
  case constant constant =>
    have checked := shape.1.kinding valid (by simp)
    rcases List.mem_cons.mp member with rfl | member
    · exact checked.2.source_term rfl
    rcases List.mem_cons.mp member with rfl | defaults
    · exact checked.1.source_term rfl
    · exact shape.2.1.source_terms rfl term defaults
  case global global =>
    have same := List.mem_singleton.mp member
    subst term
    exact shape.1.1.source_term rfl
  all_goals exact False.elim (List.not_mem_nil member)

theorem ProgramWellFormed.term_levels {program : Program} (valid : ProgramWellFormed program)
    {declaration : Definition} (declared : declaration ∈ program.declarations) :
    ∀ term ∈ declaration.terms, NoLeak 0 term ∧
      ∀ id kind level, Occurs (.variable id kind level) term → level ≤ 0 := by
  intro term member
  obtain ⟨context,level,kinded⟩ := valid.terms_kinded declared term member
  exact ⟨by simpa only [level] using kinded.noLeak,
    fun _ _ _ occurs => by simpa only [level] using kinded.variable_level occurs⟩

end Glorious.Language
