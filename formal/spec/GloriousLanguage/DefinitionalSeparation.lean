import GloriousLanguage.DefinitionalChurchRosser
import GloriousLanguage.DefinitionalNormalForms
import GloriousLanguage.ClosedDefinitionalEquality

/-! Constructor and scalar separation for the ordinary conversion judgment.
The actual definitional quotient and assumption-free logical equality consume
Church–Rosser here. Arbitrary lexical assumptions are not declared consistent. -/
namespace Glorious.Language

theorem DefinitionallyJoinable.equal {program : Program} {context : Context} {left right : Term}
    (joined : DefinitionallyJoinable program context left right) : DefinitionallyEqual program context left right := by
  obtain ⟨_,first,second⟩ := joined
  exact first.equal.trans second.equal.symm

theorem DefinitionallyEqual.iff_joinable {program : Program} (valid : ProgramWellFormed program)
    {context : Context} (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    {left right : Term} : DefinitionallyEqual program context left right ↔ DefinitionallyJoinable program context left right :=
  ⟨fun equal => equal.joinable valid contextKinded,DefinitionallyJoinable.equal⟩

/-- Structural constructors preserve their actual annotations and ordered
children under arbitrary conversion, even when those children contain active
recursive aliases or associated projections. -/
theorem DefinitionallyEqual.structural_decomposition {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Term} (equal : DefinitionallyEqual program context left right)
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    (leftStructural : left.StructuralHead) (rightStructural : right.StructuralHead) :
    SameHead left right ∧ ListRel (DefinitionallyEqual program context) left.children right.children := by
  obtain ⟨head,children⟩ := (equal.joinable valid contextKinded).structural_decomposition leftStructural rightStructural
  exact ⟨head,children.imp (fun _ _ joined => joined.equal)⟩

theorem DefinitionallyEqual.structural_iff {program : Program} (valid : ProgramWellFormed program)
    {context : Context} (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    {left right : Term} (leftStructural : left.StructuralHead) (rightStructural : right.StructuralHead) :
    DefinitionallyEqual program context left right ↔ SameHead left right ∧
      ListRel (DefinitionallyEqual program context) left.children right.children :=
  ⟨fun equal => equal.structural_decomposition valid contextKinded leftStructural rightStructural,
    fun ⟨head,children⟩ => .congr head children⟩

theorem DefinitionallyEqual.nominal_injective {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {first second : DeclId} {left right : List Term}
    (equal : DefinitionallyEqual program context (.nominal first left) (.nominal second right))
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement) :
    first = second ∧ ListRel (DefinitionallyEqual program context) left right := by
  obtain ⟨head,children⟩ := (equal.joinable valid contextKinded).nominal_injective
  exact ⟨head,children.imp (fun _ _ joined => joined.equal)⟩

theorem DefinitionallyEqual.normal_unique {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Term} (equal : DefinitionallyEqual program context left right)
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    (leftNormal : ExpansionNormal program context left) (rightNormal : ExpansionNormal program context right) :
    RowEquivalent left right := (equal.joinable valid contextKinded).normal_unique valid leftNormal rightNormal

theorem DefinitionallyEqual.scalar_injective {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Scalar}
    (equal : DefinitionallyEqual program context (.scalar left) (.scalar right))
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement) : left = right :=
  (equal.joinable valid contextKinded).scalar_injective valid

/-- Positive agreement is derived for the same raw generic tables used by
selection. It is not strengthened into a new declaration-admission premise. -/
theorem SubstitutionsConvertible.joinable {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Substitution} (equal : SubstitutionsConvertible program context left right)
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement) :
    SubstitutionsJoinable program context left right :=
  equal.imp (fun _ _ related => ⟨related.1,related.2.joinable valid contextKinded⟩)

theorem SelectsImpl.joinable_unique {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {trait : DeclId} {arguments : List Term} {firstNegative secondNegative : Bool}
    {first second : ImplDefinition} {firstSub secondSub : Substitution}
    (left : SelectsImpl program context trait arguments firstNegative first firstSub)
    (right : SelectsImpl program context trait arguments secondNegative second secondSub)
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement) :
    first = second ∧ SubstitutionsJoinable program context firstSub secondSub := by
  obtain ⟨same,tables⟩ := left.unique valid right
  exact ⟨same,tables.joinable valid contextKinded⟩

namespace DefinitionalQuotient

/-- The actual quotient by all ordinary conversions distinguishes every
scalar type. Row-only discrimination is no longer the endpoint of the proof. -/
theorem scalar_injective {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Scalar}
    (equal : (ofTerm (.scalar left) : Class program context) = ofTerm (.scalar right))
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement) : left = right :=
  (ofTerm_eq.mp equal).scalar_injective valid contextKinded

theorem eval_scalar_injective {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Scalar}
    (equal : (algebra program context).eval canonical (.scalar left) = (algebra program context).eval canonical (.scalar right))
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement) : left = right := by
  rw [eval_canonical,eval_canonical] at equal
  exact scalar_injective valid equal contextKinded

end DefinitionalQuotient

/-- Empty assumptions discharge context kinding and eliminate the logical
equality rules that could otherwise identify distinct scalar constructors. -/
theorem Equal.closed_scalar_injective {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Scalar} (equal : Equal program context (.scalar left) (.scalar right))
    (closed : context.assumptions = []) : left = right :=
  (equal.closed_definitional closed).scalar_injective valid (fun _ member => by rw [closed] at member; cases member)

theorem Entails.closed_scalar_equal {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Scalar} (held : Entails program context (.equal (.scalar left) (.scalar right)))
    (closed : context.assumptions = []) : left = right :=
  (Equal.entailed held).closed_scalar_injective valid closed

end Glorious.Language
