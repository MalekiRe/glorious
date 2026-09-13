import GloriousLanguage.ContextTyping
import GloriousLanguage.ClosedDefinitionalEquality
import GloriousLanguage.LogicalCut

/-! Source equality is interpreted by the actual entry-produced context
invariant: generic binders have been instantiated, scoped names are covered,
and every decoded source assumption is logically discharged. Full logical
transport therefore derives definitional conversion at the assumption-free
runtime context, including associated projections and quantified predicates.
Physical structural expansions use the existing layout and alias relations. -/
namespace Glorious.Language

/-- Conversion at the physical layout context is conversion at any actual
runtime context: the two contexts share their binder list, universe level and
lexical scope, carry no assumptions, and the source kinding domain is
unchanged. -/
theorem DefinitionallyEqual.runtime_context {program : Program} {runtime : Execution.Context}
    {left right : Term}
    (equal : DefinitionallyEqual program ⟨[],[],0,default,false,{}⟩ left right) :
    DefinitionallyEqual program runtime.static left right :=
  (Equal.closed_definitional
    (.entailed ((Entails.equality (.definitional equal)).cut
      (fun term kind => ⟨fun typed => typed.context_same_domain rfl rfl rfl,
        fun typed => typed.context_same_domain rfl rfl rfl⟩)
      (by intro requirement member; cases member)))
    (show runtime.static.assumptions = [] from rfl))

namespace Typing

/-- Source equality becomes runtime definitional conversion. The source place
bridge derives this law from the actual context invariant below. -/
def SourceConversionClosed (program : Program) (source : Language.Context)
    (runtime : Execution.Context) : Prop :=
  ∀ a b, Equal program source a b →
    DefinitionallyEqual program runtime.static (runtime.term a) (runtime.term b)

theorem ContextBindingsTyped.conversionClosed {program : Kernel.Program} {world : World}
    {source : Context} {runtime : Execution.Context}
    (valid : ProgramWellFormed program.declarations) (typed : ContextBindingsTyped program world source runtime) :
    SourceConversionClosed program.declarations source.static runtime := by
  intro left right equal
  apply Entails.closed_definitional_equal ?_ rfl
  simpa only [Constraint.mapTerms] using typed.entails valid (Entails.equality equal)

/-- A declared storage type read at the physical layout context: either it is
already structurally headed, or the program's own alias declaration expands it
- by the same declaration, instantiation and checked substitution edge that
`DefinitionalStep.alias` uses, at the same physical layout context - to a term
that continues the chain. Its derivations are exactly the admitted alias-headed
containers the actual `LayoutOf.alias` case introduces; this is the physical
realization of such a container, not a second field walker. -/
inductive StructuralExpansion (program : Program) : Term → Term → Prop where
  | head {type} : type.StructuralHead → StructuralExpansion program type type
  | alias {id arguments declaration substitution expanded result} :
      program.alias id = some declaration →
      Instantiates declaration.generics arguments substitution →
      (∀ argument ∈ arguments, Kinding program ⟨[],[],0,default,false,{}⟩ argument argument.kind) →
      Substitutes substitution declaration.value expanded →
      StructuralExpansion program expanded result →
      StructuralExpansion program (.alias id arguments) result

/-- The end of a structural expansion is structurally headed: aliases are the
only heads it removes. -/
theorem StructuralExpansion.structuralHead {program : Program} {type expanded : Term}
    (expansion : StructuralExpansion program type expanded) : expanded.StructuralHead := by
  refine StructuralExpansion.rec (motive := fun _ expanded _ => expanded.StructuralHead) ?_ ?_ expansion
  · intro type structural
    exact structural
  · intro id arguments declaration substitution body result found instantiated kinds graph inner ih
    exact ih

/-- Every structural expansion is source equality at the physical layout
context, so `LayoutOf.alias` gives the expansion the container's layout. -/
theorem StructuralExpansion.equal {program : Program} {type expanded : Term}
    (expansion : StructuralExpansion program type expanded) :
    Equal program ⟨[],[],0,default,false,{}⟩ type expanded := by
  refine StructuralExpansion.rec
    (motive := fun start stop _ => Equal program ⟨[],[],0,default,false,{}⟩ start stop) ?_ ?_ expansion
  · intro type structural
    exact .refl
  · intro id arguments declaration substitution body result found instantiated kinds graph inner ih
    exact .trans (.definitional (.step (.alias found instantiated kinds graph))) ih

/-- The expansion is definitional conversion at the physical layout context
(which has no assumptions). -/
theorem StructuralExpansion.definitionallyEqual {program : Program} {type expanded : Term}
    (expansion : StructuralExpansion program type expanded) :
    DefinitionallyEqual program ⟨[],[],0,default,false,{}⟩ type expanded :=
  (expansion.equal).closed_definitional rfl

/-- A physical field offset at the expansion of a declared type is a physical
field offset at the declared type: the alias-headed container has its
expansion's offsets, by the same ordered-layout derivation. -/
theorem StructuralExpansion.fieldOffset {program : Program} {world : World} {address : Address}
    {container expanded : Term} {index : Nat} {child : Term} {offset : Nat}
    (expansion : StructuralExpansion program container expanded)
    (located : FieldOffset program world address expanded index child offset) :
    FieldOffset program world address container index child offset := by
  refine StructuralExpansion.rec
    (motive := fun start stop _ =>
      FieldOffset program world address stop index child offset →
        FieldOffset program world address start index child offset) ?_ ?_ expansion located
  · intro type structural inner
    exact inner
  · intro id arguments declaration substitution body result found instantiated kinds graph inner ih innerLocated
    exact .alias found instantiated graph (ih innerLocated)

/-- The expansion chain composes: a later expansion of the end is an expansion
of the start. -/
theorem StructuralExpansion.trans {program : Program} {first middle last : Term}
    (before : StructuralExpansion program first middle)
    (after : StructuralExpansion program middle last) :
    StructuralExpansion program first last := by
  refine StructuralExpansion.rec
    (motive := fun start stop _ =>
      StructuralExpansion program stop last → StructuralExpansion program start last) ?_ ?_ before after
  · intro type structural inner
    exact inner
  · intro id arguments declaration substitution body result found instantiated kinds graph inner ih innerAfter
    exact .alias found instantiated kinds graph (ih innerAfter)

end Typing
end Glorious.Language
