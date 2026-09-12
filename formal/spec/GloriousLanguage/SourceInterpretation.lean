import GloriousLanguage.ScopedAtomTransport
import GloriousLanguage.ContextTyping
import GloriousLanguage.InputTyping
import GloriousLanguage.Contracts
import GloriousLanguage.ClosedDefinitionalEquality
import GloriousLanguage.LogicalCut

/-! The source-assumption interpretation: how a source typing context and its
symbolic equality are read at the runtime world and runtime context produced by
actual entry. Two things are kept apart on purpose.

* The *local/place* correspondence is `Typing.ContextBindingsTyped`, produced at
  actual entry by `Execution.EnterWorld.contextBindingsTyped` and here completed
  with the runtime meaning of the context's own lexical scope and with the
  invocation provenance of every declared local.
* The *conversion law* `Typing.SourceConversionClosed` reads symbolic source
  equality at the runtime image. Its definitional fragment is proved here
  (structural steps, rows, and the actual alias expansion whose declared body a
  runtime scope does not reinterpret). The remaining constructors -
  `DefinitionalStep.projection` and `DefinitionalStep.defaultProjection`, and
  therefore `Equal.entailed` - need the associated-item selection and
  projection-domain judgments transported at the runtime image, whose
  `EntailsSubstitution` premises are source logical evidence. That transport is
  the recorded open obligation; no axiom or weakened admission is introduced
  here for it. -/
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

/-- Symbolic source equality is read as runtime definitional convertibility of
the two decoded terms. This is the single non-mechanical premise the source
`PlaceType` bridge consumes, and it is stated at the exact runtime context the
bridge has. -/
def SourceConversionClosed (program : Program) (source : Language.Context)
    (runtime : Execution.Context) : Prop :=
  ∀ a b, Equal program source a b →
    DefinitionallyEqual program runtime.static (runtime.term a) (runtime.term b)

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

/-- The runtime interpretation of one source typing context at one actual
world. Beyond the shared local correspondence it records the runtime meaning of
the context's lexical scope and the actual invocation provenance of its
declared locals; the conversion law is deliberately not a field, because it is
the derived obligation above, not an assumption about the context. -/
structure Interpretation (program : Kernel.Program) (world : World)
    (source : Typing.Context) (runtime : Execution.Context) : Prop
    extends ContextBindingsTyped program world source runtime where
  regions : ∀ region, region ∈ source.static.scope.regions →
    ∃ selected, runtime.instantiation.regions.get region = some selected ∧ selected ∈ world.liveRegions
  brands : ∀ brand, brand ∈ source.static.scope.brands →
    ∃ selected, runtime.instantiation.brands.get brand = some selected
  locals : ∀ localSlot ∈ source.locals, ∀ binding,
    runtime.environment.Selects localSlot.id binding → InvocationAddress world binding.address

/-- The runtime image of the definitional steps of a source interpretation: the
definitional-step reading of the source context at one image context and one
scope. The alias expansions are derived below from actual declaration closure;
the projection steps are the recorded obligation. -/
def StepImage (program : Language.Program) (context : Language.Context)
    (scope : ScopeInstantiation) : Prop :=
  ∀ {source : Language.Context} {left right : Term}, DefinitionalStep program source left right →
    DefinitionallyEqual program context (scope.term left) (scope.term right)

/-- Definitional conversion transports to the runtime image once its steps do.
The recursion is the actual elimination of the conversion judgment, including
its row duplicates; it introduces no equality and no normalization. -/
theorem definitional_image {program : Language.Program} {context : Language.Context}
    {scope : ScopeInstantiation} (image : StepImage program context scope) :
    ∀ {source : Language.Context} {left right : Term}, DefinitionallyEqual program source left right →
      DefinitionallyEqual program context (scope.term left) (scope.term right) := by
  intro source _left _right converted
  apply DefinitionallyEqual.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ => True)
    (motive_8 := fun _ _ _ => True)
    (motive_9 := fun _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ => True)
    (motive_11 := fun _ left right _ =>
      DefinitionallyEqual program context (scope.term left) (scope.term right))
    (motive_12 := fun _ _ _ _ => True)
    (motive_13 := fun _ _ _ _ _ => True)
    (motive_14 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_15 := fun _ _ _ _ _ _ _ => True)
    (motive_16 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals try exact True.intro
  all_goals try assumption
  case refl => exact DefinitionallyEqual.refl
  case symm _ _ _ _ ih => exact ih.symm
  case trans _ _ _ _ _ _ first second => exact first.trans second
  case step _ _ _ derived _ => exact image derived
  case row _ _ _ equivalent =>
    exact DefinitionallyEqual.row (equivalent.map_scoped_atoms scope.term
      (ScopeInstantiation.scopedHomomorphism scope))
  case congrChildren _ _ _ same children ih =>
    exact (ScopeInstantiation.scopedHomomorphism scope).congr_relation
      (fun _ => DefinitionallyEqual.refl)
      (fun same children => DefinitionallyEqual.congr same children) same
      (ListRel.of_at same.children_length (fun index first second leftAt rightAt =>
        ih index first second leftAt rightAt))

/-- The meaningful source interpretation at one runtime context: the actual
rationale the closing law consumes. Its `steps` field is the definitional-step
reading (alias expansions are derived in `ScopeInstantiation.stepImage_alias`);
its `entailed` and `assumed` fields are the source logical evidence actually
read at the runtime image - the declared constraint equalities and the
entailment judgment - which are never erased into runtime equality. -/
structure SourceInterpreted (program : Language.Program) (runtime : Execution.Context)
    (source : Language.Context) : Prop where
  steps : StepImage program runtime.static runtime.instantiation
  entailed : ∀ {left right : Term}, Entails program source (.equal left right) →
    DefinitionallyEqual program runtime.static (runtime.term left) (runtime.term right)
  assumed : ∀ {left right : Term}, Constraint.equal left right ∈ source.assumptions →
    DefinitionallyEqual program runtime.static (runtime.term left) (runtime.term right)

/-- The closing law of a source context, derived from its own interpretation by
the actual elimination of `Equal`. Every assumption, entailment and lexical
duplicate is discharged by the interpretation it belongs to; none is replaced
by runtime equality. -/
theorem SourceInterpreted.sourceConversionClosed {program : Language.Program}
    {runtime : Execution.Context} :
    ∀ {source : Language.Context}, SourceInterpreted program runtime source →
      Typing.SourceConversionClosed program source runtime := by
  intro source interpreted left right equal
  apply Equal.rec (program := program)
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun context left right _ => SourceInterpreted program runtime context →
      DefinitionallyEqual program runtime.static (runtime.term left) (runtime.term right))
    (motive_4 := fun _ _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ => True)
    (motive_8 := fun _ _ _ => True)
    (motive_9 := fun _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ => True)
    (motive_11 := fun _ _ _ _ => True)
    (motive_12 := fun _ _ _ _ => True)
    (motive_13 := fun _ _ _ _ _ => True)
    (motive_14 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_15 := fun _ _ _ _ _ _ _ => True)
    (motive_16 := fun _ _ _ _ _ _ => True)
  all_goals try { intros; exact True.intro }
  case refl => intro context term interpretation; exact DefinitionallyEqual.refl
  case symm => intro context left right equality ih interpretation; exact (ih interpretation).symm
  case trans => intro context left middle right first second firstIh secondIh interpretation; exact (firstIh interpretation).trans (secondIh interpretation)
  case congrChildren => intro context left right head _ ih interpretation; exact (ScopeInstantiation.scopedHomomorphism runtime.instantiation).congr_relation (fun _ => DefinitionallyEqual.refl) (fun same children => DefinitionallyEqual.congr same children) head (ListRel.of_at head.children_length (fun index first second leftAt rightAt => ih index first second leftAt rightAt interpretation))
  case assumed => intro context left right member interpretation; exact interpretation.assumed member
  case entailed => intro context left right held _ interpretation; exact interpretation.entailed held
  case definitional => intro context left right converted _ interpretation; exact definitional_image interpretation.steps converted
  case rowDuplicate => intro context rowLeft rowRight rest tails held ih interpretation; simp only [Execution.Context.term,ScopeInstantiation.term]; exact DefinitionallyEqual.rowDuplicate (ih interpretation)
  case tailDuplicate => intro context instances rowLeft rowRight tails held ih interpretation; simp only [Execution.Context.term,ScopeInstantiation.term]; exact DefinitionallyEqual.tailDuplicate (ih interpretation)

  case t => exact equal
  case a => exact interpreted

/-- The interpretation of an assumption-free source context, derived: its
definitional-step reading is the whole content, because an assumption-free
logical equality is actual definitional conversion and a context with no
assumptions has no assumption to read. This is the producer for every context
whose own lexical assumptions are already discharged (in particular the
runtime layout context, whose assumption list is empty by construction); a
context that carries constraints needs the actual instantiation evidence for
them, which is never manufactured here. -/
theorem SourceInterpreted.of_assumption_free {program : Language.Program}
    {runtime : Execution.Context} {source : Language.Context}
    (closed : source.assumptions = [])
    (steps : StepImage program runtime.static runtime.instantiation) :
    SourceInterpreted program runtime source where
  steps := steps
  entailed := fun held =>
    definitional_image steps (Entails.closed_definitional_equal held closed)
  assumed := fun member => by
    rw [closed] at member
    exact False.elim (List.not_mem_nil member)

/-- The runtime closing law, derived: an assumption-free source equality is
definitional conversion (`Equal.closed_definitional`), and conversion is read
at the runtime image once its definitional steps are. -/
theorem sourceConversionClosed {program : Language.Program} {runtime : Execution.Context}
    {source : Language.Context} (assumptions : source.assumptions = [])
    (image : StepImage program runtime.static runtime.instantiation) :
    Typing.SourceConversionClosed program source runtime :=
  fun _left _right equal => definitional_image image (equal.closed_definitional assumptions)

end Typing

namespace ScopeInstantiation

/-- Actual alias expansion transports to the runtime image: the declared body
is closed by `ProgramWellFormed`, so the runtime scope does not reinterpret it
or its parameter graph, and the checked substitution edge survives decoding. -/
theorem definitionalStep_alias {program : Program} {scope : ScopeInstantiation}
    (valid : ProgramWellFormed program) {source : Language.Context} {id : DeclId}
    {declaration : AliasDefinition} {arguments : List Term} {substitution : Substitution}
    {value : Term} (found : program.alias id = some declaration)
    (instantiated : Instantiates declaration.generics arguments substitution)
    (kinded : ∀ argument ∈ arguments,
      Kinding program source argument argument.kind)
    (graph : Substitutes substitution declaration.value value) :
    Substitutes (substitution.map (fun entry => (entry.1,scope.term entry.2)))
        declaration.value (scope.term value) ∧
      DefinitionalStep program source (.alias id (arguments.map scope.term)) (scope.term value) := by
  have member : Definition.alias declaration ∈ program.declarations :=
    List.mem_of_find?_eq_some (Program.alias_lookup found)
  have closed := valid.scopeClosed member
  have fixed : scope.term declaration.value = declaration.value :=
    term_fixed scope declaration.value (closed declaration.value (by
      simp only [Definition.terms,List.mem_cons_self]))
  have mapped := instantiated.map_values scope.term (fun argument _ => term_kind scope argument)
  refine ⟨substitute_values scope substitution declaration.value value graph fixed,?_⟩
  exact .alias found mapped (fun argument member' => by
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member'
    exact (term_kind scope original) ▸ map_kinding scope (kinded original present))
    (substitute_values scope substitution declaration.value value graph fixed)

/-- Alias expansion transports to an image context: the declared body is fixed
by `ProgramWellFormed`, and the actual instantiation and substitution edges
survive decoding. The only input beyond actual declaration closure is the
kinding of the decoded arguments at the image context. -/
theorem ScopeInstantiation.stepImage_alias {program : Language.Program} (valid : ProgramWellFormed program)
    {context : Language.Context} {scope : ScopeInstantiation}
    {id : DeclId} {declaration : AliasDefinition} {arguments : List Term}
    {substitution : Substitution} {value : Term}
    (found : program.alias id = some declaration)
    (instantiated : Instantiates declaration.generics arguments substitution)
    (graph : Substitutes substitution declaration.value value)
    (imageKinding : ∀ argument ∈ arguments.map scope.term,
      Kinding program context argument argument.kind) :
    DefinitionallyEqual program context (scope.term (.alias id arguments)) (scope.term value) :=
  by
    simpa only [ScopeInstantiation.term,Term.mapChildren] using
      (DefinitionallyEqual.step (.alias found
        (instantiated.map_values scope.term (fun argument _ => ScopeInstantiation.term_kind scope argument))
        imageKinding
        (substitute_values scope substitution declaration.value value graph
          (ScopeInstantiation.aliasValue_fixed valid found))))



end ScopeInstantiation
end Glorious.Language
