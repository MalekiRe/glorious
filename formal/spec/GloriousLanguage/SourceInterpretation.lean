import GloriousLanguage.ScopedAtomTransport
import GloriousLanguage.ContextTyping
import GloriousLanguage.InputTyping
import GloriousLanguage.Contracts
import GloriousLanguage.ClosedDefinitionalEquality

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

namespace Typing

/-- Symbolic source equality is read as runtime definitional convertibility of
the two decoded terms. This is the single non-mechanical premise the source
`PlaceType` bridge consumes, and it is stated at the exact runtime context the
bridge has. -/
def SourceConversionClosed (program : Program) (source : Language.Context)
    (runtime : Execution.Context) : Prop :=
  ∀ a b, Equal program source a b →
    DefinitionallyEqual program runtime.static (runtime.term a) (runtime.term b)

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

/-- The recorded open obligation in its exact form: transporting the two
projection steps of `DefinitionalStep` at the runtime image. It is stated as a
proposition-valued target, not assumed anywhere below. -/
def ProjectionStepConversion (program : Program) (source : Language.Context)
    (runtime : Execution.Context) : Prop :=
  ∀ left right, DefinitionalStep program source left right →
    (∃ (associated : AssociatedDefinition), ∃ trait member owners items,
        left = .projection trait member owners items associated.kind ∧
        (DefinitionalStep program runtime.static (runtime.term left) (runtime.term right) ∨
          DefinitionallyEqual program runtime.static (runtime.term left) (runtime.term right)))
    ∨ ¬ ∃ (associated : AssociatedDefinition), ∃ trait member owners items, left = .projection trait member owners items associated.kind


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


/-- The recorded projection obligation is exactly the projection-shaped
instance of the step image: a projection-headed definitional step is either an
actual runtime step or already a runtime conversion, and either way its two
images convert. -/
theorem ProjectionStepConversion.step {program : Language.Program} {source : Language.Context}
    {runtime : Execution.Context} (obligation : Typing.ProjectionStepConversion program source runtime)
    {left right : Term} (derived : DefinitionalStep program source left right)
    (shape : ∃ (associated : AssociatedDefinition), ∃ trait member owners items,
      left = .projection trait member owners items associated.kind) :
    DefinitionallyEqual program runtime.static (runtime.term left) (runtime.term right) := by
  rcases obligation left right derived with ⟨associated,trait,member,owners,items,_same,converted⟩ | absent
  · rcases converted with stepped | equal
    · exact DefinitionallyEqual.step stepped
    · exact equal
  · exact False.elim (absent shape)

end ScopeInstantiation
end Glorious.Language
