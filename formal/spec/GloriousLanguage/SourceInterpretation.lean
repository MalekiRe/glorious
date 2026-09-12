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

end ScopeInstantiation
end Glorious.Language
