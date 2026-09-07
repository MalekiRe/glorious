# Stage-0 semantic coverage gate

This directory defines the executable language-semantics gate for the Rust
Stage-0 compiler. The current normative source is the
[language specification](../../glorious-language-specification.md), with library
contracts in the [standard-library specification](../../glorious-standard-library-specification.md).
The inventory below was derived from the previous core draft; it is regression
evidence, not complete conformance coverage for the consolidated specifications
or a backward-compatibility obligation. Update expectations for intentional
semantic changes. Optimizer breadth, compiler service lifecycle behavior, and
self-hosting convergence remain separate gates.

## Authoritative inventory

`stage0-semantic-inventory.tsv` is the machine-readable source of truth. It has
one row for every rule in the previous core draft's three acceptance sections
([recorded source](https://github.com/MalekiRe/glorious/blob/7e4a021811b6a8e0d62b2899f10e602d037c3c14/glorious-branded-environment-core-spec.md)):

- 22 conformance requirements from section 19;
- 18 safety invariants from section 17;
- 8 required rejection examples from section 18.

Every row records a stable rule ID, the requirement, one or more enabled executable
tests, and their current state:

- `anchor`: an existing passing test is the coverage witness;
- `red`: an enabled conformance test specifies required behavior that is not
  yet implemented or has not yet been demonstrated green by the Stage-0 suite.

Composite tests are intentional. One carefully constructed source program can
cover several mutually dependent rules more faithfully than isolated syntax
micro-tests. A rule may share an anchor with another rule, but no rule may be
left without an executable witness.

The `semantic_conformance` integration target—rooted at
`crates/grandiose-stage0/tests/semantic_conformance.rs` with focused modules in
`crates/grandiose-stage0/tests/semantic_conformance/`—enforces the inventory:

1. the exact 48-rule normative set is present with no duplicate IDs;
2. every row points to an existing `#[test]` function;
3. no mapped test is ignored;
4. every new `semantic_*` conformance test is mapped back to at least one
   normative rule.

This makes omission itself a test failure. Adding, deleting, renaming, or
ignoring a conformance anchor requires an explicit inventory update.

## Existing semantic acceptance anchors

The rule inventory composes the following established suites rather than
replacing them.

| Compendium chapter | Combined executable coverage |
| --- | --- |
| 13. Types, normalization, inference | `types.rs`: occurs checking, zonking, kind separation, open effect-row unification, `Never`, structural constants, and canonical fingerprints. |
| 14. Generics, traits, associated items, GATs, HRTBs, consts | `trait_solver.rs`, `coherence.rs`, and the service materialization tests cover tabled selection, associated normalization, overlap, orphan rules, mixed generic kinds, and higher-ranked contracts. |
| 15. Effects, handlers, resumptions, cancellation | `service.rs`: deep handlers, residual-stack restoration, ordered pattern matrices, generic effect identity, finite replay, terminal operations, cancellation, and the enabled composite red cases. |
| 16. Quantitative ownership | `quantity.rs`, `useflow.rs` consumers, and service tests cover interval algebra, branch hulls, callable lower bounds, replay multiplication, escape transfer, and cancellation obligations. |
| 17. Regions, lifetimes, borrowing, reborrowing | `core.rs` PlaceFlow fixtures and service tests cover projected loans, unique writeback, NLL, reborrowing, HRTBs, variance, escape, and handler/label boundaries. |
| 18. Callables, captures, brands, environments, refinements | `core.rs` and `service.rs` cover closure brands, sealed capture layouts, shared/unique/move modes, callable aggregates, handler payloads, replayed captures, and refinement scopes. |
| 19. Typed Core | `core.rs` covers frozen call/effect provenance, Core validation, labels, structural patterns, host primitives, inference sealing, and semantic fingerprints. |
| 20. PlaceFlow and executable lowering | `core.rs` and `mir.rs` cover initialization, partial moves, branch joins, loans, cleanup plans, continuation snapshots, forged-MIR rejection, VM verification, and execution. `core.rs::source_lowering_executes_handler_partial_move_and_label_leave` inspects an ordinary source body across Core, PlaceFlow, frozen MIR, VM emission, verification, and execution; `service.rs::service_executes_handler_partial_move_and_label_leave` proves the same shape through a published service artifact. |

## Newly explicit cross-cutting conformance cases

The rule-level suite adds coverage where chapter-level references were too
coarse. The composite fixtures cover:

- canonical keywordless callable declarations, result/effect omission, compact
  labels, implicit function labels, and recursive activation freshness;
- labels as generic diverging callables and label-indexed protocol identity;
- nested lexical label brands through refutable handler forwarding, a generic
  facade transfer, and the enclosing normal-completion rejoin;
- ordered multi-payload refutable forwarding preserves every successful
  prefix test before a later mismatch reaches the generic-label rejoin;
- a forwarded cancellation through that generic-label rejoin drops its
  protected lexical payload once before the completion observes outer state;
- exact `[2,2]` replay can cross a late multi-payload refutable `Forward`,
  return both residual results to its outer clause, and then rejoin through a
  generic label facade without duplicating protected cleanup;
- source-defined control names and contextual delayed blocks selected by `Fn`
  constraints rather than compiler-known names;
- fresh callable/environment brands, sealed `RunsIn` evidence, the canonical
  empty environment, ordinary shared/unique/move access, and the absence of a
  receiver-mode enum;
- `Available<E>` creation and release restrictions plus unforgeability of all
  compiler-generated relations;
- principal `Use` restriction, structural interval intersection, and the G1
  ban on restricted-use memoized globals;
- custom `Drop` eligibility, exactly-once cleanup, nonlocal cleanup, opacity to
  partial moves/deconstruction, and the prohibition on effects or label
  transfer from a destructor;
- conditional custom `Drop` selection: an inapplicable generic destructor
  leaves its concrete aggregate eligible for ordinary partial movement, while
  a selected instantiation remains opaque
  (`service_allows_partial_move_when_a_conditional_drop_impl_is_not_selected`,
  `service_rejects_partial_move_when_a_conditional_drop_impl_is_selected`);
- a nominal associated-type default remains a real selected `Packet<T>` across
  a reciprocal public facade. Its unselected conditional destructor permits
  partial movement through Core and the VM; a revision that selects the bound
  rejects that move, publishes no child cache/traces, and still permits
  whole-value cleanup execution
  (`typed_core_materializes_defaulted_nominal_items_before_partial_move_analysis`,
  `service_selects_defaulted_nominal_drop_through_recursive_facade_revisions`);
- an HRTB associated nominal callback result can carry a move-only field into
  a captured closure. Its unselected conditional Drop keeps a disjoint field
  move executable through Core/MIR/VM and decoded bytecode, while a facade
  revision selecting Drop rejects that exact projected partial move without
  publishing cache or trace products
  (`service_preserves_hrtb_associated_nominal_partial_moves_through_closure_revisions`);
- the absence of compiler-known control/arithmetic variants in `CoreKind`;
- a small independent evaluator/verified-VM differential for branded label
  execution;
- source-oriented diagnostics for label/environment escape;
- one-shot over-resume, multi-shot unique-borrow capture, and multi-shot active
  label capture.
- private nominal-field authority across source entries, including a permitted
  same-entry construction/projection and rejected cross-entry access;
- mixed-polarity trait coherence at the service boundary, so contradictory
  positive and negative implementations cannot reach executable lowering.
- recursive generic supertrait closures carry one selected associated type,
  effect row, and const identity through a public callback facade, Core, VM,
  source-order replay, and transactional rejection of both a recursive edge
  and an overlapping implementation
  (`typed_core_normalizes_all_selected_items_through_recursive_generic_supertraits`,
  `service_materializes_all_selected_items_through_recursive_generic_supertrait_facades`).
- package-level orphan coherence through public re-export facades: a local
  self type remains a valid anchor for an imported trait and reaches VM
  execution, while an imported trait plus imported self type is rejected
  before body lowering (`service_enforces_cross_package_orphan_coherence_through_public_reexports`).
- dependency trait facades preserve public associated-type contracts through
  projection, method selection, Core, and VM execution, but cannot expose a
  private provider trait (and therefore cannot leak its associated-item API)
  (`service_preserves_associated_item_authority_through_dependency_trait_facades`).
- a twice-aliased dependency facade retains the provider identity of an
  inherited generic trait method and both of its associated GAT families.  An
  implementation contract normalizes selected `Self` projections before it is
  compared, then its layout and effect row cross indirect invocation, handler
  dispatch, and VM execution; without the selected implementation, the facade
  remains a `G4190` rejection (`service_executes_aliased_reexported_generic_trait_gats_through_vm_handlers`,
  `service_rejects_aliased_reexported_generic_trait_gats_without_an_impl`).
- mutually recursive public module interfaces can likewise converge when two
  glob imports reach the same child-trait/effect identities through opposite
  facade paths. A selected generic row and `Self`-projected GAT method reaches
  the VM, while the identical SCC without an implementation terminates in the
  required `G4190` rejection rather than retaining a cyclic provisional
  interface (`service_executes_recursive_module_facade_gat_effect_contracts_through_vm`,
  `service_rejects_unselected_recursive_module_facade_gat_effect_contracts`).
- callable type aliases retain braced associated effect-row projections in
  their header rather than being cut off as declaration bodies. A reciprocal
  module facade can therefore export a generic GAT callback alias, select the
  inherited trait method as its indirect value, and execute the handler path
  in the VM (`scanner_keeps_braced_callable_effect_rows_inside_type_alias_headers`,
  `service_executes_recursive_facade_gat_callback_aliases_through_vm`).
- a public callable alias may cross a reciprocal module SCC before reaching a
  higher-ranked callback with a selected associated effect-GAT row. The alias
  executes as an indirect VM value; if the public aliases truly recurse, alias
  normalization terminates with `G3307` rather than publishing a provisional
  interface (`service_executes_recursive_public_hrtb_callable_aliases_through_vm`,
  `service_rejects_recursive_public_hrtb_callable_alias_cycles`).
- row-generic public aliases keep their braced tail rows intact while they cross
  a reciprocal module SCC and normalize into an HRTB callback. Reversing
  logical-source enumeration preserves the emitted VM fingerprint and canonical
  bytes as well as execution; a genuinely recursive generic instantiation still
  terminates as `G3307` (`recursive_row_generic_hrtb_callable_aliases_are_order_independent_and_execute`,
  `service_rejects_row_generic_recursive_public_callable_alias_cycles`).
- multiple public glob paths through a recursive facade graph may denote the
  same provider callable alias and function. They deduplicate by declaration
  identity instead of becoming a false ambiguity, independent of logical-source
  enumeration (`recursive_public_facade_globs_deduplicate_the_same_callable_alias_identity`).
- effect declaration visibility across dependency-package boundaries, including
  direct public perform/handler execution and rejection of a private effect;
- qualified nominal identity for same-named public declarations in separate
  modules, carried through record construction, projection, and VM execution.
- public fixity declarations cross glob imports and public re-export facades
  with their operator traits. The importing body's grouping table therefore
  observes the resolved operator identity rather than only declarations in its
  own source file (`service_imports_public_fixities_with_their_operator_traits_across_modules`).
- competing public fixity declarations imported from separate dependency
  packages remain an explicit body-grouping ambiguity rather than degrading
  into a missing declaration (`service_rejects_ambiguous_dependency_fixity_imports`).
- dependency manifest names retain their exact package identity while crossing
  the source boundary through the required hyphen-to-underscore module alias;
  malformed and colliding aliases fail while the immutable request world is
  normalized, before interface or body publication.
- package-level dependency cycles are rejected from resolved import-module
  edges before bodies can materialize. This remains true when reciprocal
  hyphenated package aliases publicly re-export a generic effect and selected
  trait GAT contract, and diagnostics are invariant under source enumeration
  (`service_rejects_recursive_hyphenated_dependency_facades_with_generic_effect_gats`).
- a legal reciprocal module SCC inside one package may re-export a shared
  provider's generic effect, HRTB GAT callback alias, callable, and fixity
  while a separate hyphenated package-import SCC is rejected. The illegal
  SCC emits only canonical cycle diagnostics and publishes nothing; removing
  it reuses exactly the still-valid module-SCC identities and VM bytes
  (`service_isolates_illegal_hyphenated_package_cycles_from_legal_hrtb_module_sccs`).
- legal package DAG paths that export same-named generic HRTB callable aliases,
  GAT effect contracts, and fixity metadata deduplicate only when they retain
  one provider identity; distinct providers remain canonically ambiguous.
  Making one facade's aliases private is transactional, and repair restores
  the exact public artifact without stale products
  (`service_seals_dag_hrtb_alias_interfaces_before_private_facade_transactions`).
- generic operator resolution keeps cache identity with generic callable and
  GAT effect aliases: one provider deduplicates through two facades and is
  byte-stable under reordering, distinct same-spelled providers are ambiguous,
  private revision failures publish nothing, and a repaired provider revision
  refreshes the facade and VM artifact (`service_revises_generic_operator_facade_cache_identities_transactionally`).
- generic dependency effect identity through exact replay and optional
  cancellation, including rejection when the imported handler's concrete
  effect instance does not match the performed one.
- generic effect re-export facades preserve one instantiated operation
  identity from provider performance through root replay and VM execution;
  the facade cannot expose the corresponding private effect declaration
  (`service_preserves_generic_effect_identity_through_dependency_reexport_facades`).
- a three-package DAG diamond may expose the same generic effect, child-trait,
  and selected associated-GAT contract through two public hyphenated facades.
  The root deduplicates those provider identities, emits byte-identical VM
  artifacts under source reordering, and rejects the same diamond if its
  effect remains private (`service_executes_three_package_diamond_gat_effect_facades_canonically`,
  `service_rejects_private_generic_effects_through_three_package_diamond_facades`).
- two provider packages may use the same generic trait/effect spelling without
  sharing an identity. Explicit facade aliases preserve both identities through
  GAT selection and VM execution; dual globs instead produce canonical effect
  ambiguity, and a public provider never authorizes an identically spelled
  private provider re-export (`service_keeps_same_spelled_generic_diamond_facades_provider_distinct_through_vm`,
  `service_reports_same_spelled_distinct_provider_diamond_aliases_as_ambiguous`,
  `service_rejects_private_same_spelled_generic_effect_reexports_in_a_provider_diamond`).
- package facades preserve public generic effect/GAT authority and a provider's
  operator fixity/trait as one identity: an authorized diamond executes and
  emits stable VM bytes, while same-spelled fixities from distinct providers
  remain a canonical ambiguity. Public operator authority cannot leak a
  private generic effect or trait re-export (`service_executes_generic_authorized_reexport_diamond_with_operator_fixity`,
  `service_reports_distinct_provider_reexported_fixities_canonically`,
  `service_rejects_private_generic_reexports_despite_public_operator_authority`).
- a public callable type alias retains its braced generic effect row through
  two dependency facades together with an imported fixity/trait pair, yielding
  a source-order-stable executable artifact. If the trait is private while the
  fixity stays public, exported-interface authority fails before body grouping
  (`service_executes_multilevel_callable_alias_effect_row_and_fixity_facades`,
  `service_rejects_partial_multilevel_operator_reexports_before_grouping`).
- generic associated type/effect items and a callable alias may cross the same
  re-export chain, preserving selected trait-method identity, an imported
  generic operator trait, canonical VM bytes, and execution. Private versions
  of the associated contract, alias, and effect are rejected before grouping
  with source-order-stable interface diagnostics
  (`service_preserves_generic_associated_items_and_callable_aliases_through_reexport_chains`,
  `service_rejects_private_associated_item_and_callable_alias_reexports_before_grouping`).
- sealed public interface fingerprints for generic associated item/effect
  contracts and callable aliases remain identical when every package source is
  enumerated in reverse; request normalization collapses both orders to the
  exact same frozen world. A facade cannot publicly re-export an alias that
  its direct dependency imported privately: the invalid chain produces only
  the authority error and rolls back all staged interface/cache/dependency facts
  (`service_seals_generic_facade_interface_fingerprints_independent_of_source_enumeration`,
  `service_rolls_back_malformed_private_generic_facade_reexports_before_interface_publication`).
- after a valid generic provider and facade have populated the frozen-interface
  cache, a new downstream facade that publishes a fixity while retaining its
  operator trait privately is still fully transactional: it reports only the
  authority failure, leaves cache accounting unchanged, publishes no partial
  dependency traces, and is deterministic under reversed source enumeration
  (`service_discards_downstream_private_fixity_facade_staging_after_reusing_generic_upstreams`).
- replacing a provider package with a new version under the same import alias
  changes a generic facade's selected associated contracts and public fixity
  metadata. The cached facade interface and downstream linked product change,
  canonical VM bytes/fingerprints change with the associativity result, and
  the interface cache records fresh misses rather than reusing stale metadata
  (`service_invalidates_generic_facade_artifacts_across_provider_versioned_fixity_updates`).
- when two versioned hyphenated packages would normalize to the same source
  alias, the request is rejected canonically before touching an already
  published generic facade or its interface cache. Replacing that collision
  with the valid newer provider then re-elaborates the trait/effect/fixity
  facade and VM artifact instead of retaining either stale diagnostics or
  canonical metadata
  (`service_recovers_from_hyphen_alias_version_collisions_without_stale_generic_facade_state`).
- sequential pinned sessions may use the same hyphenated dependency alias with
  incompatible generic public contracts. A rejected child world reports its
  own canonical type diagnostic without publishing cache/interface products,
  while the already-open parent session retains its original trait/effect/
  fixity identity and executable result
  (`service_pins_same_alias_generic_dependency_worlds_without_interface_or_diagnostic_leaks`).
- public and private dependency worlds may reuse the same package identity
  while exposing incompatible generic GAT interfaces. A private authority
  failure emits its private lookup/projection diagnostics, while a separate
  all-public world emits the competing-fixity ambiguity; neither rejected
  world publishes cache/interface facts or contaminates the repaired public
  world that follows
  (`service_isolates_private_authority_and_public_fixity_diagnostics_across_generic_dependency_worlds`).
- a versioned provider world may combine a private effect, a public
  GAT-selected callable alias whose result no longer meets the caller
  contract, and a second public fixity identity. The exact mixed diagnostic
  sequence is the single private-effect authority error—the interface barrier
  deliberately precedes the later body mismatch/fixity errors—under source
  reordering, publishes no cache/interface products, and cannot contaminate a
  later repaired provider version
  (`service_canonicalizes_mixed_invalid_versioned_provider_diagnostics_without_cache_leaks`).
- a package facade may contain a legal public cycle among its own modules
  while both sides re-export the same external generic provider. All members
  retain that one provider interface/fixity identity and emit stable VM bytes
  under source reordering; a private provider still cannot cross the cyclic
  public facade, and failure rolls back every staged package product
  (`service_executes_cross_package_public_module_reexport_cycles_with_one_generic_provider_identity`,
  `service_rejects_private_provider_authority_through_cross_package_module_reexport_cycles`).
- a public package module cycle may split generic trait, effect, callable, and
  operator-fixity aliases across its members. Every alias-bearing interface
  retains its provider dependency and executes in the VM; replacing that
  provider with private trait/effect contracts rejects the entire child world
  without producing a public operator ambiguity, preserves the public parent
  traces and cache state, and reports canonical diagnostics under source
  reordering
  (`service_rolls_back_private_alias_exports_through_public_package_module_cycles`).
- a versioned provider behind those cyclic aliases may move from a legal
  public revision to a private and incompatible revision, then to a repaired
  public revision. The rejected revision publishes no cache/traces or stale
  diagnostics; the repaired revision freezes fresh facade metadata and a new
  canonical VM artifact under the updated fixity
  (`service_recovers_versioned_public_cycle_aliases_after_private_incompatible_revision`).
- two independent cyclic facades may share the same normalized provider alias
  across sequential provider versions. Both facades retain their original
  generic interfaces and fixity result while a private/incompatible revision
  is rejected, then independently freeze the repaired provider identity and
  updated VM result without cache or diagnostic leakage
  (`service_isolates_parallel_cyclic_facades_across_versioned_provider_worlds`).
- a three-version cyclic package facade may export same-named generic GAT
  traits, effects, callable aliases, and fixity/trait pairs. Its public v0.1
  provider executes, a v0.2 split across private and independently named
  providers fails only during authority/identity resolution without publishing
  products, and a repaired v0.3 provider yields new provider traces and
  canonical VM bytes with no stale diagnostics
  (`service_recovers_three_version_cyclic_alias_slice_without_stale_publication`).
- two unrelated dependency diamonds may publish the same local generic aliases
  while retaining separate provider identities. A private callable/effect/GAT
  revision in one diamond is transactional: it emits canonical private
  callable/trait/effect diagnostics, publishes no child products, and leaves the other
  diamond's interfaces, cache state, and independently compiled VM bytes
  unchanged. Repairing the failed side refreshes only that provider/facade
  identity (`service_isolates_unrelated_generic_diamonds_from_private_callable_revisions`).
- two package facades may each contain a public module re-export cycle. When
  both ultimately expose one provider, aliases deduplicate to that identity;
  when they expose same-spelled distinct providers, both generic callback/GAT
  paths remain independently callable and produce a different canonical
  artifact. A private distinct provider remains blocked through its own cycle
  without publishing staged cache products
  (`service_distinguishes_provider_identities_through_parallel_package_module_cycles`).
- parallel cyclic facades preserve provider identity even when the providers
  share all generic trait, effect, and public operator-fixity names. The
  shared and distinct public worlds have stable but different VM artifacts;
  a private branch rejects its facade imports without leaking into public
  operator grouping, rolls back cache products, and reports the same
  diagnostics under source reordering
  (`service_seals_generic_fixity_identity_through_parallel_package_module_cycles`).
- an exact replay may perform an outer effect from inside its inner handler
  clause, then return across ordinary call frames to continue the next replay
  use. The VM restores the clause's program location as well as registers and
  handler frames; the local and dependency-private-helper cases execute this
  control shape (`service_executes_local_generic_nested_handler_replay_with_an_outer_effect`,
  `service_links_private_generic_nested_handler_replay_bodies_from_dependencies`).
- nested exact replay remains compositional across a public dependency facade:
  an exported outer operation replays an inner handler clause twice, each
  inner path replays a dependency-private generic operation twice, and every
  clause return restores its own dynamic program context
  (`service_restores_nested_replay_contexts_through_dependency_facade_bodies`).
- imported reference lifetime relations through a local closure and handler,
  including rejection of a closure escape after the imported call.
- whole-referent `move *reference` retains its direct unique-reference handle
  only for an exact later `*reference = value` restoration; reads, shared
  referents, handler boundaries, and body/scope completion while the referent
  hole is open are rejected
  (`whole_unique_referent_move_requires_exact_restoration_before_reuse`).
- trailing structural const defaults on nominal declarations, including direct
  `u32`, defaults derived from an earlier `u32` binder, and `Quantity`, are
  completed consistently in source signatures and record construction before
  VM execution; non-trailing defaults are rejected
  (`service_applies_trailing_const_generic_defaults_to_nominal_layouts`).
- inherited defaulted associated `u32` and `Quantity` constants can jointly
  parameterize an HRTB GAT used as the element/result of an indirect callback:
  a structural width expression reaches nominal construction and `Array`
  materialization, then canonical VM decode. A recursive selected width is
  rejected transactionally without changing the legal facade cache, trace, or
  artifact (`service_materializes_const_quantity_gat_arrays_through_hrtb_facade_revisions`).
- defaulted generic associated types and associated effect rows through source
  layout construction, outward-effect checking, handler lowering, VM execution,
  and dependency-interface serialization. The selected local impl may omit both
  associated definitions: `service_lowers_defaulted_gat_type_projections_through_vm_layouts`,
  `service_lowers_defaulted_associated_effect_gats_through_vm_handlers`, and
  `service_imports_defaulted_associated_gats_for_local_layouts_and_effect_rows`
  keep the default-selection path executable end to end.
- inherited associated-item contracts carry their own GAT binder kinds through
  a dependency interface before supertrait evidence is selected. A subtrait
  projection may therefore drive a concrete layout and an outward handler row,
  while an inherited method uses the same instantiated parent edge
  (`service_materializes_inherited_gat_types_effect_rows_and_methods_through_vm`).
- inherited associated constants use that same selected supertrait edge before
  Core materializes a nominal const argument. A reciprocal public-module SCC
  combines the const arithmetic with an HRTB effect callback; ambiguous export,
  recursive const, and overlapping-impl revisions roll back without publishing
  derived interfaces (`typed_core_selects_inherited_associated_consts_for_nominal_arithmetic`,
  `service_rolls_back_const_hrtb_supertrait_cycles_before_publication`).
- an opaque callback can simultaneously select defaulted supertrait type GAT,
  effect-row GAT, and const contracts. Its legal facade executes through the
  VM, while recursive-const and mixed-polarity provider revisions preserve the
  prior artifact and publish neither cache changes nor dependency traces
  (`service_rolls_back_defaulted_supertrait_callback_contract_revisions`).
- a Child-named projection first requires Child evidence; Parent evidence alone
  cannot select its inherited type, effect-row, or const. A negative Child
  implementation remains equally authoritative. Direct solver and Core checks
  cover the three projections together; an aliased HRTB callback then proves
  the positive path reaches the VM while missing, refuted, and mixed-polarity
  revisions cannot publish traces or cache misses
  (`negative_child_trait_refutes_inherited_type_effect_and_const_projections`,
  `parent_evidence_cannot_select_items_requested_through_an_unimplemented_child`,
  `typed_core_refutes_negative_child_inherited_type_effect_and_const_projections`,
  `typed_core_rejects_parent_only_inherited_type_effect_and_const_projections`,
  `service_keeps_negative_child_inherited_projections_authoritative_through_alias_revisions`).
- inherited methods obey the same requested-trait boundary as associated
  items: Parent evidence (including a lexical Parent-only assumption) cannot
  select `Child::method`, and a negative Child implementation cannot enter a
  method-value path. Conversely, a lexical Child assumption can select the
  inherited Parent blanket/concrete implementation rather than being mistaken
  for method-body evidence itself. Reexported `for<'a>` method values are
  checked through canonical source ordering and failed revisions before the
  positive facade is allowed to execute on the VM
  (`inherited_method_selection_requires_the_requested_child_evidence`,
  `child_lexical_evidence_selects_an_inherited_blanket_method`,
  `typed_core_requires_child_evidence_for_inherited_qualified_methods`,
  `typed_core_selects_aliased_hrtb_inherited_method_values_from_child_assumptions`,
  `service_requires_child_evidence_for_inherited_hrtb_method_values_through_facade_revisions`,
  `service_materializes_aliased_hrtb_inherited_method_values_from_child_bounds`).
- a public dependency facade preserves inherited associated effect-GAT
  evidence through a named `for<'a>` callback: the declaration-owned lifetime
  is selectable, its concrete row reaches handler lowering and verified VM
  execution, while the same facade without a selected parent implementation is
  rejected (`service_executes_reexported_hrtb_inherited_effect_gats_through_vm_handlers`,
  `service_rejects_reexported_hrtb_inherited_effect_gats_without_selected_evidence`).
- a declaration-level lifetime-polymorphic named function is checked against
  fresh `for<'a>` placeholders before becoming a first-class callback; the
  callback is then invoked and its returned reference dereferenced through the
  VM (`service_executes_hrtb_function_values_through_reference_returning_calls`).
- contextual compact closures can likewise inhabit an HRTB callback contract:
  their universal value type remains frozen while the lifted closure body uses
  caller-local regions, and an invoked reference result reaches the VM
  (`service_executes_contextual_hrtb_closure_values_through_reference_calls`).
- an HRTB closure's `RunsIn` proof and VM callable ABI open lifetime arguments
  nested in an associated effect-row projection together with its reference
  contract; the concrete projection is exercised through an indirect callback
  call and verified VM execution
  (`service_executes_hrtb_closures_with_concrete_associated_effect_projections`).
- imported callable contracts also normalize a concrete associated effect GAT
  beneath their HRTB binder before named-function value compatibility is
  checked, so the selected callback row reaches direct calls and the verified
  VM rather than remaining an opaque interface projection
  (`service_imports_hrtb_associated_effect_gat_callback_contracts_through_vm`).
- an open generic effect-row tail remains a caller-owned projection in Core
  under its HRTB binder, while a reciprocal public-module facade can select it
  for VM execution. A contradictory negative implementation is rejected as
  mixed-polarity coherence before revision-local cache or interface traces are
  published (`typed_core_freezes_open_hrtb_effect_rows_selected_by_a_positive_trait_impl`,
  `service_rolls_back_mixed_polarity_hrtb_effect_rows_through_recursive_facades`).
- concrete lifetime-GAT projections can be selected beneath an HRTB callback
  binder without treating that rigid item argument as an escaped solver goal;
  the normalized borrowed item flows through a compact closure, dereference,
  and verified VM execution
  (`service_executes_hrtb_closures_with_lifetime_gat_projections`).
- a selected HRTB trait-method value can carry associated type GATs whose
  parameter and result both include the selected associated const. It remains
  valid when stored as an indirect callback and invoked from a closure capture;
  the source artifact and a decoded canonical artifact execute identically,
  independent of facade/provider source order
  (`service_executes_hrtb_gat_const_trait_method_values_through_capturing_closures`).
- generic integer wrappers preserve their operand width through deferred MIR
  materialization: signed right shift remains arithmetic, unsigned right shift
  remains logical, and every count at least the operand width traps rather than
  being masked. `service.rs::generic_integer_shift_wrappers_materialize_signed_unsigned_and_trapping_widths`
  and `service.rs::manifest_bound_generic_int_shift_left_rejects_an_i64_width_count`
  cover both generic and frozen source-to-VM paths.
- contextual decimal literals retain an `f32` expectation through MIR, frozen
  bytecode, independent verification, and manifest-bound floating execution;
  `service.rs::manifest_bound_f32_leaf_accepts_contextual_decimal_literals_through_vm`
  covers the width that cannot reuse an `f64` raw-bit constant.
- exact move-captured closure consumption through local and imported callable
  transfers, including rejection of sequential activation and acceptance of
  mutually exclusive handler-arm transfers.
- source-storage lifecycle at the hostile-MIR boundary: nested lexical exits
  must execute `EndBorrow`, reverse-order destruction, and `StorageDead` in
  order while preserving protected label/effect payloads.
- source-produced ownership/control paths: a handler arm transfers from a
  label after a partial aggregate move while retaining the disjoint field;
  `source_lowering_executes_handler_partial_move_and_label_leave` and
  `service_executes_handler_partial_move_and_label_leave` prove this crosses
  Core, PlaceFlow, frozen MIR, VM emission, verification, and published
  runtime execution.
- deep finite replay reinstates an enclosing irrefutable normal-completion
  arm for every cloned residual path, with fresh completion binders rather
  than a once-only wrapper around the initial performance
  (`service_replays_each_finite_resumption_through_deep_normal_completion`).
  The dynamic facade path extends that guarantee through two refutable
  partial-handler forwards and an imported cancellation: each outer replay
  closes the inactive inner frames before selecting the completion arm
  (`service_replays_nested_facade_cancellation_through_outer_normal_completion`).
  An effectful completion can then cross public facade and provider caller
  frames to an enclosing one-shot handler independently for every replay
  (`service_replays_effectful_completion_after_facade_cancellation_through_outer_resume`).
  Existing service cases separately cover closure/handler captures
  (`service_move_captures_aggregate_roots_for_partial_closure_moves` and
  `service_joins_partial_aggregate_move_captures_across_handler_arms`), while
  `semantic_drop_runs_once_on_normal_and_nonlocal_cleanup` covers custom-Drop
  cleanup through real source compilation.
- a refutable local handler can forward an unmatched performance from an
  imported effectful callable to a still-installed outer one-shot frame; the
  outer resumption result returns through the imported call
  (`service_forwards_a_partial_local_handler_over_an_imported_deep_effect`).
- executable effect-row polymorphism preserves an explicitly instantiated
  `{| e}` callable contract across an indirect named function-value call and
  routes its concrete residual performance through a VM handler; legacy
  `perform`/`with`/`resume` spellings normalize to that same path
  (`service_forwards_an_effect_row_generic_function_value_through_a_vm_handler`,
  `service_normalizes_legacy_perform_and_with_migration_syntax_through_vm_handlers`).
- a public child-module row-polymorphic forwarder preserves its instantiated
  residual effect through interface freezing and an indirect call, so a root
  handler dispatches the child's concrete performance
  (`service_routes_cross_module_open_effect_row_forwarding_through_root_handler`).
- an imported two-operation callable can resume its first one-shot effect,
  then cancel its later effect without leaking the now-inactive earlier
  handler frame (`service_cancels_a_second_imported_operation_after_resuming_the_first`).
- a nested partial replay handler can forward an imported read to an outer
  replay frame; each resumed dependency path then cancels its inner write and
  closes the inactive nested frames before returning to the outer clause
  (`service_replays_a_forwarded_imported_read_then_cancels_its_nested_write`).
- two nested partial replay handlers can forward an effect through a public
  re-export facade and its ordinary caller frame to an outer replay handler;
  each replayed path cancels the inner operation only after closing the three
  inactive lower frames
  (`service_replays_through_two_partial_facade_handlers_before_nested_cancellation`).
- a late refutation in the second payload of a nested partial replay row
  preserves the complete ordered test chain before forwarding through public
  facades to the outer exact replayer; every replayed provider residual then
  cancels its sibling operation
  (`interprocedural_replay_forwards_after_a_late_payload_then_cancels`,
  `service_replays_late_payload_forwarding_then_facade_cancellation`).
- third-payload refutations compose with both nested cancellation and labelled
  re-entrant completion: every partial row retains all three ordered tests
  before forwarding, while public facades preserve the outer replay frame,
  sibling cancellation, retained completion, and label leave
  (`deep_replay_cancellation_checks_all_three_payloads_in_both_partial_rows`,
  `reentrant_replay_checks_a_late_third_payload_before_labelled_completion`,
  `service_replays_late_third_payloads_through_nested_facade_cancellation_and_completion`,
  `service_forwards_a_late_third_payload_through_facade_replay_completion_and_label_leave`).
- a concrete associated effect-row projection normalizes before terminal
  lowering, so a generic terminal operation can cross a normal callee frame,
  be cancelled by its terminal arm, or contribute its final clause result to
  a nested completion that leaves a lexical label
  (`projected_terminal_contract_rejoins_nested_completion_through_a_label`,
  `service_rejoins_a_terminal_generic_callee_through_nested_completion_and_label`,
  `service_intercepts_a_nontransparent_projected_terminal_callee_through_a_vm_frame`).
- a selected concrete associated row also survives a statement-scoped handler
  around both a direct and opaque interprocedural callable: the one-shot
  resumption keeps the dynamic frame installed through the callee return,
  then normal cleanup precedes the enclosing lexical suffix
  (`projected_trait_effect_handler_statements_rejoin_their_lexical_suffix_in_mir`,
  `service_rejoins_a_projected_trait_effect_handler_statement_before_its_suffix`,
  `service_rejoins_an_opaque_projected_trait_effect_handler_statement_before_its_suffix`).
- a projected two-operation row retains its exact replay-frame identity across
  a direct public call and an opaque callable alias: a refutable inner row
  forwards to the outer replay frame, each residual cancels the sibling
  operation, and normal completion executes after that unwind
  (`service_replays_a_projected_multi_operation_row_through_refutable_forwarding_cancellation_and_completion`).

## Previously enabled red semantic cases

The established service suite and focused backend tests keep these semantic
bridges executable:

| Missing semantic behavior | Test |
| --- | --- |
| Transfer in an effect argument exits before the performance | `service_label_transfer_exits_from_an_effect_argument_before_performance` |
| Refutable handler joins normal and label-transfer clauses | `service_refutable_handler_mixes_normal_and_label_transfer_outcomes` |
| Resumption result exits to an enclosing label | `service_resumption_result_may_transfer_to_an_enclosing_label` |
| Immediate closure capture of a resumption | `service_allows_an_immediately_invoked_closure_to_capture_a_resumption` |
| Immediate closure capture of a refinement binder | `service_allows_an_immediately_invoked_closure_to_capture_a_refinement_binder` |
| Trait method materialization with independent impl-head binders | `service_materializes_trait_methods_with_independent_impl_head_generics` |
| Multi-operation resume then cancellation to a label | `service_multi_operation_handler_may_cancel_to_an_enclosing_label_after_a_resume` |
| Partial-handler forwarding to an outer label transfer | `service_partial_handler_forwarding_may_reach_an_outer_label_transfer` |
| Finite replay followed by label transfer | `service_replayed_resumption_result_may_transfer_to_an_enclosing_label` |
| Exact replay through a late refutable forward then generic-label completion, with one protected cleanup | `nested_generic_label_replay_forward_rejoins_completion_with_single_cleanup`, `service_replays_forwarded_multi_payload_operation_then_rejoins_generic_label_completion` |
| Exact replay forwards after a later refutable payload through a public facade, then cancels a sibling operation | `interprocedural_replay_forwards_after_a_late_payload_then_cancels`, `service_replays_late_payload_forwarding_then_facade_cancellation` |
| Three-payload partial rows forward only after their final payload, through nested facade cancellation and labelled re-entrant completion | `deep_replay_cancellation_checks_all_three_payloads_in_both_partial_rows`, `reentrant_replay_checks_a_late_third_payload_before_labelled_completion`, `service_replays_late_third_payloads_through_nested_facade_cancellation_and_completion`, `service_forwards_a_late_third_payload_through_facade_replay_completion_and_label_leave` |
| A concrete projected generic terminal row crosses an ordinary callee frame and separately re-joins a nested completion through a label | `projected_terminal_contract_rejoins_nested_completion_through_a_label`, `service_rejoins_a_terminal_generic_callee_through_nested_completion_and_label`, `service_intercepts_a_nontransparent_projected_terminal_callee_through_a_vm_frame` |
| Cancellation through a public effect facade must retain a move-captured callback's lower-use obligation | `service_rejects_move_capture_cancellation_through_public_facades` |
| A shared-only closure payload is duplicable across an exact `[2,2]` replay handler through public facades | `service_replays_shared_closure_payloads_across_public_facades` |
| A custom-`Drop` aggregate survives partial-handler forwarding and is destroyed exactly once when the enclosing `[0,1]` handler cancels the suspended continuation | `service_drops_a_custom_aggregate_once_across_forward_and_cancellation` |
| Completion after resumption transfers to an enclosing label | `service_completion_after_a_resumption_may_transfer_to_an_enclosing_label` |
| Reentrant replayed completion cancels through nested facades to a branded label | `service_reentrant_completion_cancels_to_label_through_nested_facades` |
| Outer completion leaves while a nested replay has a forwarded dependency continuation | `service_outer_completion_leaves_after_reentrant_forwarded_replay_through_facades` |
| Inner reentrant completion leaves a label while retaining an enclosing normal completion | `service_inner_reentrant_completion_leave_retains_outer_normal_completion_through_facades` |
| A label leave preserves enclosing handlers for a replayed, effectful outer completion | `service_outer_replay_after_inner_label_leave_reenters_effectful_dependency_completion`, `cleanup_leave_preserves_the_lexical_outer_handler_prefix` |
| G1 source boundary rejects deferred non-exact and unbounded resumption quantities such as `[1,2]`, `[0,2]`, and `[1,infinity]` | `service_rejects_deferred_resumption_quantities_at_the_g1_source_boundary` |
| Source-storage cleanup emits ordered actions, excludes protected payloads, ends loans before storage release, and preserves branch-correlated drop-flag erasure | `source_storage_cleanup.rs::mir_requires_ordered_source_storage_cleanup_on_nested_lexical_leave`, `source_storage_cleanup.rs::mir_requires_end_borrow_before_source_storage_cleanup`, `source_storage_cleanup.rs::mir_requires_drop_flag_for_divergent_source_storage_initialization` |
| Executable storage statements check store-before-live, read-after-transfer/death, and replacement without zero-use destruction before VM lowering; true and false `DestroyIf` branches carry equivalent checked VM erasure witnesses. | `mir.rs::mir_rejects_read_of_uninitialized_source_storage_before_vm_lowering`, `mir.rs::mir_rejects_path_dependent_source_storage_initialization_at_a_join`, `source_storage_cleanup.rs`, `vm_storage_erasure.rs`, and `storage_statement_contract.rs` |
| Source assignment lifecycle uses `StorageLive` then Store from an ordinary temporary; overwrite destroys while armed and disarms before replacement; a moved slot reinitializes without a second destroy; lifted mutable captures retain independently frozen addressable slots; and PlaceFlow-branded nonlocal exits emit reverse ordered, payload-protecting source-storage cleanup, including a `Leave` emitted from a handler clause. | `source_assignment_lowering.rs::{source_let_initializer_lowers_as_live_temporary_then_first_store, source_assignment_destroys_an_initialized_place_before_overwrite_store, source_assignment_reinitializes_a_moved_place_without_destroying_an_empty_slot, lifted_closure_assignment_preserves_a_mapped_addressable_capture_slot, source_assignment_leave_emits_reverse_storage_dead_cleanup_after_move_and_reinit, source_leave_protects_reinitialized_owner_payload_before_storage_dead, handler_leave_protects_a_direct_reinitialized_source_owner_payload}` |
| Source-produced storage covers parameters, shadowing lets, partial moves, closure captures, handler payload/resumption binders, completion binders, and nonlocal `Leave` boundaries. | `source_storage_lowering.rs::{source_lowering_preserves_typed_storage_side_table_for_ordinary_lexical_exit, source_lowering_requires_executable_storage_for_payload_and_completion_bindings, source_lowering_requires_lifecycle_storage_for_lifted_closure_bindings}` |
| Source-storage cleanup arena rejects forged lifecycle, local provenance, scope-boundary, and reverse-order records | `source_storage_cleanup.rs::source_storage_arena_rejects_forged_lifecycle_and_cleanup_boundaries` |

## Acceptance condition

The 100% language-semantics gate is green only when all of the following hold:

```text
cargo test -p grandiose-stage0 --test semantic_conformance
cargo test -p grandiose-stage0
```

Every inventory row must remain mapped to an enabled test, every mapped test
must pass, and the ordinary Stage-0 suite must remain green. New normative
semantics must add or extend an executable anchor and update the inventory in
the same change; prose-only claims never count as coverage.
