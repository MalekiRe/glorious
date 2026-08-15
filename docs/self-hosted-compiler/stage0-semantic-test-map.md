# Stage-0 semantic coverage gate

This directory defines the executable language-semantics gate for the Rust
Stage-0 compiler. The normative source is the generation-1 core specification
in `glorious-branded-environment-core-spec.md`; optimizer breadth, compiler
service lifecycle behavior, and self-hosting convergence remain separate gates.

## Authoritative inventory

`stage0-semantic-inventory.tsv` is the machine-readable source of truth. It has
one row for every explicit normative rule in the core specification's three
acceptance sections:

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
- effect declaration visibility across dependency-package boundaries, including
  direct public perform/handler execution and rejection of a private effect;
- qualified nominal identity for same-named public declarations in separate
  modules, carried through record construction, projection, and VM execution.
- generic dependency effect identity through exact replay and optional
  cancellation, including rejection when the imported handler's concrete
  effect instance does not match the performed one.
- imported reference lifetime relations through a local closure and handler,
  including rejection of a closure escape after the imported call.
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
  Existing service cases separately cover closure/handler captures
  (`service_move_captures_aggregate_roots_for_partial_closure_moves` and
  `service_joins_partial_aggregate_move_captures_across_handler_arms`), while
  `semantic_drop_runs_once_on_normal_and_nonlocal_cleanup` covers custom-Drop
  cleanup through real source compilation.

## Previously enabled red semantic cases

The established service suite also keeps these implementation gaps enabled:

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
| Completion after resumption transfers to an enclosing label | `service_completion_after_a_resumption_may_transfer_to_an_enclosing_label` |
| G1 source boundary rejects deferred non-exact and unbounded resumption quantities such as `[1,2]`, `[0,2]`, and `[1,infinity]` | `service_rejects_deferred_resumption_quantities_at_the_g1_source_boundary` |
| Source-storage cleanup emits ordered actions, excludes protected payloads, ends loans before storage release, and preserves branch-correlated drop-flag erasure | `source_storage_cleanup.rs::mir_requires_ordered_source_storage_cleanup_on_nested_lexical_leave`, `source_storage_cleanup.rs::mir_requires_end_borrow_before_source_storage_cleanup`, `source_storage_cleanup.rs::mir_requires_drop_flag_for_divergent_source_storage_initialization` |
| **Red: executable storage statements.** Every program-point transition is checked: store-before-live, read-after-transfer/death, and replacement without zero-use destruction are rejected before VM lowering; true and false `DestroyIf` branches lower to equivalent checked VM erasure witnesses. | `mir.rs::mir_rejects_read_of_uninitialized_source_storage_before_vm_lowering`, `mir.rs::mir_rejects_path_dependent_source_storage_initialization_at_a_join`, `source_storage_cleanup.rs`, `vm_storage_erasure.rs`, and `storage_statement_contract.rs` |
| **Red: source assignment lifecycle.** A source `Place` initializer must use `StorageLive` then Store from an ordinary temporary; overwrite destroys/disarms the prior resident; a moved slot reinitializes without a second destroy; and lifted mutable captures retain an independently frozen addressable slot. | `source_assignment_lowering.rs::{source_let_initializer_lowers_as_live_temporary_then_first_store, source_assignment_destroys_an_initialized_place_before_overwrite_store, source_assignment_reinitializes_a_moved_place_without_destroying_an_empty_slot, lifted_closure_assignment_preserves_a_mapped_addressable_capture_slot}` |
| Source-produced storage covers parameters, shadowing lets, partial moves, closure captures, handler payload/resumption binders, completion binders, and nonlocal `Leave` boundaries | `source_storage_lowering.rs::{source_lowering_preserves_typed_storage_side_table_for_ordinary_lexical_exit, source_lowering_requires_executable_storage_for_payload_and_completion_bindings, source_lowering_requires_lifecycle_storage_for_lifted_closure_bindings}` (last two red until lowering gives every source binding executable lifecycle storage and drop-flag transitions) |
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
