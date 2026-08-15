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
| 20. PlaceFlow and executable lowering | `core.rs` and `mir.rs` cover initialization, partial moves, branch joins, loans, cleanup plans, continuation snapshots, forged-MIR rejection, VM verification, and execution. |

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
