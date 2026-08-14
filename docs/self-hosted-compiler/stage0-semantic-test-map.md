# Stage-0 semantic test map

This is the executable-coverage map for the Rust Stage-0 compiler's language
semantics.  It is derived from the test plans in chapters 13 through 20 of
the self-hosted compiler compendium.  A row names a small set of deliberately
composite tests; it does not require a separate test for every wording in the
specification.

The map excludes optimizer breadth, compiler-service operations, and
self-hosting convergence.  Those are not language-semantics acceptance
criteria for Stage-0.

## Existing semantic acceptance coverage

| Compendium chapter | Combined executable coverage |
| --- | --- |
| 13. Types, normalization, inference | `types.rs`: `unification_is_occurs_checked_and_zonks_body_local_uncertainty`, `occurs_checks_cover_callable_effect_and_nominal_generic_edges`, `open_effect_rows_unify_without_becoming_type_holes`, and the canonical-fingerprint tests cover inference, normalization, kind separation, effect rows, `Never`, and canonicalization. |
| 14. Generics, traits, associated items, GATs, HRTBs, consts | `trait_solver.rs`: the tabled-generic, HRTB, associated-projection, recursive-normalization, and mixed-kind tests; `coherence.rs`: overlap/orphan/negative-head tests; `service.rs`: `service_materializes_generic_trait_methods_with_associated_type_and_const_layouts`, `service_lowers_concrete_associated_effect_gats_through_vm_handlers`, and `service_opens_higher_ranked_callback_lifetimes_without_leaking_them`. |
| 15. Effects, handlers, resumptions, cancellation | `service.rs`: `service_composes_generic_effects_closures_and_finite_replay_across_a_call`, deep residual-stack/replay tests, ordered multi-operation matrix tests, cancellation tests, generic-effect frame tests, and the enabled red conformance cases below. |
| 16. Quantitative ownership | `quantity.rs`: `quantities_distinguish_sequence_exclusive_branches_and_replay` and `principal_use_intervals_accept_only_contained_actual_use`; `service.rs`: callable lower-bound, branch-hull, cancellation, and resumption-replay obligation tests. |
| 17. Regions, lifetimes, borrowing, reborrowing | `core.rs`: PlaceFlow loan/projection/reborrow/escape tests; `service.rs`: unique-reference writeback, nested projection reborrow, NLL through handlers and labels, HRTB leak, and effect-payload escape tests. |
| 18. Callables, captures, brands, environments, refinements | `core.rs`: closure brand/capture/refinement tests; `service.rs`: closure invocation, move capture, callable aggregate, handler payload, and replayed-capture tests, plus the enabled red capture cases below. |
| 19. Typed Core | `core.rs`: frozen-call/effect provenance, Core validation, structural-control, label, pattern, host-primitive, and semantic-fingerprint tests. |
| 20. PlaceFlow | `core.rs`: root/projected place, initialization, partial move, branch join, loan, cleanup, and continuation-snapshot tests; `mir.rs`: independently forged-MIR validation tests. |

## Enabled red semantic conformance cases

These tests are intentionally enabled.  They define required language behavior
that the current implementation rejects or misexecutes; the normal Stage-0
service suite remains red until they pass.

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

## Acceptance condition

Semantic acceptance requires every test above to pass, with no ignored
semantic-conformance tests.  New language semantics must either extend one of
the listed composite fixtures or add a new mapped fixture before being called
implemented.
