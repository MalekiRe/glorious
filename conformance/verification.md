# Groundwork verification — 7 September 2026

Baseline before these test/documentation changes: `ac69a403` on `master`.
No production compiler, VM, runtime or standard-library implementation changed.
This record is not a full workspace test run or a conformance certificate.

## Plan gate

```sh
tooling/test-with-budget.sh python3 tooling/conformance_check.py --check
tooling/test-with-budget.sh python3 -m unittest discover -s tooling/tests -p 'test_conformance_check.py'
```

The plan audit passes: 191 families (48 language, 96 library, 47 supplemental),
573 positive/negative/boundary scenario slots, 597 routed prose/list/table/code
review units, 34 expansion matrices and 20 candidate regression links.
The slots and review units are **not counts of implemented semantic tests**.
All families are explicitly planned. The scalar expansion enumerates all 588
As/TryAs/ExactAs source/destination cells before value/backend/target expansion.

The audit has 22 passing tests, including mutations for missing checklist
coverage, unowned prose sections, invalid matrices, missing conversion cells,
fake passing status, stale spec hashes and missing/non-test/ignored anchors.
CLI output and the deliberately failing readiness check are also tested.

`python3 tooling/conformance_check.py --require-complete` exits 1 as required:
there is no per-scenario/profile execution evidence yet. CI uses plan integrity,
not this unfinished semantic readiness gate.

## Rust regression harness

The deleted-specification `include_str!` dependency is removed. The old
48-entry index now checks its own regression anchors, not old normative prose.
Current specification coverage is audited independently above. Two callable
surface fixtures now use intended `fn` and unit/effect omission spellings;
the compact-label fixture also uses positional effect payload syntax and avoids
an unrelated undeclared arithmetic operator.

Commands (debug information disabled to avoid recreating the previous large
temporary build cache; build products remain under the ignored `target/`):

```sh
CARGO_TARGET_DIR=target/conformance-groundwork \
CARGO_PROFILE_TEST_DEBUG=0 CARGO_INCREMENTAL=0 CARGO_BUILD_JOBS=2 \
CARGO_PROFILE_TEST_OPT_LEVEL=1 \
tooling/test-with-budget.sh tooling/ram-gate.sh \
cargo test -p grandiose-stage0 --test semantic_conformance \
regression_inventory_is_total_enabled_and_machine_checkable -- --exact

CARGO_TARGET_DIR=target/conformance-groundwork \
CARGO_PROFILE_TEST_DEBUG=0 CARGO_INCREMENTAL=0 CARGO_BUILD_JOBS=2 \
CARGO_PROFILE_TEST_OPT_LEVEL=1 \
tooling/test-with-budget.sh tooling/ram-gate.sh \
cargo test -p grandiose-stage0 --test semantic_conformance --no-fail-fast
```

The target builds. Its inventory test passes independently. The full target
reports **24 passed, 14 failed, 0 ignored** across 38 tests; Cargo exits 101.
The canonical unit/effect omission fixture passes. The failures are:

| Module | Test suffix after `semantic_` |
| --- | --- |
| backend | multishot_resumptions_reject_unique_and_label_captures |
| ownership | callable_brands_and_runs_in_evidence_are_fresh_and_sealed |
| ownership | drop_runs_once_on_normal_and_nonlocal_cleanup |
| ownership | optional_move_capture_copies_a_duplicable_source |
| ownership | optional_move_capture_forces_an_owned_closure_environment |
| surface | canonical_callable_surface_and_compact_labels_execute |
| surface | capturing_callable_runs_in_its_compiler_generated_environment |
| surface | contextual_blocks_follow_fn_constraints_not_names |
| surface | named_function_implicit_labels_are_fresh_per_activation |
| surface | nested_generic_labels_forward_ordered_multi_payload_rows |
| surface | nested_generic_labels_rejoin_after_refutable_forwarding_and_completion |
| surface | only_struct_and_enum_are_nominal_declaration_spellings |
| surface | runs_in_borrowed_access_matches_sealed_capture_authority |
| surface | source_defined_conditional_is_an_ordinary_selector |

The updated compact-label fixture exposes a current header-parser gap:
`effect Exit { exit(i64) -> i64; }` produces `G3203` (expected a colon after a
parameter name) and `G3207`. The intended specification uses positional payload
types. The test remains enabled and red; the expectation was not weakened to
preserve the old named-payload syntax.

Other failures include unresolved Bool, missing operator fixity in fixtures
that do not supply their library dependencies, and rejection diagnostics that
do not reach the ownership reason the test intends to exercise. They require
fixture/dependency and semantic triage. In particular, a rejection caused by
an unrelated missing operator is not evidence that an ownership rule works.
This run does not classify all fourteen as compiler defects or as obsolete tests.

The older broad 1,101/15 result and the source-compiler fixture results are
different suites, not rerun or relabeled as this run. No LLVM/native conformance,
full standard-library implementation, whole-workspace green result or repaired
compiler behavior is claimed here.
