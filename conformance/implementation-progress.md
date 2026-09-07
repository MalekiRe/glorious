# Stage 0 implementation progress

The consolidated specifications remain authoritative. This log records bounded
implementation work, not completed acceptance families or overall conformance.
The scenarios in `cases.tsv` remain planned until their complete required
execution and evidence contracts are implemented.

## Baseline after module cleanup

The Stage 0 library and integration tests, excluding the 60 GSC2 tests, executed
2,484 tests: 1,958 passed and 526 failed. The cleanup preserved every individual
test result. This is not a workspace-wide or self-hosting acceptance result.

Initial triage groups failures by their first reported diagnostic other than
the recovered-Core summary diagnostics G7007/G4182. These are symptom buckets,
not independently established root causes; one fix may uncover another failure.

| First diagnostic group | Failing tests | Investigation |
| --- | ---: | --- |
| G4108/G4111: operator grouping or missing fixity | 362 | Resolved library operators, selected prelude, and phase-local fixtures |
| G3304: unresolved type | 71 | Library type visibility and missing source/profile inputs |
| Other diagnostics or assertion/runtime failures | 93 | Ownership, refinements, backend contracts, and individual surface cases |

Language §2.5 requires a selected default prelude at lowest import priority.
At that baseline, the service only attached its distributed library when source explicitly
mentions `std`; this is an implementation gap, not grounds for assuming every
missing `Bool` or operator is an obsolete fixture. Phase-local parser/Core tests
also need deliberate source environments. Fixing this area must respect
`no_std`, `no_implicit_prelude`, explicit imports, package authority, and the
selected profile rather than installing hard-coded operator/type fallbacks.

## First slice: positional effect payloads

Language §10.1 and the §19 operation grammar specify positional payload types.
The effect header parser previously routed these through named function
parameter parsing and rejected `effect Exit { exit(i64) -> i64; }` with G3203
and G3207. It now parses operation payloads separately, retaining ordered types
and spans without treating borrowed payloads as method receivers. Handler arms
continue to introduce their own bindings.

Coverage added:

- Header parsing of generic, qualified, borrowed, tuple and callable types,
  trailing commas, empty payload lists, omitted unit results and terminal results.
- Rejection of unnamed ordinary function parameters: this change does not relax
  the function declaration grammar.
- Execution and verified wire round trips for generic ordered payloads, explicit
  borrowed lifetimes, tuples/callables and terminal operations.
- A payload type mismatch still produces the operation-specific source error.

The existing `semantic_canonical_callable_surface_and_compact_labels_execute`
regression now passes. No old failure was ignored or changed into an expected
failure. The full non-GSC2 run now executes 2,491 tests: 1,966 pass and 525 fail.
Comparing suite-qualified test identities shows exactly one old failure fixed,
seven new passing tests, no missing tests and no regressions. The 22
conformance-plan checker tests also pass.

This is not full effect conformance: contextual family inference,
operation constraints/imports, continuation quantities and the other §10
requirements still require their own acceptance work. Previously accepted
named operation headers are unchanged in this slice; legacy-syntax disposition
has not been certified against the consolidated grammar.

Focused checks:

```sh
cargo test -p grandiose-stage0 --test header --test positional_effects
cargo test -p grandiose-stage0 --test semantic_conformance \
  semantic_canonical_callable_surface_and_compact_labels_execute
tooling/test-with-budget.sh python3 tooling/conformance_check.py --check
```

Use the repository's time/RAM limits for broad runs. The plan-integrity check is
green; it explicitly reports that semantic conformance is not established.

## Second slice: explicit-import priority

Language §2.3 gives explicit imports priority over glob candidates. The resolver
previously combined both groups, so an explicit selection could become ambiguous
merely because a glob exposed a different declaration under the same name.

Value/type/trait/effect/operator lookup and qualified module-alias traversal now
resolve explicit candidates first. Only an absent candidate in the relevant
namespace permits glob lookup. Ambiguity and inaccessible explicit targets stay
errors; priority never grants the importing module's authority to an outside
requester. Source-order independence and benign import-cycle handling remain
part of the resolver contract.

The new `import_priority` suite covers namespace-specific selection, module
aliases, public reexports, explicit and glob ambiguity, privacy failures,
cross-namespace fallback, and actual execution plus verified wire round trips.
The full non-GSC2 run executes 2,500 tests: 1,975 pass and 525 fail. All nine new
tests pass; every pre-existing suite-qualified test result is unchanged, with
none missing or ignored. The plan-integrity gate also remains green.

This is prerequisite resolution work for the default prelude; automatic prelude
injection and the opt-out attributes are not implemented by this slice.

## Third slice: distributed default prelude

Ordinary service requests now attach the distributed standard-library source
without requiring a textual `std` reference. Its source-owned `std::prelude`
exports are selected at lowest lexical priority. Local and explicit bindings
still win, and qualified lookup does not turn implicit imports into exports of
user modules. Explicitly supplied standard packages are respected; a closed
runtime manifest is not silently expanded.

Leading `#![no_std]` and `#![no_implicit_prelude]` attributes are scanned from
lossless tokens and retained on interfaces. Opt-outs inherit through nested
modules; `no_std` on the request root suppresses automatic library attachment,
while `no_implicit_prelude` preserves explicit dependency access. Comments and
string contents do not select profiles. Invalid attributes produce source
diagnostics, and scanner diagnostics now reach the service instead of being
discarded during interface collection.

Incremental interface fingerprints include the selected prelude's public
contract. Resolved public re-export cycles retain all component source inputs
and outgoing interface dependencies without inserting cyclic product-ledger
edges. Regression coverage checks both application-private and provider-private
edits remain green, while public provider changes invalidate dependent contracts.
The general dependency ledger still rejects unresolved product cycles.

Fixture migrations preserve semantic assertions: phase-local library tests
explicitly opt out of the default prelude; bootstrap convergence budgets include
the actual distributed source length; rollback checks cover application and
library packages; diagnostic provenance uses the prepared input world; and an
orphan-coherence fixture no longer contains an invalid trailing declaration
semicolon. No runtime primitives or wire-format semantics were added. Language,
interface, and cache generations were advanced for the changed source semantics.

This implements the distributed profile's existing library surface, not every
standard-library API or future core/alloc profile. Full language and self-hosting
conformance remain unestablished.

The complete comparable non-GSC2 run executes 2,518 tests: 2,329 pass and 189
fail, down from 525 failures before this slice. Suite-qualified identity
comparison confirms 336 old failures fixed, 18 new passing tests (16 prelude
integration tests and two dependency-component unit tests), no regressions, and
no missing tests. All 14 regressions exposed by the initial prelude run were
repaired before this comparison. The existing semantic-conformance target
improves from 25 passing / 13 failing to 36 passing / two failing; the standard
library target passes all 175 tests. The 22 plan-checker tests and the
plan-integrity gate also pass. Acceptance families remain planned.

The comparable broad baseline uses optimized test binaries:

```sh
CARGO_TARGET_DIR=target/conformance-groundwork \
CARGO_PROFILE_TEST_DEBUG=0 CARGO_INCREMENTAL=0 CARGO_BUILD_JOBS=2 \
CARGO_PROFILE_TEST_OPT_LEVEL=1 \
tooling/test-with-budget.sh tooling/ram-gate.sh \
cargo test -p grandiose-stage0 --lib --tests --no-fail-fast -- --skip gsc2
```

A separate unoptimized debug run reached its time limit and also exposed a
native-bridge process stack overflow in
`callbacks_share_native_allocation_domain_and_bound_native_stack_reentry`.
All 28 native-bridge tests pass under the optimized baseline settings. The
debug-profile stack exhaustion is not fixed or established as pre-existing by
this slice; it must not be counted as a successful debug-profile acceptance run.

## Fourth slice: provably unused optional resumptions

Language §10.6 permits discarding an optional `[0,1]` continuation and requires
cancellation of its captured residual. A named but unused token previously
reached Runtime MIR as normal handler completion. The independent VM verifier
correctly rejected that instruction while a continuation was still pending.

Cleanup MIR now derives a conservative no-reference fact from its own concrete
operands. Runtime lowering uses the existing cancellation instruction and the
sealed surviving-frame cleanup plan for those optional tokens. The proof does
not use source names or direct-call counts: reads, aliases, invocation operands,
and closure captures all prevent classifying the token as unused. Required-use
contracts remain source errors. No verifier rule, VM schema, or runtime primitive
was relaxed; cache generation 24 invalidates artifacts from the old lowering.

Eight integration tests cover verified execution and wire round trips, skipped protected
suffixes, cancellation without normal completion transformation, callee-frame
unwinding, distinct operation/handler result types, invocation and alias guards,
the required-use rejection, and exactly-once destruction of a callee's owner.
Two graph-level tests check reference classification and the required-use guard.

The full optimized non-GSC2 baseline now executes 2,528 tests: 2,340 pass and
188 fail. The previously failing
`service_allows_an_explicit_unused_affine_direct_resumption` now passes; all ten
new tests pass. Suite-qualified comparison against the prelude baseline finds
no regressions and no missing tests. The 22 plan-checker tests and plan-integrity
gate remain green, without changing any acceptance family's planned status.

This is deliberately not general path-sensitive optional-resumption support.
An aliased-but-uninvoked token is conservatively excluded, as are conditional
zero-or-one invocation paths and unresolved nested handler-state issues. Those
remain separate semantic work, not permission to weaken verification.

## Fifth slice: deep handler verification contexts

Language §10.5 requires deep handlers: a resumed continuation may perform the
same operation again and re-enter the same clause. The machine verifier kept
only one incoming state per instruction, so it rejected the initial clause
entry and a later resumed entry as incompatible return contexts.

The verifier now keeps separate incoming states for ordinary execution and
resumption-return contexts, including their permitted handler brands. Within
each context, ordinary CFG joins still check the same register initialization,
ownership, provenance, and handler-stack constraints. Static analysis tracks
whether a return belongs to a resumption, not an ever-increasing dynamic depth.
Reinstalling an already live brand and restoring duplicate live brands remain
errors rather than creating unbounded distinct return-context keys.

Additionally, `ResumeReturn` now audits every suspended suffix reaching a shared
clause, instead of choosing the first one. Each completion must satisfy every
applicable resumption result ABI. This is a verification change, not a new
runtime primitive or wire format; verifier generation 21 and cache generation
25 distinguish it from the earlier implementation.

Nine new integration tests cover three-site and twelve-site re-entry, ordered
pattern forwarding, clause suffixes returning through their own resumptions,
optional cancellation, and verified wire round trips. Hostile variants reject
uninitialized reads and wrong completion types in later resumed suffixes,
duplicate live-brand installation, and incompatible ordinary handler-stack
joins. General captured-resumption support across callable frames and other
remaining handler gaps are not certified by this slice.

The full optimized non-GSC2 baseline executes 2,537 tests: 2,359 pass and 178
fail. Ten old service failures are fixed, including repeated one-shot dispatch,
Boolean pattern coverage, three-deep forwarding/replay, aliased inner snapshots,
and optional cancellation before later performances. All nine new tests pass;
suite-qualified comparison finds no regressions and no missing tests. The
plan-integrity gate and all 22 checker tests remain green. These results do not
establish complete language, standard-library, or self-hosting conformance.

## Next work

1. Triage the remaining failures after default-prelude selection, separating
   phase-local fixture environments from remaining compiler semantic gaps.
2. Audit fixtures against their current specification obligations. Preserve their
   semantic assertions while updating genuinely obsolete source forms or setup.
3. Re-run the full non-GSC2 Stage 0 baseline after each coherent semantic change;
   compare individual test identities, not only aggregate totals.
