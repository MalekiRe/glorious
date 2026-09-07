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

## Sixth slice: resolved pattern-name uniqueness

Language §4.3 resolves bare pattern names as structural constants when those
values are in scope; only otherwise do they introduce binders. The body parser
previously counted every bare name as a binder, so repeated Boolean constants
and imported constants failed with G4017 before resolution.

Uniqueness is now checked after structural-constant resolution in pattern
elaboration. Independently elaborated operation payloads also check their
combined clause scope. Actual payload binders still cannot shadow a generated
continuation, for either positional or explicit `with` spelling. Neither
constant names nor Boolean spellings are special-cased in the parser. Cache
generation 26 identifies the changed body/elaboration contract; verifier,
bytecode, language, and interface generations are unchanged.

New tests cover repeated constants in nested tuples, arrays, records, enum
payloads and operation clauses, including imported constants and verified wire
round trips. Negative cases retain rejection of duplicate actual binders,
continuation conflicts, mismatched constant types, and repeated unimported
names. A direct `is` pattern-elaboration test verifies duplicate rejection
without depending on the separate contextual-refinement implementation.

Two parser tests are renamed to reflect deferred name resolution; their
semantic rejection obligations are covered by the pattern/Core and service
tests. The historical frozen compiler oracle and M19 evidence are unchanged.
This slice does not certify `let name` forced-binder syntax, closed Boolean
constant schemes, or the current specification's contextual `Test` carrier.
The new Boolean integration fixtures use explicit subject types to isolate
pattern-name resolution from the remaining unconstrained-tuple inference gap.

The full optimized non-GSC2 run executes 2,549 tests: 2,375 pass and 174 fail.
Four old service failures now pass: exhaustive nested Boolean tuple coverage
and the typed integer comparison regressions for `u8`, `u64`, and `usize`.
All twelve new tests pass. Suite-qualified comparison, accounting for the two
documented parser-test renames, finds no regressions and no missing tests.
The plan-integrity check and all 22 checker tests also pass. This remains a
bounded Stage 0 result, not complete language or self-hosting conformance.

Reproduction uses the same profile and resource guards as the prior baseline:

```sh
CARGO_TARGET_DIR=target/conformance-groundwork CARGO_PROFILE_TEST_DEBUG=0 \
  CARGO_INCREMENTAL=0 CARGO_BUILD_JOBS=2 CARGO_PROFILE_TEST_OPT_LEVEL=1 \
  tooling/test-with-budget.sh tooling/ram-gate.sh \
  cargo test -p grandiose-stage0 --lib --tests --no-fail-fast -- --skip gsc2
```

## Seventh slice: closed Boolean constants

Language §4.3 and library §3 require `true` and `false` to be monomorphic
`Result<(), ()>` values. The distributed library instead declared open
constructor applications, allowing `true` to inhabit `Result<(), E>` and
`false` to inhabit `Option<T>`. Besides admitting invalid programs, those open
parameters prevented inference in otherwise ordinary unannotated aggregates.

Both declarations now supply explicit unit type arguments. This uses the
existing ordinary initializer/type machinery, not compiler recognition of
Boolean names. `None` remains an open structural constant scheme. The two
generic Option lazy-insertion helpers now match their vacant branch with
`None`, not the formerly polymorphic `false` constant. Source fingerprints
identify this library-only semantic change; artifact generations are unchanged.

Six new prelude tests exercise unannotated locals, nested tuples and arrays,
reject incompatible Result types in both expressions and patterns, and retain
independent generic None and constructor instantiations. Positive cases execute
both the original artifact and a verified canonical-wire round trip. Negative
assertions require the type error to originate in the calling source file.
The old `truth_constants_leave_the_absent_variant_polymorphic` boundary test
contradicted the consolidated contract. Its replacement rejects those old
uses and preserves the two generic execution/round-trip scenarios with `None`
and `Result::Ok`; it is an explicit fixture migration, not an ignored failure.
The earlier slice's unannotated Boolean-aggregate inference limitation is
resolved here; forced-binder syntax and the contextual Test carrier remain
outside this work. Unit-payload constructor patterns in the new fixtures use
`_`: direct `()` pattern elaboration remains a separate gap.

Following the explicit request to migrate tests whose semantics are obsolete,
three service fixtures no longer call the VM-predicate `run_bool` helper on a
nominal library Bool. They observe `true`/`false` through an exhaustive source
dispatch and check the resulting integer in both original and verified wire
artifacts. Negation and numeric-comparison/literal tests additionally check
false outcomes. The character/comparison fixture retains its Boolean `!=`
assertion: it now exposes the missing applicable operator implementation,
rather than stopping at the obsolete host-result assumption. It remains a
failure, not a deleted or ignored semantic obligation.

The completed optimized non-GSC2 run executes 2,555 tests: 2,384 pass and 171
fail. Closing the constants fixes the compact-label result-inference test;
the migrated negation and numeric-comparison/literal service tests also pass.
All six new tests pass, as do both existing Option lazy-insertion regressions.
Suite-qualified comparison against the sixth slice, accounting for the one
documented boundary-test replacement, finds no regressions and no missing
tests. The plan-integrity check and all 22 checker tests remain green. No
acceptance-family or self-hosting completion status is changed.

An intermediate rerun exhausted filesystem space and did not complete; it is
not used as full-run evidence. With explicit cleanup permission, `cargo clean
--profile dev --target-dir /home/malek/Projects/grandiose/target` removed
54.2 GiB of reproducible default-profile build artifacts. The separate
`target/conformance-groundwork` build and comparison logs were preserved, and
the complete baseline was rerun using the sixth slice's command and guards.

## Next work

1. Triage the remaining failures after default-prelude selection, separating
   phase-local fixture environments from remaining compiler semantic gaps.
2. Audit fixtures against their current specification obligations. Preserve their
   semantic assertions while updating genuinely obsolete source forms or setup.
3. Re-run the full non-GSC2 Stage 0 baseline after each coherent semantic change;
   compare individual test identities, not only aggregate totals.
