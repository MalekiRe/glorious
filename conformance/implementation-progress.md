# Stage 0 implementation progress

The consolidated specifications remain authoritative. This log records bounded
implementation work, not completed acceptance families or overall conformance.
The scenarios in `cases.tsv` remain planned until their complete required
execution and evidence contracts are implemented.

## Cache 78 checkpoint: mixed execution and known release regression

Integrated `3938cdd9`: generated LLVM/VM ordinary-call partitions preserve
arguments, results and reference addresses through ABI version 2. All 12 LLVM
native, 29 native-bridge and 22 request/revision tests pass in the integrating
tree (`target/integration-mixed-native-v2.log`). Cross-engine mandatory tails,
callable/effect exports and full native conformance remain outside this subset.

Cache generation 78 preserves an explicit `ReleaseAvailable` Core operation
and rechecks its exact lexical Environment/affine evidence. Both frozen release
test groups pass, and the all-target check passes. This is an incomplete
checkpoint: executable lowering currently rejects that operation too early,
so the lawful generic availability-release semantic test fails with G6001.
The focused run passes 37 of 38 semantic-conformance tests, all six conditional
drop groups and all ten minimum-use groups (`target/available-release-focused-v1.log`).
Do not treat this checkpoint as a green semantic-conformance build.

The inherited effect-projection ambiguity diagnostic now passes its targeted
recheck (`target/integration-ambiguity-final-v3.log`); the complete service suite
has not been rerun since the preceding 890/1 result. Newer callback-contract
and reference-array follow-ups on agent branches are not part of this checkpoint.

## Ownership, borrowed-array and generated-native integration

The bounded crate split extracts `grandiose-compiler-base` and
`grandiose-syntax`, leaving semantic analysis and execution in the integrating
stage-zero crate. Workspace/all-target checks and 124 boundary/leaf tests pass;
public stage-zero module paths remain compatibility re-exports. The single
selected local Rust profile is LLVM O1 (`tooling/cargo-fast.sh`).

Integrated `ead059f9`, `a204b869` and `470392c5`: opaque generic data captures
transfer ownership unless lexical evidence permits copying or establishes a
callable capability; borrowed array completion patterns observe resident
shells; runtime fixed-array transfers check concrete element/extent contracts.
Older test fixtures now discharge linear residents and declare zero-use
permissions where their generic bodies discard values. The complete focused
ownership/array batch passes 427 tests (`target/integration-ownership-array-v1.log`).

Integrated `e7a3469f`: compact, copy-on-write reference-origin sets and in-place
verifier joins preserve the same may/must facts. Integrated `4d00bb15`: the first
generated LLVM backend checkpoint, with an explicit trusted toolchain/loading
boundary and fail-closed instruction admission. Its verification batch passes
502 tests (`target/integration-native-verifier-v1.log`), including six generated
native execution/ABI groups, all 17 mandatory-tail groups, 29 bridge groups and
180 VM verifier groups. These batch counts overlap in library unit tests.
Generated LLVM-to-VM calls, callable/effect exports and full native conformance
are not included; see `docs/stage0-native-llvm.md` for the admitted subset.

The latest completed combined service recheck reaches 890 passing / 1 failing
test, and all 98 signature tests pass (`target/integration-contract-final-v2.log`).
Concrete outlives tautologies are now removed from implementation-contract
comparison without using the contract's own assumed predicates. The remaining
failure checks the exact wording of the inherited effect-projection ambiguity
diagnostic; its follow-up is under verification. A completely green service
run is not yet claimed. Semantic fixture follow-up `b0351665` is integrated;
the `Available<E>` release/minimum-use proof conflict remains open.

## Conditional destructor shells and generic wrapper normalization

Cache 77 integrates `b5fb972e`: a conditional custom destructor protects the
whole initialized shell even when its condition is not yet decidable in a
generic template. Implicit and explicit consuming projections, nested record,
tuple, array and effect-payload patterns are checked again after Core freezes.
Concrete unselected hooks still permit deconstruction; selected hooks execute
once across ordinary, label, terminal-effect and cancelled-continuation cleanup.
The six conditional-drop groups pass, including fresh/decoded O0/O2 execution.

Implementation bodies can now normalize associated types and rows on rigid
structural subjects such as `Wrapper<I>`, using only solver-proven lexical
predicates. Abstract subjects remain symbolic. Qualified generic method calls
retain inherited supertrait evidence instead of requiring an exact explicitly
listed bound. Callee and application result contracts share the normalization,
including mandatory recursive tail transfers. Associated-row subset matching
uses exact subject identity or a unique successful transactional candidate;
it cannot equate two distinct rigid subjects merely because their item names
match, nor leak failed candidate bindings or guess an ambiguous row operand.

The preceding combined regression batch passes 419 tests
(`target/rigid-drop-broad-v1.log`). The final focused nominal/row/type batch
passes 55 (`target/rigid-inherited-unions-v3.log`), including missing-bound and
omitted-row negatives, inherited methods, generic recursive tails, and row
inference isolation. The latest completed iterator check reaches eight
diagnostics (`target/rigid-iterator-v4.log`, down from 35 after explicit
referent assignments); this is not a passing source root.

The full service run completed with 849 passing and 42 failing tests in
579.91 seconds (`target/nominal-minimum-service-v1.log`), before the ownership,
fixture and native integrations recorded above. That run is historical, not
the latest integration result.

## Nominal declaration contracts and integrated minimum-use enforcement

Cache 76/interface 18 retain nominal `where` predicates through parsing,
elaboration, alias normalization, imported declarations, constructor aliases,
and native source-contract fingerprints. Struct/tuple-struct/enum fields are
checked under their own lexical evidence. Every instantiated nominal type,
including one with no projection fields, must establish its substituted trait,
associated equality, outlives and supported universal requirements. Frozen Core
and PlaceFlow receive the exact callable or implementation/method evidence;
it is not granted globally. Detached frozen equalities are rejected. Nominal
domain recursion and proof work remain bounded.

Integrated `08110256`: ordinary owners now have minimum-use obligations distinct
from callable invocation quantities. Branches, lexical scopes, constructor
shells, partial moves, overwrites, abandoned strict operands and continuation
cancellation retain the obligations of every surviving owner. Only the exact
manifest-bound abort primitive has no cleanup continuation. `Vec::insert`
now returns `Result<(),Rejected<T,BoundsError>>`, retaining rejected input as
the standard-library specification requires. Its error carriers live in the
base library, and the impossible VecDeque insertion failure aborts. Previously
invalid positive fixtures now explicitly consume their linear owners or state
the actual zero-use bound. The linear-array regression is active, not ignored.

Verification checkpoints: 221 combined minimum-use/array/reborrow/mutable/library
tests pass (`target/merged-minimum-use-v1.log`), including all 175 bootstrap
library tests and nine fixed-array tests. The broader Core/header/signature/
trait/coherence/higher-ranked/native/revision run passes 573 tests
(`target/nominal-contract-broad-v1.log`), before the final richer frozen-context
reconciliation. The final targeted run passes 49 header, seven nominal-contract
and 22 revision tests (`target/nominal-contract-final-v1.log`); two new hostile
contract/fingerprint unit tests also pass (`target/nominal-contract-units-v1.log`).
All-targets checking passes with the pre-existing 26 Core fixture warnings
(`target/nominal-minimum-all-targets-v1.log`). The complete service run
(`target/nominal-minimum-service-v1.log`) has reported additional G5024 failures
and is not passing. Two isolated reproductions confirm these concern retained
ordinary owners and refinement carriers; the ownership agent is distinguishing
invalid older fixtures from false rejections. They have not been waived.
Bytecode 71/verifier 34/schema 115 are unchanged.

The real iterator root clears the previous G4190 nominal-field barrier and
reaches 60 later diagnostics (assignment receiver forms, associated result/row
normalization, reference provenance, tail carriers and possible cascades),
recorded in `target/nominal-iterator-v1.log`; it is not a passing library root.
The combined I/O run built under Rust LLVM opt1 in 77 seconds but then exhausted
the 590-second total test budget, exiting 143 without a semantic result
(`target/merged-io-llvm1-v1.log`). This is not proof of a hang or success; its
remaining compile/verification/runtime cost needs isolation.

At the user's explicit request, all three agents continue on full callable/
environment semantics, conditional Drop/reference-array ownership, and actual
LLVM-generated Glorious execution/shared-ABI work. Root owns declaration
contracts and integration. General quantified projection domains and
non-lifetime binders remain unfinished; no overall completion is claimed.
The shared agent baseline is snapshot `804b0fc7` (`agent-baseline/cache76`),
created with a separate Git index. It does not move the user's master branch
or change their staged edits, and is not a claim of a regression-free compiler.

## Earlier checkpoint: quantified user-trait integration and combined library rechecks

Integrated `fdf1e948`: lifetime-universal user-trait predicates now survive
function and implementation contracts, lexical forwarding, and exact
associated type/effect equalities. Nested proof scopes use fresh rigid regions,
isolated environments and a shared bounded query budget; ordinary chosen-region
calls can eliminate lexical universal evidence. Cache 75/interface 17 retain
the new implementation predicates; bytecode 71/verifier 34/schema 115 are
unchanged by this source-contract work.

The combined Core/signature/trait-solver/coherence/higher-ranked/revision run
passes 496 tests (`target/merged-quantified-v1.log`). Five quantified unit tests
pass (`target/merged-quantified-identity-v1.log`); that command's name filter
excluded revision tests, which were rerun separately after the generation bump
and pass all 22 (`target/merged-quantified-revision-v2.log`). All-targets checking
passes with the existing 26 unused-variable warnings in Core test fixtures
(`target/merged-quantified-all-targets-v1.log`).

The real binary-library source root now compiles, verifies decoded bytecode,
and executes successfully with the combined verifier in 8.88 seconds
(`target/merged-binary-v1.log`). Iterator rechecking exposed a missing `T: 'a`
requirement in the four `SliceIter<'a,T>` trait implementations; adding it
clears G4305. The remaining G4190 errors identify a distinct compiler gap:
nominal declaration `where` predicates are not retained in `ParsedHeader` or
`ElaboratedHeader`, and field projection validation receives empty evidence.
`Peekable<I>` and `Zip<I,J>` therefore lose their declared iterator bounds.
The enhanced projection diagnostic includes its subject so independent missing
obligations are not collapsed (`target/merged-iterator-v3.log`). Full nominal
contract preservation, scoped field validation and application enforcement
are required; simply skipping the field check would not fix this gap.

Quantified `RunsIn`, borrowed/stored callback invocation, general quantified
projection-domain validation, and non-lifetime higher-ranked binders remain
unfinished. Minimum-use enforcement is still an isolated agent follow-up.
No full source-matrix or overall conformance acceptance is claimed.

## Earlier checkpoint: completed agent integration of fixed arrays and final-label tails

Integrated `385cfa59` (fixed arrays) and `057e8227` (final lexical/named-label
tail discharge), preserving the already integrated provenance and associated
contract changes. Fixed arrays retain their distinct type and checked length,
sparse pattern indices, compact native layout, zero-sized ownership state,
and independently checked layout-overflow rejection. `Vec::finish_empty`
releases its allocation then forgets the consumed empty owner, preventing
the conditional Drop hook from releasing it twice.

Reconciliation added fixed-array traversal to the new associated/outlives
contract checks and retained callback/label provenance verification. The
combined code exposed an opaque-carrier scalar assignment rejection in the
array conversion helper; scalar resident writes now preserve reference
metadata while still evaluating computed reference operands. Reference-
bearing writes continue to require their sealed provenance path. A dedicated
O0/O2 fresh/decoded regression exercises this interaction.

Cache 74/interface 16/bytecode 71/verifier 34 and VM schema 115 invalidate
older artifacts: sparse array patterns change an existing wire payload.
All-targets checking passes (`target/merged-agents-all-targets-v2.log`).
The combined parser/Core/control/handler/tail suites pass 343 tests
(`target/merged-labels-regressions-v1.log`). The combined array, memory, VM,
contract, and revision run passes another 444 tests, with one known ignored
case (`target/merged-agents-regressions-v2.log`); the focused array-contract
tests and scalar-carrier regression also pass. The first combined array run exposed
the scalar assignment issue and is retained as a failing pre-fix checkpoint.

One explicitly ignored fixed-array regression still records the general
unused named exact-linear owner gap; it is not counted as acceptance. Native
regressions use `RUST_MIN_STACK=33554432` because the pre-existing deep generic
layout test exceeds Cranelift's default test-thread stack. Quantified callback
work and minimum-use enforcement are separate active follow-ups. Reference-
bearing array paths and conditional custom-Drop deconstruction still require
further conformance work. Binary and I/O require combined-source rechecks
against the newly integrated label-tail and VM-provenance changes.

## Earlier checkpoint: local-label transfer, callback invocation, and two integrated compiler lanes

Cache 73/interface 15/verifier 33 add executable must-proofs for local label
transfers and higher-order callback invocation. A forwarding shim must match
its complete executable behavior, including frame cleanup. Its actual local
label destination re-enters verifier dataflow; may-label taints, mixed
callable/label joins, address-exposed slots, and opaque forwarding paths do
not gain this authority. Callable invocation and destruction have separate
proofs, with conditional call-graph summaries, intersection at joins, and
mutation invalidation in live/saved continuations. No source name, safety
annotation, or closure's mere frame-independence certifies invocation.

Integrated provenance commits `d79407dd`/`08aa4d6b` and associated-contract
commit `c027c607`: stored-reference paths retain dereference/field offsets
and storage identity; expected unique references become child reborrows;
implementation methods own their lexical exit labels; result-region
forwarding stays explicit. Associated-item selection retains domain/result
bounds and scoped type/region outlives evidence through calls, projections,
coherence, and source-call fingerprints.

Evidence so far: the initial merged provenance run passed 247 tests
(`target/merged-provenance-label-v1.log`). The combined associated/provenance
run passed 517 tests (`target/merged-contracts-regressions-v1.log`), and
all-targets checking passed. The broader pre-contract service run passed
889/890 service tests and 319 other tests; the recursive generic supertrait
facade case reported G4147 (`target/merged-provenance-label-broad-v1.log`).
Follow-up `e16a9250` fixes associated-const selection by distinguishing lexical
membership evidence from a selectable implementation. That complete focused
service case now passes in main (`target/merged-supertrait-const-v1.log`,
13.09 seconds); the entire service suite has not been rerun since this fix.

The full float parser passed source compilation and decoded verification
with the initial callback proof, then hit the execution harness's cumulative
16,777,216-element allocation limit (`target/tail-callable-float-v1.log`).
It is not counted as a passing source root. After subsequent mutation-proof
tightening, reduced `float_tail` coverage compiles, verifies decoded bytecode,
and executes nonzero `1.5` parsing and `1x` error detection successfully
(`target/tail-float-smoke-v2.log`, 221.17 seconds). No new complete source
matrix is claimed; the previous 10-pass/20-fail matrix is historical.
The final targeted mutation/label/callback checks pass 27 runtime-memory,
180 VM, and 22 revision tests (`target/tail-label-callback-final-v2.log`).
This includes direct and generic callback mutation rejection in fresh and
decoded bytecode, with the corresponding pure callbacks executed successfully.

Fixed-array integration is still pending. At the user's renewed request,
all three worker slots are active on arrays, quantified callback contracts,
and binary/I/O blockers. General positive-use enforcement and conditional
custom-Drop deconstruction remain explicitly tracked gaps, not waived rules.

## Earlier checkpoint: lexical label disposal and isolated implementation work

Cache 72/verifier 32 distinguish disposing a lexical label from running a
closure destructor. `MakeLabel` establishes that disposal owns no capture
environment, while the live label remains frame-dependent and cannot become
a tail carrier. The reduced bytecode test fails with G7042's underlying
`UnprovenTailCarrier` before this change
(`target/tail-label-disposal-before-v3.log`) and passes afterward in both
fresh and decoded programs. The final focused run passes all 178 VM and 22
revision tests (`target/tail-label-disposal-final-v6.log`). Earlier v1/v2
reproduction builds had fixture type errors; v5 retained one stale generation
assertion, corrected in v6. This does not yet prove the full float parser:
generic early-return label invocation remains an unknown indirect mutation
boundary in helper summaries.

At the user's request, three isolated Astra worktrees implement fixed arrays,
associated-item/outlives contracts, and remaining source reference provenance.
Their changes are not yet integrated or counted as main-worktree completion.
The main Cargo target was cleaned at the user's request; build artifacts are
regenerable and the top-level diagnostic logs were preserved.

## Expected reborrows, lexical implementation contracts, and library integration

Cache 71/verifier 31 add explicit expected shared reborrows of unique
references, retaining referent places and loan origins through direct,
generic, computed, and returned-reference calls. This is not automatic
borrowing of a bare owner, shared-to-unique conversion, or permission to
extend local storage. Call argument inference aligns open regions before
unifying element types; a contextual byte literal can therefore recognize
an already-inferred `u8` slice despite its unresolved region. The Path source
test now compiles, verifies, and executes (`target/library-path-v4.log`).

Implementation method contract normalization now uses isolated lexical
trait and associated-equality assumptions from its enclosing implementation.
Generic I/O wrappers no longer fail the four previously reported G4147 row
checks. Later reference, callback, and ownership errors remain. Library
source dependency closures, public test error paths, and String-to-Str byte
views are corrected. Ordinary structural Eq implementations for unit and
Result supply Bool equality without a compiler alias exception; the expanded
foundation source test passes (`target/library-foundation-v1.log`).

The VM verifier separately tracks independence of a reference's address
graph and of its typed referent contents. Helper summaries are reconstructed
from executable code. Replacing borrowed local storage invalidates referent
facts, including facts in saved continuations; raw pointer casts cannot
inherit the weaker typed-reference proof. The hostile replacement regression
initially exposed a missing Store invalidation, now fixed. This precision
improvement does **not** finish floating parsing: the current failure is
localized to `float_find_floor`, PC 105, register 101, and G7042 retains
structured function/PC/register facts and a related source callable location
(`target/library-float-parse-v3.log`).

The final non-overlapping focused targets pass **390 tests**: 5 associated
bindings, 5 expected reborrows, 22 revision, 24 runtime memory, 92 signatures,
65 trait solver, and 177 VM tests. Evidence is in
`target/library-fixes-regression-v6.log` and the corrected reborrow/revision
targets in `target/library-fixes-regression-v7.log`. The v6 failures were stale
generation assertions and a new cancellation fixture that omitted `with _`
and therefore correctly resumed instead of cancelling; no compiler acceptance
rule was relaxed. The panic-recovery regression separately passes with LLVM
in `target/library-fixes-llvm-unwind-v1.log`. Cranelift+mold is the opt-in fast
Rust edit path; the installed Cranelift backend still fails that unwind test.

The last full source matrix remains 10 passing/20 failing, before the later
individual Path success. It has not been rerun on this entire batch; neither
390 focused passes nor Path's success proves overall conformance. Fixed arrays,
associated domain/result and outlives contracts, general quantified evidence,
remaining reference provenance, and tail proofs are still active work.
Interface 14, bytecode 70, and VM schema 114 are unchanged in this batch.

## Implementation associated equalities and declaration boundaries

Cache 70/interface 14 retain named associated type and effect-row equalities
on implementation headers. Trait candidate admission, method selection and
explanations check the instantiated equalities. Generic callers can supply
their own lexical equality evidence; each query resets its table environment
so those assumptions do not become global implementation rules. Inherited
associated owners and ordered GAT arguments remain part of the obligation.
Bytecode 70/verifier 30/schema 114 are unchanged.

Header parsing splits adjacent equality/type operators (`=<`, `=&`, `>=`),
and declaration scanning tracks the corresponding angle boundaries, including
`>=<`. The scanner now skips bracket groups instead of treating an array
type's internal semicolon as a declaration terminator. This is not fixed-array
type, layout or runtime support.

`target/associated-bindings-focused-v5.log` passes 4 associated-binding,
48 header, 8 scanner, 90 signature and 65 trait-solver tests. The binding cases
exercise accepted and rejected implementations, generic lexical callers,
inherited items, GAT arguments and effect rows, with fresh/decoded O0/O2
execution for the concrete cases. The source matrix remains 10 passing and
20 failing roots, none ignored; the completed run has **225 passing and 20
failing tests**. Earlier v3's semantic positive failed because its fixture
used an unsupported qualified-call expression; v4 exposed the scanner's
adjacent GAT equality boundary. Neither failure was waived.

`target/associated-bindings-import-v7.log` additionally passes all 5 final
binding tests with exact G4169 rejection checks and cross-package O0/O2
fresh/decoded execution. The preceding broad v6 run's new import fixture
correctly failed for constructing a private field; the test library now
explicitly exports that field. No production visibility rule was weakened.
The completed v6 run otherwise passes 259 library-unit, 262 Core, 48 header,
24 library-boundary, 22 revision, 8 scanner, 890 service, 90 signature and
65 trait-solver tests. Together with the corrected five-test v7 target, this
is **1,673 passing tests** across those final targets; the source matrix's
20 failures above remain outstanding.

Three independent read-only diagnostics are consolidated in
[the Stage0/library blocker map](stage0-library-blockers.md). Missing expected
reference reborrowing has the broadest immediate shared-library impact.
Generic I/O contract environments, fixed arrays, GAT domain/result contracts,
general quantified evidence, source dependency closure and remaining proof
precision issues are still outstanding. Selection regressions do not establish
complete associated-item coherence or overall conformance.

## Typed memory preservation across mandatory tail calls

Cache 69/verifier 30 reconstructs frame-preservation facts for typed raw
memory writes/copies, resize/release, and helpers whose inputs are all proven
frame-independent. The helper summary is separate from unconditional and
destructor-only preservation: passing a current-frame pointer cannot satisfy
its input requirement. These facts are recomputed from executable code, not
trusted source names or producer annotations. Reference-bearing writes of
current-frame addresses still invalidate the surviving carrier, including
transitive calls and both raw-copy forms. Bytecode 70/schema 114/interface 13
are unchanged.

The floating parsing scanners now branch directly to their result or proper
tail invocation, without reachable post-tail work or retained early-return
labels. Their previous source-level errors are gone; parsing still fails a
later mandatory-tail provenance check and is not accepted as complete.

`target/tail-memory-before-v1.log` reproduces the rejected scalar raw-write
tail call before the fix. The completed `target/tail-memory-final-v5.log`
passes 259 library-unit, 29 native-bridge, 22 revision, 25 runtime-manifest,
23 runtime-memory, 890 service, 175 library-API, and 176 VM tests. Its source
matrix passes 10 roots and fails 20, for **1,609 passing and 20 failing tests**
overall. No tests are ignored. `float_text` is newly passing; the other source
failure identities are unchanged. Tests cover fresh/decoded O0/O2 execution,
heap replacement and resize, both raw-copy forms, a 42-iteration tail cycle
under a 16-frame cap, and independent admission rejection of direct/helper/
destructor/raw-write/raw-copy attempts to hide current-frame references.

## Inferred reference shapes and computed assignment destinations

Cache 68 resolves already-bound inference structure when allocating Core
expressions and looking up assignment locals. A completion result whose type
cell is already bound to a reference, record, or callable exposes that shape
to subsequent structural checks. This is not premature zonking: unresolved
type, lifetime, and effect-row cells remain open. Shared references do not
gain mutation authority, and inferred borrows cannot escape local storage.

PlaceFlow now evaluates computed dereference destinations after the RHS,
including destinations beneath field projections. It uses the same non-moving
reference-handle traversal as reads and reborrows, retaining temporary result
loans through the store. Whole-referent restoration still precedes capability
validation, and abrupt RHS evaluation skips the destination. Structural exit
analysis also follows the computed destination after a normally completed RHS.

The original inferred-reference reproduction fails with G4140 in
`target/inferred-place-before-v1.log`. Resolving its type exposed a second
failure (missing frozen NLL loan fact) for immediate completion destinations;
destination traversal addresses that separate omission. Regression coverage
includes fresh/decoded execution at optimization levels 0 and 2, projected
destinations, RHS-first side effects, skipped destinations, inferred records
and callables, and mutation/escape/alias rejection.

Verification: `target/inferred-place-verified-v4.log` passes 259 library-unit,
262 Core, 13 mutable-binding, 22 revision, and 890 service tests. Its one
failure was a negative-test expectation: the forbidden second unique borrow
correctly reports G5006, not the anticipated G5004. With that expectation
corrected, `target/inferred-place-final-v5.log` passes all 7 borrowed-temporary,
19 higher-ranked/call-lifetime, 17 lifetime-inference, and 176 VM tests.
These completed runs cover **1,665 passing tests** without an outstanding
failure in those targets. This is bounded regression evidence, not proof of
full language conformance.

The completed `target/inferred-place-focused-v2.log` still has 21 failing
standard-library source roots (9 passing). The previous G4140 errors in the
floating-point helpers are gone, but this is not library completion:
`float_text` now fails a mandatory-tail frame-provenance check, while
`float_parse` still has result-context, tail-control, and moved-value errors.
Bytecode 70/verifier 29/schema 114/interface 13 are unchanged.

## Safe pointer address inspection and anonymous call-region inference

Cache 67/bytecode 70/verifier 29/schema 114 add two finite, manifest-bound
machine operations required by standard-library section 22.2: pointer address
equality and pointer address inspection. Their exact safe contracts accept
const raw pointers and return u32 equality/usize address values. They neither
read storage nor confer allocation, lifetime, or dereference authority. The
implementation compares/inspects native addresses without exposing provenance
for integer-to-pointer reconstruction. Null, dangling, and one-past addresses
can be inspected without establishing an initialized resident.

The canonical library root now declares both leaves, so memory clients share
one manifest-bound declaration rather than unbound fragment-local externs.
Their memory ordinals append at 25/26 and authority tags at 208/209; earlier
tags are unchanged. The Rust authority inventory and the corresponding source
enum, metadata, and witness inventory now contain 182 roles. Interface 13 is
unchanged. This is address inspection, not a new pointer reconstruction API.

Explicit body-local lifetime arguments spelled `'_` now allocate inference
cells, just like omitted lifetime arguments. Both ordinary and associated
generic-argument elaboration preserve that distinction from a fixed elided
annotation. A reference-returning `identity<'_>(value)` follows the input's
enclosing region and cannot extend it to `'static`. The positive case failed
with G5017 before this change (`target/explicit-inferred-lifetime-before-v1.log`).

`target/pointer-inspection-verified-v5.log` passes 259 library-unit, 19
higher-ranked/call-lifetime, 29 native-bridge, 22 revision, 25 runtime-manifest,
20 runtime-memory, 90 signature, and 176 VM tests (**640 total**). New tests
cover fresh/decoded pointer equality, null/dangling/cast/one-past inspection,
malformed operation substitution rejection, and refusal of raw reads after
safe inspection. A fresh/decoded cross-engine test observes exactly the same
pointer address in source and native code, with native mutation visible to
the source owner afterward.

The completed `target/pointer-inspection-broad-v6.log` passes 47 header,
29 resolution, 890 service, 175 standard-library API, 65 trait-solver,
32 type, and 23 unsafe-memory tests (**1,261 total**), with no failures.

The standard-library source target in `target/pointer-inspection-focused-v3.log`
is now **9 passing and 21 failing cases**. The `budget` case compiles and
executes to 42; it previously stopped on the two missing machine leaves.
Comparing failed identities with the previous structural-lifetime baseline
removes only `budget`, with no new source failure. That intermediate run's
separate unit failure was a stale 180-role assertion, corrected and verified
against the complete 182-role witness inventory in v5.

The additional source-authority execution attempt
(`target/pointer-authority-source-protocol-v4.log`) fails before execution on
immutable bindings used mutably throughout existing compiler sources, including
`runtime_manifest::named` and `conversion_name`. It does not establish executed
source-protocol parity. Source metadata has been updated, but self-hosted
compiler completion and full language/library conformance remain open.
Across v5, v6, the source-composition target from v3, and this additional
source-protocol target, the non-overlapping result is **1,910 passing and
22 failing tests**: 21 library-source failures and one source-protocol failure.

## Rigid caller regions and omitted callable lifetime inference

Cache 66 separates omitted declaration lifetime arguments from fixed caller
regions. Ordinary named-function and method instantiation now allocates a
distinct lifetime inference cell for each omitted region, shared by the value
contract and its executable generic application. Structural callable invocation
opens only callable-bound regions; an enclosing Generic region or explicitly
supplied lifetime is not rebound. Free generic application arguments remain
intact even when absent from every value parameter, result, and effect.

This fixes incorrect acceptance of calls through an explicitly typed callback
with an unrelated enclosing lifetime, including callbacks with a separate
higher-ranked binder. Explicit direct lifetime applications now enforce the
same rigid rule. Inferred named-function aliases can learn their region through
a later local invocation, and that shared inference closes their executable
instance rather than leaving a fictitious declaration-region argument behind.

Lifetime variance checking retains inference equations from callback inputs
even when their structural type is replaced by a proven coercion view. A
static-only callback therefore constrains the enclosing call's inferred region
instead of silently accepting an arbitrary short borrow. Temporary result and
argument contexts freshen inference cells independently while preserving region
relationships and nested binder scopes; contextual elision cannot prematurely
fix the input-derived region of `Str::as_bytes` and similar generic calls.

`target/structural-call-lifetimes-v5.log` passes 258 library-unit, 262 Core,
17 higher-ranked/call-lifetime, 17 lifetime-inference, 22 revision, 90 signature,
and 23 unsafe-memory tests (**689 total**). New positive tests execute typed
callback reference returns, inferred named-function aliases, and explicit
phantom lifetime applications in both fresh and decoded VM artifacts. Negative
tests reject structural/enclosing lifetime rebinding, explicit direct lifetime
rebinding, and static-only callback input inference. The invalid structural and
explicit direct calls reproduced release-artifact acceptance before this fix
(v1/v3); the positive typed-callback and inferred-alias cases also failed in the
baseline (v2). The intermediate v4 run exposed the contextual-elision ordering
problem described above; v5 fixes it and passes the complete focused set.

The completed `target/structural-call-lifetimes-broad-v6.log` run passes 47
header, 29 resolution, 890 service, 65 trait-solver, 32 type, and 176 VM tests.
The source-composition target remains at 8 passing and 22 failing cases, with
exactly the same failing identities as `target/universal-body-broad-v16.log`.
`target/structural-call-lifetimes-contracts-v7.log` passes 5 borrowed-temporary,
9 effect-union, 3 generic-default, 17 mandatory-tail, 28 native-bridge,
19 runtime-memory, 4 runtime-storage, and 175 standard-library API tests
(**260 total**). Across these non-overlapping targets and v5, the result is
**2,196 passing and 22 failing tests**, not a full conformance-suite result.

This does not establish full lifetime inference or higher-ranked conformance.
The remaining quantified-relation and standard-library requirements below
remain open. Interface 13, bytecode 69, verifier 28, and schema 113 are unchanged.

## Lifetime-universal Fn proofs and transactional leak checking

Cache 65 checks lifetime-quantified Fn predicates with fresh rigid
`Lifetime::Placeholder` regions. Those regions are distinct from declaration
generics, callable-bound regions, and inference holes. Predicate opening
removes exactly its owning binder, preserves nested binders, and shifts
references to outer scopes without capture. A higher-ranked actual callable
is instantiated with proof-local lifetime holes before its inputs, output,
and effect equalities are checked against the rigid predicate.

Inference is transactional. Completion partially resolves every older type,
lifetime, effect-row, and const cell, including indirect references and pending
effect equalities. A new region reachable from that outward state rejects the
proof and restores all prior assignments. Successful proofs retain safe outer
constraints and discard proof-local assignments. Nested proofs preserve the
outer scope and use fresh identities after rollback. Proof-local regions are
rejected by type fingerprints, frozen lifetime-scope validation, concrete
instance identities, MIR placeholder checks, and VM generic-argument validation;
the VM decoder does not admit their reserved encoding tag.

Direct generic calls now accept owned universal Fn evidence and shared/unique
receiver evidence for known capture-free named function arguments. A callback
valid only for `'static` cannot satisfy a universally quantified input region.
An inferred output type cannot capture that region. Frozen quantified records
also reject invalid lifetime scopes and detached associated equalities with
G4199. First-class function values cannot yet retain residual quantified where
contracts and are explicitly rejected with G4198 rather than erasing them.

Generic bodies can invoke owned callbacks using their lexical universal Fn
evidence when the receiver is independent of the quantified regions. Each
invocation opens the callable-bound regions independently and retains the
input-to-output reference-origin contract. Enclosing declaration lifetimes
remain rigid, including in ordinary lexical Fn evidence: they are not new
callee-owned binders. Region substitution preserves those free lifetimes in
the result and effects, and mutable-reference/raw-pointer invariance checks
use the opened contract without rebinding its enclosing regions.

`target/universal-free-lifetime-v15.log` passes 258 library-unit, 11 end-to-end
higher-ranked bound, 17 lifetime-inference, 22 revision, and 90 signature tests
(**398 total**). Tests cover fresh/decoded VM execution of universal callback
invocation and returned-reference provenance, static-only and outer-output
leak rejection, first-class erasure rejection, and both ordinary/universal
lexical evidence retaining enclosing lifetimes. The enclosing-lifetime
negative case reproduced incorrect acceptance before the fix (v13); v14
rejected it but exposed a syntax error in a new positive fixture, corrected
and verified in v15. The free-input/output positive fixture checks generic
body elaboration; its runtime entry point does not invoke that generic body.

This is not full language section 13.3. Higher-ranked ordinary traits and
RunsIn, borrowed-closure receiver/environment evidence, body-local use of
receiver-dependent universal assumptions, first-class quantified contracts, implementation
conditions, and non-lifetime binders remain unfinished. Bytecode 69,
interface 13, verifier 28, and schema 113 are unchanged. Standard-library
and self-host completion remain open.

The completed `target/universal-body-broad-v16.log` run passes 47 header,
29 resolution, 890 service, 65 trait-solver, 32 type, and 176 VM tests. The
standard-library source target remains at 8 passing and 22 failing cases;
its failing test identities are unchanged from the associated-row baseline.
Its failing identities also match `target/universal-source-broad-v9.log`
exactly. Together with v15 this is **1,645 passing and 22 failing tests** across the
executed, non-overlapping targets, not a full conformance-suite run.

## Quantified callable contract representation (historical representation step)

Cache 64/interface 13 add `CallableSignature::universal_bounds`, whose
`QuantifiedWhereBound` records own the lifetime binder, subject, exact trait
identity, and associated type/effect equalities as one bundle. Universal
predicates never enter the ordinary where-bound or associated-equality lists.
Renaming bound lifetimes preserves their canonical identity. Callable, trait
method, selected implementation, and normalization transformations retain the
bundle and shift inserted caller regions under its scope. The trait solver's
nested callable substitution now applies that shift too.

Native source-contract fingerprints include quantifier counts and all bundled
relations/equalities; the fingerprint encoding has advanced to v2. Bytecode
69, verifier 28, and schema 113 are unchanged. Tests check bound-name alpha
equivalence, ordinary/universal evidence separation, specialization of type
and effect arguments containing outer regions, and native fingerprint
changes when quantified metadata changes.

At this representation-only step, elaboration still emitted G4198 and did not grant universal
evidence. Lifetime-quantified callable predicates are retained in the error
interface for checking and transformation tests; quantified implementation
conditions and non-lifetime binders still need representation work. Fresh
rigid proof scopes, leak checking, validation of imported quantified proof
metadata, and instantiation of universal evidence inside bodies remain open.
The two end-to-end higher-ranked where-bound tests therefore remain pending.
The completed `target/quantified-contract-focused-v3.log` run passes 247
library-unit, 22 revision, 25 runtime-manifest, and 90 signature tests; the
later trait-solver substitution regression is verified separately below.

The completed `target/quantified-contract-focused-v4.log` run passes all 248
library-unit, 22 revision, 25 runtime-manifest, 890 service, 90 signature, and
65 trait-solver tests (**1,340 total**), including the nested quantified
substitution regression. This is focused transformation and compatibility
evidence, not higher-ranked where-bound semantic conformance.
`target/quantified-contract-pending-bounds-v5.log` confirms both pending
end-to-end bounds tests still fail with G4198 rather than granting evidence.

## Capture-avoiding specialization under callable binders

Cache 63 corrects an existing higher-ranked substitution defect: a caller's
free bound region could be captured by a callable binder inside an alias or
selected contract. Substitution now shifts free bound regions in inserted
type, lifetime, and effect-row arguments, while preserving regions bound
inside those arguments. The same rule applies to selected `Self` and the
legacy type-only substitution path. Every callable node owns a de Bruijn
scope, including an empty binder list, matching header elaboration.

The new region traversal reaches nominal arguments, associated type/const/row
projections, GAT arguments, effect instances, and static-data element types;
depth overflow is rejected. Source alias expansion is compared against an
explicitly written nested callable, not only inspected through synthetic
terms. `target/higher-ranked-capture-before-v1.log` reproduces the capture
failure before the fix. This is prerequisite scope preservation, not universal
where-bound proof checking; the G4198 guard and two pending end-to-end tests
below remain in place. Interface 12, bytecode 69, verifier 28, and schema 113
are unchanged.

The completed `target/higher-ranked-capture-after-v4.log` run passes all
245 library-unit, 47 header, 22 revision, 890 service, 89 signature, 65 trait
solver, and 32 type tests (**1,390 total**), including the new source alias
equivalence check. This focused run does not include the still-failing
standard-library source or higher-ranked where-bound targets.

## Higher-ranked predicate syntax groundwork (not semantic support)

`WhereBoundHeader` now owns an optional universal binder for the entire
predicate: subject, trait arguments, and associated equalities. This is not
a callable-type binder or an extra declaration generic. Adjacent predicates
retain independent binders, and nested callable types retain their own
lifetime scope. Empty/missing binder lists, repeated names within a binder,
and universal defaults are diagnosed. The existing declaration-kind parser
retains lifetime, row, and const kinds; constrained brand binders still need
additional syntax and semantic work.

At this syntax-only step, signature elaboration deliberately failed closed with G4198 for quantified
predicates, including implementation bounds. No universal predicate becomes
ordinary existential trait evidence. Frozen quantified contracts,
capture-avoiding specialization, rigid-placeholder proof checking, leak
checks, and body-local use of universal evidence were still unimplemented.

`target/higher-ranked-header-v2.log` records all 47 header, 29 resolution,
and 87 signature tests passing. The two new end-to-end tests in
`tests/higher_ranked_bounds.rs` intentionally remain red:
`target/higher-ranked-bounds-after-header-v2.log` records their G4198 failures.
The positive case requires fresh/decoded VM acceptance; the negative case
requires an actual universal callable/lifetime obligation failure rather than
an unsupported-feature diagnostic. Neither is counted as conformance evidence.
No full-baseline rerun or successful-interface/wire generation change is
claimed for this syntax-only step. Standard-library and self-host completion
remain open.

## Declaration-kinded associated effect equalities

Cache 62 classifies associated equalities after resolving the trait and its
associated-item declaration. A bare `Effects=e` on intrinsic Fn/RunsIn, or a
bare equality on a source-declared associated row, now freezes as an effect-row
binding instead of a type binding. Inherited associated items retain their
row/type kind along with their generic argument kinds. An unrelated source
trait named Fn with an ordinary type named Effects does not acquire intrinsic
row authority. Wrong-kind brace equalities and type projections used as rows
are rejected. Bare associated-row projections retain their exact subject,
trait identity, and item name.

Invocation inference now solves where-clause equalities before checking the
outward effect permission. Fn Effects equalities use row unification directly:
two independently minimized subset constraints could otherwise select an empty
inference row and then reject a nonempty callback. The executable regression in
`target/associated-row-equality-service-v7.log` verifies fresh/decoded VM
execution of an inferred, handled row, rejection when that effect is unhandled,
and rejection of different callback rows constrained to be equal. The earlier
`target/associated-row-equality-contracts-v2.log` records 85 signature and
29 resolution tests passing, including bare generic rows and inherited row
declarations. Bytecode 69, interface 12, verifier 28, and candidate schema 113
are unchanged; this changes elaboration and inference, not wire layout.
The final focused run in `target/associated-row-equality-contracts-v10.log`
passes all 87 signature, 29 resolution, and 22 revision tests, including the
exact projection-identity and wrong-kind/source-spelling regressions.
The completed optimized non-GSC run in
`target/associated-row-equality-full-baseline-v9.log` records **2,754 passing
and 22 failing tests**, with 60 GSC tests deliberately excluded. All 890 service
tests and every other executed target pass. The only failing target remains
`standard_library_sources`, with 8 passing cases and the same 22 failing case
names as the borrowed-temporary baseline; no new failing cases were added.

Higher-ranked where-bounds such as `for<'call> &'call mut F: Fn<...>` remain
unimplemented. Their acceptance needs universal binder scope, fresh rigid
placeholders, and leak checks through associated equalities and specialization;
merely accepting their syntax would not establish language section 13.3.
The existing callable-type lifetime binders do not prove that broader contract.
Standard-library and self-host completion remain open.

## Explicit borrowed temporaries and referent context

Cache 61 connects explicit rvalue borrows to the existing temporary-place
lowering. PlaceFlow now publishes a distinct `Temporary` storage origin keyed
by the producing Core expression. The same identity reaches the actual
Evaluation/Control/Runtime MIR resident; it is not a synthetic Unit marker.
Incoming borrowed fields and destructor observations are retained under this
owner. Escape analysis treats the resulting reference as body-local rather
than rejecting every temporary immediately or inventing static provenance.
Borrowing a temporary's field retains the complete owner and projects its
place, rather than moving the field into another temporary. Initializers that
exit abruptly do not create a phantom storage owner or reference.

Explicit borrow expressions also pass expected referent types into their
operands. This supplies the ordinary selected-width numeric and contextual
Str literal rules without supplying the expected outer reference lifetime as
escape authority. Scope-exit analysis now rejects live loans assigned into
outer owners as well as loans returned in a block's computed result. This
closes an outer-variable escape discovered by the new temporary tests.

`target/borrowed-temporaries-library-v8.log` records all four new temporary
tests passing, including O0/O2 execution, single initializer evaluation,
single destruction, whole-owner field borrowing, destructor-retained input
loans, typed u128 extrema, abrupt initializers, local reborrows, and rejection
of returned/assigned/tail-transferred temporary references. The existing
`stdlib/tests/integer_text.glorious` passes unchanged: the library source run
now has **8 passing and 22 failing cases**. The preceding contract runs in
`target/borrowed-temporaries-contracts-v6.log` and
`target/borrowed-temporaries-contracts-v7.log` record 262 Core, 17 lifetime,
17 mandatory-tail, 13 Evaluation MIR, and 22 revision tests passing (v6's stale
cache-number assertion was corrected and passes in v7).
`target/borrowed-temporaries-storage-v12.log` additionally records all five
temporary tests and all five source-storage tests passing, including the exact
MIR resident check and rejection of expected `&'static` references to temporary
u128 or Str values. Static backing data does not make its local view carrier
static storage.

The completed optimized non-GSC regression run in
`target/borrowed-temporaries-full-baseline-v10.log` records **2,749 passing and
22 failing tests**, with 60 GSC tests deliberately excluded. All 889 service
tests and every other executed target pass. Comparing exact failing case names
with the preceding tail-provenance baseline removes only `integer_text` and
adds none. The final static-reference test was added after that run's temporary
target executed and is separately verified by v11 and the complete five-test
v12 temporary run; it is not included in the 2,749 baseline count.

This does not complete the language's literal-materialization contract:
uncontextualized text/byte literals still use the older scalar fallback,
and literal wrapper selection still needs the full selected-library manifest
authority rather than the current distributed-library lookup. Standard-library
completion and self-host completion remain open.

## Mandatory tail-transfer provenance

Cache 60 and verifier 28 replace the blanket rejection of reference-bearing
tail arguments with positive frame-independence proofs. Source escape analysis
tracks incoming borrows, nested carriers, owned closure captures, and surviving
branch assignments; local borrows and mixed local/incoming alternatives remain
rejected with G4403. Block and pattern binding restoration prevents shadowed
locals from contaminating outer provenance. Aggregate joins are idempotent and
field-wise rather than accumulating exponentially nested alternatives.

The VM independently reconstructs its evidence from executable instructions.
Copies, reborrows, aggregates, and supported pointer producers propagate must
facts; unknown producers and potentially reference-mutating boundaries revoke
them, including facts retained in handler continuations. Recursive helper
summaries prove result independence and conditional destruction safety without
trusting source names or producer-supplied purity metadata. Registered callable
destructors participate in these summaries. Initialization-probe refinements
require an actual adjacent predecessor, so a jump cannot borrow authority from
a skipped probe. Never-exposed empty slots can prune impossible cleanup paths.
These are derived verification facts, not new wire fields: bytecode 69,
interface 12, and candidate envelope schema 113 are unchanged.

`target/tail-provenance-contracts-v14.log` records all 17 mandatory-tail,
22 build/revision, and 176 VM tests passing. Source cases execute fresh and
decoded bytecode at optimization levels 0 and 2, including 10,000 recursive
transfers under a four-frame limit. Negative cases reject local aliases,
mixed branches, forged helper results, recursive false producers, reference
mutation, and skipped initialization probes. The strengthened mutation test in
`target/tail-provenance-destructor-v18.log` additionally rejects both direct
and helper-mediated execution of a mutating registered capture destructor;
removing its reference-bearing store makes both variants verify and execute.

The new executable `stdlib/tests/integer_parse.glorious` covers all twelve
integer widths, signed minima, unsigned maxima, signs, radices, and parse error
offsets. Its focused run passes in `target/tail-provenance-integer-parse-v8.log`.
This does not complete the broader integer-text suite or the standard library.
Language section 12 and L37/L38 remain partial: indirect tail targets,
captured callees, active-handler transfers, and native-backend acceptance are
not established by this work. Source mutation diagnostics also need richer
alias-sensitive post-call analysis; the VM remains independently fail-closed.

The completed optimized non-GSC regression run in
`target/tail-provenance-full-baseline-v16.log` records **2,743 passing and
23 failing tests**, with 60 GSC tests deliberately excluded. All 889 service
tests and every other executed target pass. The library source target now has
7 passing cases, including the new integer parser case, and exactly the same
23 failing case names as the preceding scalar-literal baseline. Full compiler
conformance, standard-library completion, and self-host completion remain open.

## Scalar literal validation and borrowed-text trait integration

Scalar integer literals now receive checked, selected-width range validation
after inference. MIR and VM pattern readers share the checked sign/radix parser,
including negative hexadecimal/octal/binary values and signed minima. Floating
patterns parse directly at their selected precision and use canonical structural
bit equality (including distinct positive and negative zeros). Cache 58 and
verifier 27 invalidate older scalar-literal and pattern behavior; the wire
format remains bytecode 69, interface 12, candidate envelope schema 113.

The signed-minimum expression exception currently requires a unique, safe,
pure source operator contract. Proving that the selected implementation actually
implements numeric negation, rather than an unrelated same-spelled operation,
remains unfinished; this is not a completed operator-authority acceptance claim.
The integer library's checked-multiplication limits now have explicit unsigned
type annotations so an out-of-range default `i64` is not cast after the fact.

Cache 59 additionally instantiates trait method lifetimes through simultaneous
kind-preserving substitution. Implementation-owned lifetimes in `Self` and
inserted trait arguments are not rebased again. This removes a false contract
mismatch for traits implemented by borrowed nominal types. Escape analysis also
preserves caller-owned reference provenance when loading an incoming borrowed
aggregate, without assigning that provenance to unknown or body-local storage.

Source `Str` implementations now provide Clone, Eq, Ord, Hash, and Display;
ordering is byte-lexicographic and hashing uses the existing owned String stream.
This does not establish the complete standard hash policy or Debug escaping.
Verification: `target/trait-lifetime-contracts-v10.log` records 84 signature
and 22 build/revision tests passing, including distinct owner/trait/method
lifetimes, rejection of swapped lifetimes, and nested effect/projection/HRTB
substitution. `target/borrowed-aggregate-load-v10.log` records the executable
incoming-aggregate forwarding regression and its local-escape rejection passing.
`target/stdlib-scalar-literals-v11.log` records 6 standard-library cases passing
(including borrowed-text traits and integer arithmetic) and 23 still failing.
The borrowed-text case checks empty/prefix/UTF-8 ordering, clone, String-compatible
hash streams, and UTF-8 display through the verified VM. The earlier focused
scalar runs recorded 19 service and 258 MIR/pattern/revision/VM tests passing
(`target/signed-literal-service-v6.log`, `target/signed-literal-contracts-v6.log`).
The fresh optimized non-GSC baseline in
`target/scalar-literal-full-baseline-v12.log` completes with **2,734 passing and
23 failing tests**, with 60 GSC tests deliberately excluded. All 889 service
tests and every other executed target pass; the only failing target is
`standard_library_sources`, with the same 23 failing case names as the focused
library run. The strengthened local-escape diagnostic assertion additionally
passes in `target/borrowed-aggregate-load-v12.log`. This is a compiler regression
baseline, not a full specification acceptance audit: standard-library completion
and self-hosted compiler completion remain unproven.

## Kind-preserving integer const values and expressions

Cache 57 replaces the `ConstU32`/`ConstU32Expr` generic-identity representation
with one checked, kind-preserving integer value/expression representation for
all twelve signed/unsigned scalar integer kinds. Header and body syntax retain
literal spelling until the declared slot supplies its kind. Closed identities,
specialization, trait arguments, associated constants, nominal defaults, and
VM metadata carry that kind and the complete 128-bit magnitude. The Stage 0
target's pointer-width const checking uses its 64-bit ABI, not host `usize`.
Quantity values remain a separate domain.

Symbolic substitution uses original mixed-kind binder indices, simultaneous
substitution, checked arithmetic at the selected width, and explicit resource
failures. Dependent nominal arithmetic defaults wait for earlier inferred
arguments and then constrain the supplied/defaulted slot; they do not fabricate
a symbolic binder for an unresolved inference variable. Immediate negative
literals and negative literal patterns admit the signed minimum values.

Interface 12, cache 57, bytecode 69, verifier 26, and candidate envelope schema
113 invalidate older serialized identities. Closed integer encoding includes
kind, canonical sign, and 128-bit magnitude; symbolic metadata must be normalized
and cannot use expression wrappers for already closed values or bare binders.

The three new service tests pass (`target/integer-wide-source-v3.log`), covering
all twelve kinds' unsigned maxima/signed minima, six kinds of symbolic
arithmetic, dependent nominal defaults, associated constants, wrong-kind
arguments, out-of-range values, specialization overflow, and symbolic known-zero
division/remainder in source signatures. Fixed arrays,
remaining compiler conformance, standard-library failures,
and the failing self-hosted production source closure remain unfinished.

The completed optimized non-GSC2 regression run
(`target/integer-wide-baseline-v1.log`) records 2,707 passes and 33 failures.
All 884 service, 262 Core, 111 inference, 175 standard-library, and 28 native
bridge tests pass. Twenty-four failures are the same standard-library source
test names as the previous baseline. The other nine exposed stale parser
expectations, a changed wrong-kind diagnostic, and VM test message/byte-offset
expectations. The wrong-kind diagnostic is restored; parser tests now verify
range rejection at typed elaboration and invalid arithmetic remains an error
sentinel, never a fabricated zero.

After correction, `target/integer-wide-final-focused-v4.log` passes all 581
selected tests: 240 compiler unit, 29 body, 43 header, 19 integer-const, 81
signature, and 169 VM-backend tests. New coverage checks all 144 integer kind
pairings, mixed-slot substitution, distinct kind fingerprints, full-width
encoding, truncation, malformed kind/sign/range metadata, and noncanonical or
ill-kinded symbolic expressions. Hostile-artifact testing exposed a genuine
known-zero divisor gap: both symbolic division and remainder now reject a
literal zero denominator immediately, rather than waiting for substitution.
This focused rerun corrects the nine compiler regression failures but is not
a fresh full-suite run or a full acceptance claim.

## Integer const literal spelling and checked width selection

Cache 56 connects header and body structural literals to one checked integer
literal reader. Decimal, binary, octal, hexadecimal, and digit separators now
produce the same values in explicit const arguments and quantity bounds. The
reader mirrors the bootstrap lexer's existing single separator after a radix
prefix; this does not establish the consolidated lexical grammar's acceptance
contract. Existing `u32` generic-value and `u64` quantity/arithmetic range
checks remain in force, with no new artifact encoding or runtime instruction.

The width-aware reader preserves magnitudes through `u128::MAX` and applies
an enclosing immediate negation before signed range checking, admitting
`i128::MIN` without a positive signed intermediate. It checks declared 32/64
target widths independently of host size, rejects malformed digits/separators,
and does not implement suffixes or silently default a literal's integer kind.
Its wide-value capability is a kernel API: source generic argument storage is
still `ConstU32`/`ConstU32Expr`, so wide closed generic values, fixed arrays,
and complete scalar const elaboration remain unfinished.

Focused verification: 29 body, 43 header, 17 integer-const, and 22 request tests
pass (`target/integer-const-literal-focused-v3.log`). The new service test
compiles, decodes, verifies, and executes seven equivalent spellings/expressions
to 42 (`target/integer-const-literal-service-v3.log`). Its first meaningful
run exposed the separate body parser's decimal-only conversion; both body
const arguments and quantity bounds now use the shared reader. The earlier
service-v1 invocation selected zero tests and is not execution evidence.

The completed default-debug diagnostic run
(`target/integer-const-literal-baseline-v1.log`) records 2,702 passes and 84
failures: the same 24 standard-library source failures plus all 60 GSC2 source
tests, previously excluded from the compiler baseline. It also aborts the
native-bridge process on host stack overflow in the callback reentry test,
leaving 11 cases without outcomes. This unguarded run is diagnostic evidence,
not a passing repository acceptance gate. All 881 service tests pass.

A guarded native-bridge rerun using the previous baseline's optimized test
configuration passes all 28 cases in 6.58 seconds
(`target/integer-const-literal-native-v2.log`). Combining distinct outcomes
from these two configurations yields 2,713 passes and 84 source-compilation
failures, with no missing or changed previously recorded test outcomes and
six new passing regressions. This combined count is not a single-run result;
the default-debug native stack abort remains a separate unresolved robustness
issue. Plan integrity and its 22 unit tests pass; full semantic conformance,
standard-library completion, and self-hosting remain unestablished.

## Integer const binder kinds and compile-time value reads

Cache 55/interface 11 preserve all twelve integer const kinds, plus the
existing quantity domain, through declaration headers, symbolic generic
arguments, inference, projection checks, and fingerprints. Explicit
`const N: usize` binder syntax and other integer kinds are recognized in
ordinary and associated declarations. Missing/non-const kinds are diagnosed.
Canonical kind tags are centralized; bytecode 68/verifier 25/schema 112 extend
const-kind metadata decoding while rejecting unknown tags and older envelopes.

Const parameters can also occur in integer value position. A dedicated
`ConstValue` node crosses Typed Core, Evaluation MIR, Control MIR, and Ownership
MIR with its kinded argument intact. Each boundary checks the scalar result
against the argument's kind; inference cells cannot enter frozen metadata.
Specialization substitutes the enclosing instance and emits a concrete literal
only for an established supported integer value. No symbolic const opcode is
published to the VM. The older concrete-MIR adapter fails closed for an
unspecialized const term rather than inventing a runtime value.

The source regression initially exposed missing const value lookup and omitted
callable defaults (`target/integer-const-kind-source-v2.log`). Value lookup is
now implemented and verified with explicit arguments. Callable-default
application/precedence remains separate unfinished work. The current positive
source tests execute decoded artifacts with distinct const instances,
compile-time const use in a closure, mixed type/const slot indices, and an
inherent implementation's const binder. Cross-kind contracts and implicit
`u32`-to-`usize` result conversion are rejected. Focused runs pass in
`target/integer-const-kind-source-v3.log` and
`target/integer-const-value-source-v4.log`.

This is still not full fixed-array support: concrete non-`u32` const values
and expressions have not yet migrated into `GenericArgument`/VM representations,
and `[T;N]` types, layouts, construction, patterns, and ownership are unfinished.
The width-aware arithmetic kernel below is ready for that next integration;
recognized binder syntax alone does not certify the specified array APIs.
The completed full non-GSC2 run in `target/integer-const-kinds-baseline-v5.log`
reports 2,707 passed, 24 failed, none ignored, and 60 filtered out across 64
suites. Only the standard-library source target fails. Suite-qualified
comparison with the cache-54 baseline finds 21 new passing tests (including
the preceding integer-kernel tests), no missing tests, and no changed existing
outcomes. The subsequently strengthened Core regression also verifies that a
closure reading a const binder has an empty capture environment
(`target/integer-const-core-focused-v6.log`). No production edits followed the
full-suite build. Plan integrity and its 22 unit tests pass; semantic
conformance and self-hosting remain unestablished.

## Width-aware structural integer normalization groundwork (preceding checkpoint)

The specified fixed-array API uses `const N: usize` (standard-library §14).
The preceding frontend had only `u32` and quantity const domains; array
support requires a kind-preserving representation migration, not a source API
rename or truncation of lengths to `u32`.

The new `types::integer_const` kernel represents every scalar integer width
through 128 bits, including signed minimum and unsigned maximum without lossy
host casts. `usize`/`isize` use explicit 32-/64-bit target widths. Checked
addition, subtraction, multiplication, division, remainder, and negation report
invalid operations; values and symbolic binders retain their exact scalar
kind. Symbolic normalization is deterministic, preserves overflow-sensitive
subexpressions, and uses simultaneous kind-checked substitution. Node and
recursion bounds fail explicitly. Array-length validation requires nonnegative
values representable by the target index size; it does not establish element
layout multiplication or array ownership correctness.

Existing `StructuralU32Expr` folding now calls the shared integer arithmetic
kernel while retaining its current symbolic ordering and serialized form.
No source or artifact generation changed: the new wider term representation
is not yet carried by `GenericArgument`, parsed headers, serialized interfaces,
or runtime layouts. `const N: usize` and `[T;N]` are still unfinished source
features, not supported APIs at this checkpoint.

The first focused run (`target/integer-const-kernel-focused-v1.log`) passes
11 tests, including exhaustive 8-bit arithmetic against an independent wider
integer oracle, 128-bit boundaries, target-width differences, kind mismatches,
array-length limits, simultaneous substitution, and proof-budget exhaustion.
After formatting, `target/integer-const-kernel-regressions-v2.log` passes all
244 tests across header, signature, types, trait-solver, generic-default,
tuple-struct-edge, and integer-kernel suites. The source/Core/native-bridge
const-focused run in `target/integer-const-source-regressions-v2.log` passes
80 tests with 1,087 filtered out. Formatting, diff integrity, and conformance
plan integrity checks pass. The full non-GSC2 baseline below predates this
kernel change; no new full-suite, standard-library-source, or self-hosted
completion claim is made from these focused checks.
These are candidate-only links, not completed conformance families.

## Pending ordinary trait bounds before numeric defaults

Cache generation 54 includes ordinary trait obligations in the shared
pre-default propagation loop. A later constraint on one argument can narrow
the compatible implementation heads and constrain another argument. Candidate
head constraints still require the ordinary solver's proof, including every
prerequisite; an unresolved obligation remains pending. Captured assumptions
retain their lexical scope while acquired inference bindings are resolved on
each retry.

The source regression initially fails with G4143 in
`target/numeric-pending-where-focused-v1.log`. It supplies an ambiguous numeric
owner to a generic callable, then fixes the owner to `usize` later in the body.
The test also covers reversed implementation declaration order, ordinary
defaulting without a late constraint, a top-level initializer, an incompatible
floating value, and an implementation with an unproved prerequisite. All four
acceptance programs execute to 42 after artifact decoding and verification,
and both rejection programs fail as required
(`target/numeric-pending-where-focused-v3.log`). All test targets build. The
completed full non-GSC2 run in `target/numeric-pending-where-baseline-v3.log`
reports 2,686 passed, 24 failed, none ignored, and 60 filtered out across 63
suites. Only the standard-library source target fails. Suite-qualified
comparison with the cache-53 baseline finds one new passing test, no missing
tests, and no changed existing outcomes. This is not complete numeric inference
conformance.

## Initializer constraint propagation before generalization

Cache generation 53 shares the non-defaultable obligation propagation phase
between executable bodies and top-level value initializers. Initializers run
that phase before result generalization, which itself supplies numeric defaults.
Unresolved obligations remain pending for strict final checks; neither a
generalized result nor a defaulted numeric type constitutes trait evidence.

The new regression first failed with G4143 in
`target/numeric-initializer-focused-v1.log`: a later `usize` constraint on the
owner could not reach the initializer result before that result defaulted to
`i64`. With the shared phase, the program compiles and executes to 42 after
artifact decoding and verification (`target/numeric-initializer-focused-v2.log`).
The incompatible floating-value rejection case also passes with the final
cache-53 edits (`target/numeric-initializer-focused-v3.log`). All library and
integration test targets build successfully. The completed full non-GSC2 run
in `target/numeric-initializer-baseline-v3.log` reports 2,685 passed, 24 failed,
none ignored, and 60 filtered out across 63 suites. Only the standard-library
source target fails. Suite-qualified comparison with the cache-52 baseline
finds one new passing test, no missing tests, and no changed existing outcomes.
The existing polymorphic-initializer regression also passes. This does not establish complete
inference conformance or resolve the remaining standard-library failures.

## Numeric obligations and deferred associated results

Cache generation 52 extends non-defaultable constraint propagation to ordinary
callable trait bounds, including bounds whose unresolved argument occurs in
the trait relation rather than its subject. A sole compatible implementation
head supplies constraints, not evidence: the ordinary where-bound solver
still rejects missing or contradictory prerequisites.

Associated equality seeding can now query partially resolved heads. For
example, a generic implementation with `Container<T>::Item = usize` can
constrain another numeric literal before `T` itself receives a default. The
projection query must supply its ordinary normalized answer; unresolved or
failed evidence does not grant equality. The complete binding is checked
again after inference.

Rigid body-type equalities involving unresolved associated projections remain
pending instead of failing before their receivers are settled. They are
retried during constraint propagation and checked strictly after defaulting.
Final Core type sealing normalizes concrete associated results throughout
expression and embedded type metadata, while reference/provenance validators
remain mandatory. The new scalar-return cases do not certify every deferred
reference-return or higher-ranked inference combination.

The new positive regression attempts four independent programs: a bound on a
numeric subject, a bound on a numeric trait argument, an associated equality
with a partially inferred generic head, and an associated return type with
multiple compatible receiver implementations. All execute to 42 after
artifact decoding and verification. The negative regression rejects a
floating value against an associated `usize` equality, an incompatible
deferred result, and an implementation with an unproved prerequisite.
Both tests pass in `target/numeric-obligations-focused-v3.log`.
Full regression revalidation completed in
`target/numeric-obligations-baseline-v3.log`: 2,684 passed, 24 failed,
none ignored, and 60 self-hosted tests filtered out across 63 suites. The
only failing target is `standard_library_sources`. Suite-qualified comparison
against `target/numeric-capture-baseline-v13.log` finds exactly the two new
passing tests, no missing tests, and no changed outcomes for existing tests.
The conformance-plan checker and its 22 unit tests pass; semantic conformance
is still not established. These remain candidate-only tests,
not completed conformance families. Default dependency ordering, initializer
obligation propagation, and broader inference combinations still require
specification-driven coverage.

## Typed Core numeric inference integration (preceding checkpoint)

Cache generation 51 integrates the numeric constraint engine into Typed Core.
Uncontextualized and inference-context literals retain scalar-domain
constraints rather than choosing `i64`/`f64` immediately. Pattern binders,
tuple/nominal fields, contextual callbacks, and qualified calls share those
variables. Explicit nominal-pattern arguments and structural constants add
ordinary type constraints; pattern checking does not privately default or
renumber body inference variables. Integer radix prefixes are distinguished
from decimal exponent notation in both expressions and patterns.

Operator declarations can supply their symbolic callable contract before a
width-specific implementation is selected. Qualified calls also seed known
receiver constraints before checking contextual bodies. A unique compatible
implementation head may narrow a receiver using isolated, kind-preserving
inference trials; this is not evidence for its where clauses or supertraits.
Multiple compatible heads remain undecided. Concrete deferred calls must
receive ordinary solver evidence before Core is sealed, and missing, negative,
ambiguous, or exhausted selection remains an error.

Function-body sealing retries pending callable and associated equalities
before numeric defaulting.
Known associated results can constrain an equality's inferred value instead
of defaulting that value to test equality. Deferred associated obligations
retain their original lexical equality assumptions. Deferred effect checks
retain the original declared row and active handler instances/operations;
a handler entered later cannot authorize an earlier call. Defaulting then
precedes strict obligation checks and the final zonking of Core expressions
and embedded metadata. Numeric roots are defaulted, not generalized into
arbitrary initializer type parameters. Capture classification exposes solved
types while unresolved numeric scalars retain their intrinsic copy capability.

The focused numeric run passes all 11 tests, including both completion-arm
orders, nested expressions and pattern binders, later `usize`/`f32` context,
radix spelling, associated-equality constraints, ambiguous implementation heads,
missing implementation evidence, and preserved lexical effect authority.
The separate higher-ranked service run passes 71 tests. These are recorded in
`target/numeric-pattern-focused-v9.log` and
`target/numeric-pattern-hrtb-v9.log`.

The final full stage-zero library/integration run completes 63 suites with
2,682 passes, 24 failures, and zero ignored tests
(`target/numeric-capture-baseline-v13.log`). All suites outside the extended
standard-library source matrix pass, including all 874 service tests, 261
Core tests, 233 library unit tests, 175 standard-library tests, and 28 native
bridge tests. The native callback regression passes with its original zero
native-allocation limits; neither its limits nor its assertion were changed.
Suite-qualified comparison confirms the same 24 failing source-library test
identities as the preceding generic-default checkpoint, with no remaining
existing-test regression. The 60 GSC-2 source tests were explicitly filtered
from this run; the earlier source-authoring failure remains unverified here.
Plan integrity passes with 61 candidate links, and all 22 checker mutation
tests pass. That audit explicitly does not establish semantic conformance.
Candidate links remain candidate-only, not completed conformance families.

This work does not certify all inference forms, numeric suffix/range rules,
standard-library completion, or self-hosting. In particular, general deferred
associated-result equations and complete declaration/default application
still need specification-driven coverage. The extended source-library matrix
and the previously identified self-hosted source migrations remain open.

## Deferred numeric constraint engine (preceding checkpoint)

The inference engine now supports numeric constraints separately from type
bindings. Integer-literal constraints permit integer or floating scalar
contexts; floating-literal constraints require floating contexts. Unifying
type variables transfers and merges their numeric constraints without
choosing a default. Incompatible concrete bindings are rejected before the
hole is bound, so a failed candidate does not poison later valid inference.

An explicit `finish_numeric_defaults` phase first checks the complete set of
numeric constraints, then defaults only unresolved numeric roots. Merged
integer/floating roots choose `f64` independently of union direction; a
known `usize` or `f32` context wins over defaults. Ordinary unconstrained
generic holes remain unresolved. Four new unit tests cover those properties,
including default-phase idempotence and recovery after invalid bindings.
All 233 library unit tests and all 31 type integration tests pass in
`target/numeric-constraint-engine-lib-v1.log` and
`target/numeric-constraint-engine-types-v1.log`.

At that checkpoint Core did not yet call the new constraint protocol. Integrating literal
elaboration, contextual checking, and deferred operator/trait obligations is
was still required; the source regression below remained an active failure.
This checkpoint is an inference-engine primitive, not a claim that numeric
defaulting, the standard library, or full compiler conformance is complete.

## Numeric-defaulting regression exposed (preceding checkpoint)

An active source regression now demonstrates arm-order-dependent numeric
inference. A function returning `usize` binds a completion result from
`true => 0, false => value`, where `value` is `usize`. That ordering fails
with G4167/G4110; reversing the two arms compiles and executes to the expected
result 42. Both requests are attempted by the same test, so the passing
ordering is observed even when the other fails. The evidence is
`target/completion-numeric-defaults-v2.log`; the test remains failing, not
ignored or converted into an expected rejection.

Core's `literal_expected` eagerly unifies an unresolved expected type with
the literal default. Completion arms share their result variable and are
elaborated in source order, so a leading literal fixes that variable to
`i64` before the other arm contributes its non-defaultable `usize` constraint.
This contradicts language section 13.4 and reproduces the shape of the
standard library's `Layout::extend`/`Layout::padded` padding computations.
It does not prove that all errors in those routines have the same cause.

The compiler fix remains open. A sound implementation must retain deferred
numeric constraints through the consumers that currently demand concrete
types, including operator/trait selection and contextual callable checking.
Reordering emitted arms, adding library annotations, or changing a literal's
type after selecting width-dependent operations would not establish that
contract. No compiler behavior changed in this checkpoint, and no new full
baseline run is claimed.

## Callable and nested generic-default contracts (preceding checkpoint)

Cache 50/interface generation 10 extend default validation beyond nominal
and alias declarations. A shared declaring-scope elaborator checks ordinary
and inherent callables, trait/implementation parameters, nested methods,
associated items, and effect declarations/operations. Nested slots retain
their outer-binder offsets, and validation runs after the enclosing `Self`
has been installed. Thus earlier outer binders and an instantiated inherent
head are valid defaults, while self/later references remain invalid even in
unused declarations or before arithmetic folding.

Ordinary and inherent callable defaults are also frozen in the interface's
resolved default table, preserving declaring-module identity, transparent
alias normalization, and higher-ranked lifetime binders. Nested method,
associated-item, and effect default application remains unfinished; this
checkpoint does not claim their defaults are applied at use sites.

The full run in `target/generic-default-contracts-baseline-v1.log` completed
63 suites with 2,668 passes, 25 failures, and zero ignored tests. No existing
test changed or disappeared relative to the preceding baseline. One new
metadata test had an invalid fixture: a bodyless inherent method and use of
the module-local interface collector as though it recursively collected an
inline module. After correcting only that fixture to provide a method body
and both module interfaces, all three new tests pass in
`target/generic-default-contracts-focused-v4.log`. Combined suite-qualified
evidence therefore records 2,669 passing identities and the same 24 failing
standard-library source identities; this is not described as a second full
run. Plan integrity passes with 52 candidate links, and all 22 checker
mutation tests pass.

Callable omission behavior is deliberately unchanged. The specification
permits generic defaults and callable prefix inference but does not explicitly
state whether an omitted callable parameter immediately selects its default
or uses it only after value/result inference leaves the parameter unresolved.
That precedence question has been raised for clarification; declaration
validation and frozen templates are required under either interpretation.
Full conformance, standard-library completion, and self-hosting remain open.

## Declaration-scoped nominal and alias defaults (preceding checkpoint)

Cache 49/interface generation 9 carry resolved, kind-preserving default
templates for nominal and alias declarations. Source defaults may be types,
lifetimes, effect rows, or supported structural constants. Signature
elaboration resolves their names in the declaring module, validates unused
declarations too, and freezes position-aligned templates for Core. Application
substitution preserves earlier actual arguments without capturing caller
slots; omitted lifetime slots use declared defaults when present.

Self/later-binder references and wrong-kind defaults are rejected. Structural
references are checked before arithmetic normalization can erase them,
including constants nested inside a default type. Recursive expansion and
acyclic exponential expansion have explicit resource diagnostics; fully
explicit finite nominal applications do not spuriously expand defaults.
Resolved default templates participate in interface merging and transparent
alias normalization. The former const-only resolution-index default table is
removed rather than retained as a competing authority.

Source regressions execute declaration-scoped rows/types despite caller
shadowing, dependent type/row/lifetime defaults, defaulted aliases in type and
constructor positions, and finite nested defaults. They verify VM execution
both before and after canonical bytecode decoding, and reject unused invalid
defaults and excessive expansion. Full verification in
`target/generic-defaults-baseline-v1.log` completes 62 suites: 2,666 passes,
24 failures, zero ignored. Suite-qualified comparison with the preceding
nominal-kind baseline finds seven new passes (including four substitution
unit tests from the groundwork below), the formerly failing row-default test
now passing, and no missing or regressed test identities. The same 24
standard-library source tests remain failing. Plan integrity passes with 49
candidate links, and all 22 checker mutation tests pass.

This does not complete generic-default support for callable, trait, method,
or effect declarations; their contract and inference paths remain open.
It also does not establish full conformance, complete the standard library,
or verify the GSC2/self-hosting pipeline, which is excluded from this run.

## Generic-default substitution groundwork (preceding checkpoint)

Signature and body elaboration now share one kind-preserving default
substitution implementation. It traverses type structure, effect rows,
lifetimes, and structural constants using the existing transparent-alias
substitution rules. Substituted caller arguments are not recursively
reinterpreted as declaration slots; higher-ranked lifetime binders retain
their identity, and a const parameter cannot accept a type argument.

Four focused unit regressions pass, covering caller-slot capture, row-tail
substitution, higher-ranked lifetime preservation, and constant folding/kind
checks. The complete library unit suite passes 229 tests with zero failures
or ignored tests (`target/generic-defaults-lib-v1.log`). The existing
end-to-end constant-default regression also passes, executing literal,
dependent arithmetic, and quantity defaults to VM result 42 and rejecting a
non-trailing default (`target/generic-defaults-const-v1.log`). This is groundwork,
not completed generic-default support: parsing non-const defaults,
declaration-scope resolution, earlier-binder validation, and freezing those
contracts remain unfinished. The active source-level row-default regression
below is not disabled, and the full conformance baseline has not been rerun
for this groundwork change.

## Nominal generic argument kinds

Cache 48 replaces invented empty rows and rigid constant parameters at omitted
nominal-constructor argument positions with independent inference variables.
Constructor payloads and contextual results constrain them; explicit arguments
and declared structural-constant defaults remain constraints. Unconstrained
row/constant identities cannot enter executable metadata.

Bytecode 67/verifier 24/schema 111 carry tagged type, effect-row, and structural
constant arguments in nominal types and layout descriptors. This replaces the
former type-only nominal representation; rows are not erased or encoded as
ordinary value types. Source lifetime arguments are still erased only after
field substitution, and hostile nominal metadata retaining a lifetime is
rejected. Matching, specialization, binding-pack decoding, native descriptor
collection, and production-LIR closure checks use the kind-preserving form.

The new constructor regressions execute contextual constant inference for
records/tuple structs/enums, row inference from callback payloads, explicit
argument mismatch rejection, and an existing declared constant default.
The new VM regression checks exact wire round trips and rejects row/kind
changes in layout descriptors, duplicate row effects, unerased lifetimes, and
constants disguised as value-type arguments. All focused tests for these
changes pass. The previous Core test for the intentionally unsupported
type-only layout boundary now positively checks all five source argument
kinds; it no longer expects the obsolete rejection.

A further active regression exposes an unfinished frontend feature:
`nominal_effect_row_defaults_are_declaration_scoped` currently fails because
generic defaults accept structural constants only. Language §13.1 requires
defaults of compatible kinds, so this test remains a real failing requirement,
not an ignored or expected-failure test. Full current-tree verification in
`target/nominal-kind-optimized-baseline-v2.log` completes 62 suites with 2,658
passes, 25 failures, and zero ignored tests. Relative to the preceding tuple
checkpoint, the suite-qualified comparison contains exactly three new passes
and this one newly exposed failure, with no missing or regressed existing test
identities. The other 24 failures remain in the standard-library source matrix.
The workspace compile check is clean; plan integrity passes with 45 candidate
links, and all 22 checker mutation tests pass. GSC2/self-hosting remains outside
this regression run and is not established by these results.

## Tuple-struct implementation checkpoint

Cache 47/interface 8 retain tuple structs as distinct nominal layouts, including
their ordered field types and declaring-module visibility. Concrete struct
constructors occupy the value namespace. Tuple-struct calls and constructor
values lower to nominal records, not structural tuples; patterns use the same
authorized field-deconstruction plan as records.

The five `tuple_struct` tests execute constructors, numeric assignment,
left-to-right effectful arguments, first-class/imported constructors, patterns,
and scoped field authority, including independently verified wire round trips.
The five `tuple_struct_edges` tests additionally exercise transparent alias
reordering/inference, same-spelling ordinary value precedence, higher-ranked
borrowed constructor callbacks, partial-field cleanup, and custom-Drop
deconstruction rejection. Both suites pass in the complete non-GSC2 run
`target/tuple-struct-optimized-baseline-v1.log`: 62 suites, 2,655 passing,
24 failing, and zero ignored tests. Comparing suite-qualified test identities
with `target/visibility-baseline-v3.log` shows exactly ten new passes, no
missing tests, and no regressions. Every remaining failure is in the existing
standard-library source matrix. The separate focused run
`target/tuple-struct-edges-v6.log` also passes all 28 body-parser tests.
This is regression evidence, not a completed language/library acceptance gate.

The edge tests exposed and fixed independently relevant gaps: body-local field
projection now consults solved inference variables; pattern type arguments
normalize aliases and the empty tuple to unit; detached runtime nominal-layout
descriptors open callable lifetime binders without weakening their contracts.
The local-shadowing case also exposed absent canonical anonymous-function
syntax. `fn(parameters) -> Result / row { body }` now parses explicitly;
an omitted result is unit, and parameter annotations remain required. The
added execution/rejection cases cover unit, captures, effects, immediate
application, and malformed signatures.
Remainder/reference pattern syntax, the native ABI acceptance family, the full
language/library matrix, and self-hosting completion remain unproven. No
conformance scenario is promoted by this checkpoint.
The plan-integrity gate passes with 43 candidate links, and all 22 checker
mutation tests pass. GSC2 is explicitly excluded from the complete regression
run; its separate source-migration failures are recorded in
`compiler/spec/progress.md` and do not constitute a passing self-hosting gate.

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

## Eighth slice: unit patterns

Empty tuple-pattern syntax `()` now recognizes a Unit subject before the
ordinary tuple-arity check. It produces the same irrefutable decision as a
frozen unit constant. This is not a wildcard for other types: scalar subjects,
nonempty tuples, and nonempty tuple patterns against Unit remain errors.
Cache generation 27 identifies the changed elaboration result.

Three new tests cover direct pattern elaboration, completion arms, nested
tuples/arrays, enum payloads, operation payloads, and type/arity mismatches.
Positive integration cases also execute verified canonical-wire round trips.
All 66 tests in the pattern, pattern-names, prelude, and request/revision suites
pass, and the conformance-plan integrity check passes. The full non-GSC2 suite
was subsequently rerun with the same optimized profile and resource guards:
2,558 tests executed, with 2,387 passing and 171 failing. All three new tests
pass; suite-qualified comparison finds no regressions, missing tests, or
changes to the previous failures. All 54 suites completed, and all 22
conformance-plan checker tests pass. This does not establish full semantic
or self-hosting conformance.

## Ninth slice: concrete floating-literal diagnostics

Language §3.2 requires finite source-literal overflow to be an error, with
rounding directly at the selected width. Previously `1e9999` reached lowering
and failed as G7041, an internal missing-representation error without a source
span. Concrete f32/f64 literals are now checked after Core type resolution and
report source diagnostic G6003 at the literal span. Parsing is directly at the
selected precision, without an intermediate f64 conversion for f32.

Three new service tests cover f32/f64 overflow, a negative literal, an unused
unannotated literal, finite maxima, subnormals, underflow to zero, and a value
that overflows f32 but remains finite as f64. Valid cases execute original and
verified wire artifacts. Runtime infinity remains valid. Cache generation 28
identifies this diagnostic change. Literals retaining generic types until
specialization and broader numeric-literal/suffix conformance are not certified
by this slice; existing lowering checks remain in place.

The full optimized non-GSC2 run completes all 54 suites: 2,561 tests execute,
with 2,391 passing and 170 failing. The existing decimal-f64-overflow regression
now passes without changing its assertion, and all three new tests pass.
Suite-qualified comparison finds no regressions and no missing tests. The
plan-integrity check and all 22 checker tests pass. These results do not change
the planned status of full conformance families.

## Tenth slice: returning-handler completion and current backend fixtures

Language §10.5 makes normal completion part of a resumption's handler-result
contract. Control lowering previously returned the raw protected value to
`k(...)` before executing the completion transformation. Returning explicit
resumptions now include that transformation. Tail-only and cancellation-only
handlers retain their early delimiter exit; full-control clause results still
bypass normal completion. Core separately infers the protected result and final
handler result, checking completion before freezing the continuation's callable
type. Nonreturning completion has a concrete bottom result rather than an
unresolved inference variable. Cache generation 29 identifies these changes.

Seven new tests execute original and verified wire artifacts for nonidentity
completion, exact replay, type-changing completion, cancellation, repeated
performance, helper calls, and effectful completion through an outer handler.
Five old wrong-result service regressions now pass. These tests do not establish
general captured-resumption, replay-ownership, or contextual-control conformance.

Source-produced bytecode assertions now require the ownership-aware call,
perform, and handler instructions. Returning-call checks identify calls to
captured resumption registers, not arbitrary indirect calls. Handler operation
ABI checks compare identities rather than stack-installation order. Existing
runtime expectations and hostile-target rejection checks remain in place.
Parser fixtures retain ordinary truth names and source-declared operator chains;
one conditional parser test is renamed accordingly. Cache-accounting fixtures
now count the distributed standard root/prelude interfaces as well.

The complete optimized non-GSC2 run in `target/ambitious-fixes-full.log` executes
2,569 tests: 2,441 pass and 128 fail. Suite-qualified comparison, accounting for
the parser-test rename, finds 43 old failures resolved, all seven new handler
tests passing, no missing tests, and no previously passing test regressing.
There are 127 remaining old failures and one new failing Glorious-library test.
That new suite exercises the separately embedded expanded source library and
is currently compiler-blocked; the default production library remains the
previous source bundle. Library work continues independently of this snapshot.
All 22 plan-checker tests and the plan-integrity gate pass. No acceptance-family
status or frozen conformance inventory is promoted by these results.

## Eleventh slice: source authority and closure contracts

Module-scoped field authority, explicit public fields, and source-owned scalar
inherent functions are preserved through their defining modules (interface 5,
cache 30). Phase fixtures now import the ordinary standard source and its
fixities instead of relying on removed compiler operators. Explicit runtime
manifest fixtures declare their own source operators and selected leaves.

Cache 31 preserves a captured callable's resident ABI when an individual call
coerces its invocation interval. Immediately invoked compact closures receive
argument-provided type evidence; a regression checks that elaboration does not
change runtime argument evaluation order. The four phase suites passed in
targeted runs: Control MIR 8, Evaluation MIR 13, assignment lowering 7, and
storage lowering 4.

## Twelfth slice: current-semantics tests and remaining ownership defects

The completed non-GSC2 run in `target/all-failures-v6.log` reports 2,526 passing
and 70 failing tests. This is a historical checkpoint, not the current working
tree's final status: the expanded library inventory and further test rewrites
have changed since that run.

Obsolete Boolean `is` fixtures now observe ordinary Test constructors and open
sealed binding packs through contextual callbacks. Six redundant Core tests
for the old Boolean branch-refinement representation and primitive lazy join
were removed; current binding-pack scope, generative identity, producer
validation, and lazy-call tests remain. Producer forgery tests additionally
reject a positive pack on the negative branch and independently renamed binder
evidence. A legacy VM cleanup-sidecar assertion over Copy scalars was removed;
observable destruction and hostile cleanup-proof tests remain.

Three former implementation-limit rejection tests now execute host aliases,
nested returning-resumption payloads, and dynamic-label completion with replay,
discard, and refutable dispatch. Both original and verified wire artifacts are
checked. The host-alias case still requires runtime host authority. Opaque-call
fixtures now use callable parameters rather than local aliases that can legally
be devirtualized; assertions distinguish ordinary calls from resumption calls.

Cache 32 transfers backing-loan authority away from vacated reference carriers,
uses unqualified source names for inherent-method implicit labels, counts entry
into a canceled indirect callee without assuming invocation of its callback
arguments, and preserves lifted closures' own safety qualifiers. Targeted tests
confirm the moved-carrier regression (including forbidden mutation variants),
inherent labels, the float library family, and canceled indirect invocation.
Broader regression verification is still in progress.

The plain-reference NLL assertion in lifetime_inference is explicitly frontend
only and now calls that boundary directly. This does not fix the documented
executable-MIR gap for ending a loan before same-block storage replacement.
Captured labels/resumptions and additional expanded-library compiler features
remain unfinished. No conformance acceptance family is promoted by this work.

## Next work

Cache 46/interface 7 replace item/import/member public flags with explicit
private, parent-module, package and public scopes. The scanner and member/field
header parser share restricted-visibility parsing. Resolution checks every
module/import edge against the original requester's module identity, including
restricted inherent functions. Exposed imports cannot widen their targets'
authority, and merged restricted alias scopes receive the same ambiguity
checks as public aliases. `pub(super)` without a parent module is rejected.

Unmarked nominal record fields now carry declaring-module authority; explicit
field restrictions resolve to their parent/package module scopes. Construction,
projection, assignment and owning patterns preserve that authority through
aliases and re-exports. `Range.start`/`Range.end` are explicitly public as the
library specification requires; storage-bearing library types remain private.
The source matrices cover same-file denial, cross-file descendant access,
cross-package denial, restricted imports/members/modules, invalid restrictions,
and narrowing visibility across cached revisions. Tuple-struct syntax and its
field authority remain a separate unimplemented requirement, not certified by
these nominal-record tests. Nine source/scanner/revision matrices and all 29
resolution tests pass in `target/visibility-focused-v4.log`. Fifteen existing
service fixtures explicitly expose fields used by their cross-module/facade
contracts; their ownership, Drop-selection, source-order, malformed-pattern
and revision assertions remain intact. All 15 pass in
`target/visibility-service-migration-v1.log`. The private-field revision fixture
now removes `pub` to test the canonical default rather than adding a legacy
`private` modifier. UTF-8/FFI library tests now pass restricted-visibility
parsing and reach later type/tail-proof failures.

The final current-tree regression run in `target/visibility-baseline-v3.log`
completes with 2,645 passing tests across 60 suites, the same 24 source-library
failures, and zero ignored tests. All 866 service tests pass. Comparing
suite-qualified results against the mandatory-tail checkpoint finds 10 new
passes (nine visibility matrices and the additional tail-carrier corruption
case), no missing tests, and no regressed results. Plan integrity with 40
candidate links and all 22 checker mutation tests passes; semantic acceptance
families remain planned. This is not full compiler/library/self-hosting
conformance.

Cache 45 adds a bounded mandatory-tail frontier: direct statically selected
calls with structurally frame-independent concrete arguments. The obligation
survives Core, Evaluation, Control, Ownership, Specialized, Cleanup and Runtime
MIR into an explicit VM frame-replacement instruction. It is not gated by the
authoring profiler or optimization setting. Arguments are protected in source
order before remaining frame owners are destroyed; enclosing caller handlers
and the result destination survive transfer. The compatibility MIR adapter
rejects this obligation instead of silently emitting ordinary recursion.

Owned stores and aggregate construction now explicitly consume their prepared
carriers in production VM LIR and both VM interpreters. Wire verification
tracks possible initialization separately from definite readability, rejecting
tail transfer when a destructor-bearing carrier remains on any incoming path.
Mandatory-transfer functions retain selected consuming destruction glue rather
than inline structural cleanup that leaves aggregate shells in temporaries.
The bytecode/verifier/VM-schema versions are 66/23/110.

Fifteen focused regressions cover mutual and geometric recursion at O0/O3
request settings, unprofiled bounded call depth, ordinary-recursion controls,
effectful argument order, enclosing handlers, linear payloads, nested/partial
cleanup, source rejection and corrupted candidate/wire rejection, including
downgraded nonconsuming stores and constructors. These are
interpreter checks, not native-backend acceptance. Generic/borrowed carriers,
indirect and owning receivers, active delimiter/environment discharge or
fusion, and native mandatory transfer remain unfinished.

The full consuming-carrier checkpoint in `target/mandatory-tail-baseline-v2.log`
passes 2,635 tests across 59 suites, with the same 24 standard-library source
failures and zero ignored tests. Comparing suite-qualified identities against
the cache-44 run finds exactly 15 new passes, no missing tests, and no regressed
results. That full run includes 14 tail tests. The subsequent compatibility
adapter rejection, concrete-instance nested-borrow proof, and additional
store/constructor corruption case pass the latest 15-test focused suite in
`target/mandatory-tail-test-v16.log`. Plan integrity (37 candidate links) and
all 22 checker mutation tests pass. No L37/L38 acceptance family is promoted;
the overall compiler/library/self-hosting goal remains open.

Cache 44 distinguishes missing module names from bindings hidden behind private
imports. A private glob no longer marks every queried name inaccessible; its
owner's authority is used only to establish whether it supplies that module,
never to grant the requester access. The regression permutes root/API globs,
checks public dependency paths, keeps actual private module bindings hidden,
and keeps value-only imports out of module lookup. All 29 resolution tests
passed in the initial focused run; the expanded private-glob tests, including
six compile/verify/run-or-reject cases, pass in
`target/private-glob-focused-v4.log`. The source-library matrix still has four
passing and 24 failing tests (`target/private-glob-library-v1.log`), but no
longer reports G3326 or private-type G3304: it reaches later syntax/type checks,
including mandatory `tail` sites. The full non-GSC2 regression run in
`target/private-glob-baseline-v1.log` completes with 2,620 passing tests, the
same 24 source-library failures, and zero ignored tests across 58 suites.
All tests outside that source-library matrix pass; this does not establish
full compiler, library, or self-hosting acceptance.

Binding and tuple-projection conformance has a verified checkpoint (cache 41).
Body syntax retains `let mut`; Core checks assignment and unique borrowing
against non-reusable lexical binding identities. Immutable reference bindings
retain unique-referent authority, while shadowed bindings cannot inherit write
permission. One Core matrix (16 positive/negative source cases) and six
compile/verify/execute tests pass. The bootstrap library has explicit mutable
locals where required, including owned-parameter shadowing, and a CLI probe
executes replacement to 42. Legacy tests are being migrated to explicit
mutable declarations without weakening their ownership/lifetime assertions.
The initial enforcement run exposed 334 failures before that migration.
`target/mutable-bindings-baseline-v2.log` completed with 2,565 passing,
49 failing, and zero ignored tests: 25 remaining fixture-migration failures
and the 24 still-failing standard-library source tests. Parameter and handler
payload fixtures now introduce explicit mutable local shadows; interpolated
sources and two allocation-profile source files also have explicit authority.
The follow-up v3 run completed with 2,586 passing and 32 failing tests, but
is not a clean source snapshot: two new tuple tests and two cache assertions
were compiled against the preceding library build. Four remaining fixture
failures have also been corrected: two handler tests preserve their original
shadow-scope assertions by separating the input seed name, one interpolated
owner declaration needed `mut`, and the native vector test observes its incoming
parameter home before moving it into a mutable local. Focused shadow/native
reruns pass. `target/mutable-bindings-baseline-v4.log` completed at cache 39:
2,596 passing, 24 failing, zero ignored. All tests outside the standard-library
source matrix pass. The cache-40 verification in
`target/mutable-bindings-baseline-v5.log` completed with 2,597 passing,
24 standard-library source failures, and zero ignored tests.
Explicit local type annotations are now parsed, supplied as initializer context,
and checked with rigid lifetime bounds (cache 37). The focused suite additionally
checks scalar/tuple/reference initializers, immutable annotated locals, type
mismatches, and short-loan rejection. Numeric tuple reads, writes, borrows,
reinitialization, and chained indices now use the structural field lowering
(cache 38); out-of-range indices and immutable writes are rejected. The ten-test
binding/annotation/tuple suite passes in `target/mutable-bindings-tuples-v2.log`.
Destructuring bindings now carry a lexical block continuation (cache 39),
reuse checked pattern ownership transfer, require exhaustive patterns, and
record each binder's explicit mutability. Lexical unsafe authority is preserved
in both elaboration and frozen Core scope evidence. The expanded twelve-test
suite passed in `target/pattern-bindings-service-v3.log`.
A further ownership regression exposed wildcard erasure of exact-linear
initializer fields. Cache 40 requires principal zero-use permission for every
discarded let-pattern value, including proof from ambient generic bounds.
`target/pattern-bindings-service-v4.log` passes all thirteen focused tests,
including exact-linear transfer/discard and live/escaping borrow checks.
Binding diagnostics now use G4220–G4223; G4190–G4193 remain reserved for the
pre-existing trait-obligation diagnostics.
Cache 41 additionally rederives tuple projection arities and selected value/place
types from structural base layouts during independent Core validation. A focused
forgery matrix passes in `target/tuple-projection-validator-v1.log`.
Six L03 regression candidates are linked to the new binding tests; the plan
integrity gate and its 22 mutation tests pass. These links do not mark the
required execution/ownership expansion matrices or any full family complete.

The next representation gap is explicit multi-tail effect-row union (§10.2).
Cache 42 now parses associated row projections after `|` in declarations,
typed closures, nested callable types, and explicit row arguments. Multiple
projection operands and a single named tail are preserved; empty/repeated
separators are rejected. Typed closures share the body row-literal parser.
Implementation-associated values use the trait declaration's item kind to
distinguish bare row projections from ordinary associated type projections;
trait row defaults also admit bare projections. In
`target/effect-projections-v1.log`, all 157 body/header/signature/operation tests
pass, including artifact roundtrip execution of duplicate projection unions,
generic row projection definitions/defaults, and missing-permission rejection.
The standard-library source matrix remains four passing and 24 failing tests.
This is projection support, not completion of multi-parameter row unions.
The full non-GSC2 run in `target/effect-projections-baseline-v1.log` completed
with 2,603 passing, 26 failing, and zero ignored tests. Twenty-four failures
remain in the standard-library source matrix; the other two were test assertions
still pinning cache 41. Those assertions now pin cache 42, and all 22 request/
revision tests pass in `target/effect-projections-cache-v2.log`. No other test
failed in the full run. The three new S14 regression links are candidate-only;
the plan-integrity gate and its 22 mutation tests pass with 29 total links.
Cache 43/interface 6 replace the single optional tail with an ordered operand
set throughout headers, inference, Core/MIR, substitutions, summaries, and VM
metadata. Bytecode 65/verifier 22/schema 109 frame the full set and reject
unsorted, duplicate, truncated, or over-budget wire operands. Inference defers
nonunique union equations until other arguments constrain their operands;
freezing rejects remaining ambiguity, while an empty union uniquely resolves
every operand to empty. Trait matching and selected-method materialization
also defer union equations until independent head arguments are known.
Coherence uses correlated row-membership equations to find overlap witnesses,
not arbitrary call-site splits or equality between separate operands.
`target/effect-unions-focused-v6.log` passes 536 unit, coherence, type, trait,
request, VM, and union tests. The expanded nine-test source suite passes in
`target/effect-unions-focused-v8.log`, including explicit row arguments, typed
closure unions, associated row defaults, reordered forwarding, later-argument
inference, omitted permissions, and selected trait method artifact execution.
The full non-GSC2 run in `target/effect-unions-baseline-v1.log` completes with
2,618 passing, 24 failing, and zero ignored tests. Every failure is in the
standard-library source matrix; all other Stage 0 tests pass. The 33 candidate
links and 22 plan-checker mutation tests pass the integrity gate. No acceptance
family is promoted by these bounded tests.
This ongoing source-semantic change supersedes the green checkpoint below.

Last pre-mutability full verification: `target/all-failures-v15.log` completed with 2,583
passing, 24 failing, and zero ignored non-GSC2 tests. All 2,579 tests outside
the new standard-library source matrix pass, including all 865 service tests.
The remaining 24 failures are library compilation failures; its other four
tests pass. GSC2/self-hosting acceptance remains excluded from this run.
This clears the existing compiler regression backlog, not the language
conformance or expanded-library implementation backlog.

That frozen matrix has now completed in `target/standard-library-freeze.log`:
28 active tests, four passing and 24 failing, none ignored. Foundation, time,
float bit policy, and embedding/inventory integrity pass. The remaining family
tests fail during compilation. The frozen surface is 39 source fragments;
the unresolved grammar/contracts additionally include fixed arrays and const
parameters, crate-scoped visibility, associated effect-row tails, and complete
higher-ranked callback/RunsIn constraints. Source presence is not execution
conformance. The surrounding literal-inference regression run completed with
259 Core tests and 28 type tests passing, and service at 856 passing/five
failing, with the same five open control-scope failures.

Direct lexical resumption aliases now retain the original resumption identity
for escape checks, including shadowing and alias chains. Numeric literals now
resolve their expected type and record defaulted numeric constraints against
inference variables (cache 33). The generic-operation regression passes with
both the standard operator and a source-defined operator, including verified
wire execution. Captured control tokens and the expanded library's missing
mutable/destructuring binding and checked-tail features remain open.

Cache 34 includes a normally returning, zero-operation-clause path in callable
use analysis unless straight-line direct dispatch is proved. An effect row
permits an operation but does not guarantee that a callee performs it. A new
negative regression rejects an exact outer resumption used only inside an
optional inner dispatch with source diagnostic G5012, before VM lowering. The
positive nested indirect-call fixture resumes the outer continuation after
the inner handler and executes both a performing and a normally returning
callee, including wire verification. All 29 targeted outer-handler tests pass.

Cache 35 reuses the bounded structural pattern-domain proof for direct
operation dispatch, including exhaustive Boolean arm partitions. Both affected
move-capture handler tests pass, and all 29 outer-handler tests remain green.
It also structurally fuses proven immediate continuation-only closures into
their active clause, with argument temporaries preceding parameter bindings.
No runtime continuation capture or VM escape check is relaxed. All 45
resumption-focused service tests pass, including borrowed-result wire
verification and escape rejection. A new parameter-shadowing regression is
included in the passing full run. That regression also exposed an independent
resolution defect: the legacy `resume(k, value)` migration shorthand hijacked
a two-argument local callable named `resume`. It now applies only when there
is no lexical binding and ordinary value resolution is unresolved. The local
regression passes (`target/resumption-fusion-shadow-v4.log`); source-defined
and imported function regressions also pass in v15.

The three former lazy-label fixtures assumed eager compiler-controlled Boolean
branches after their operands had become ordinary source callbacks. Their
positive cases now use callback-local label destinations; a new negative test
retains the original outer-label capture forms and requires G4179 rather than
a VM failure. Cross-call label destinations still require structural fusion
or source rejection under language §11; this change does not claim that fusion
is implemented. Selected-callback cleanup and skipped-callback behavior pass
in the rewritten destruction fixture. The complete focused lazy run has two
destruction and 14 service tests passing (`target/lazy-label-current-v1.log`).

The plan-integrity gate and its 22 mutation tests pass. They establish only
plan integrity, not language or library semantic conformance.

1. Triage the remaining failures after default-prelude selection, separating
   phase-local fixture environments from remaining compiler semantic gaps.
2. Audit fixtures against their current specification obligations. Preserve their
   semantic assertions while updating genuinely obsolete source forms or setup.
3. Re-run the full non-GSC2 Stage 0 baseline after each coherent semantic change;
   compare individual test identities, not only aggregate totals.
