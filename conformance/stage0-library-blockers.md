# Stage0 and standard-library blocker map

Updated from the current source and cache 117 verification below,
with the earlier independent read-only compiler audits retained. This is a prioritized
implementation map, not an exhaustive conformance inventory: earlier failures
still mask later ones. The language and standard-library specifications remain
authoritative. Self-hosting is deferred while Stage0 and the library are the
active focus.

The latest completed main-tree source matrix is **16 passing / 15 failing tests**, none
ignored (`target/cache114-library-source-matrix-v1.log`, cache 114). This includes a source
embedding check, so it is not a count of 31 execution roots. Passing a root is
not proof that every generic API in it was exercised.
The 176-test bootstrap library API suite is a different, narrower test target.

### Latest implementation checkpoint

Cache 117 couples normal result values and storage snapshots in EscapeFlow,
using the existing shared continuation authority. Terminal branches retain their
actual transfers but do not contribute placeholder normal results. PlaceFlow
preserves a handler computation's result loans on its normal outgoing edge.
Direct operation evaluation now keeps an invoked terminal payload separate from
its absent result, and distinguishes it from an unexecuted operation whose
argument exits. No second evaluation fallback or new control walker is needed.

Verification has 471 distinct passes and three failing tests. Two unchanged
existing failures reproduce at pre-change `1263ea85` (a destroyed callable
environment and a carrier-reborrow rejection). The new generic-reference
label helper passes VM execution but leaves unsupported native `MakeLabel`
materialization; its native success test remains active and failing. Direct
completion transfers pass native O0/O2. No whole-target green claim follows.

The final full-library root **still fails** with 68 diagnostic records and no
suppression marker (`target/normal-result-library-final-v13.log`). The sorting
source correction removed its inference errors, but `split_at` still supplies
an opaque generic result before the views are bound. That missing provenance
remains a priority; normal-exit filtering is not a substitute for its contract.
See `implementation-progress.md` for exact regression and execution scope.
The source matrix remains the historical 16 passing / 15 failing result above.
General handler payloads, guarded storage, native handlers and self-hosting
remain open. The following source-only and cache 116 entries are historical.

The subsequent source-only sorting correction supplies the erased temporary
view's missing `T` as `SliceMut<'_,T>`. Positive annotation/constructor and negative
unconstrained-type regressions pass at O0/O2, including fresh/decoded positive
execution. The existing sorting root still fails with 54 diagnostic records;
its library helper no longer has inference errors, but nominal result provenance
and dependent loan/lifetime checks remain. Its application retains independent
callback lifetime, private API, borrow and quantity failures. This is not a
callback-inference bug in `sorting_swap`, which contains no callback.
See `implementation-progress.md` for the exact source-only gate. The full-root
count below predates this correction; no new matrix is claimed.

Cache 116 consolidates lexical, kinded projection normalization in the shared
trait solver and migrates signature comparison/validation, Core and executable
materialization to that authority. Partial substitution reads the existing
inference cells before normalization; an inferred call argument can therefore
unlock dependent projected parameters. The two graph `components_from` argument
errors at line 201 are gone. The implementation-only permission flag and the
duplicate consumer selection/normalization walkers are removed.

The verified boundary has 589 distinct passing checks; one unchanged obsolete
label-shape fixture also fails in the pre-change baseline and is not counted as
passing. See `implementation-progress.md` for exact gate scope and logs.
The full-library composition root still fails with 94 diagnostic records and no
diagnostic-limit suppression marker (`target/projection-normalization-library-final-v17.log`).
Remaining errors included Bytes/Slice and array-kind API mismatches, sorting
view inference, graph result/provenance checks, custom-Drop extraction,
unsafe UTF-8 operations, tail provenance and minimum-use obligations. No new
31-test source matrix or self-hosting acceptance result is claimed.

The following cache 115 and earlier checkpoints are historical.

Cache 115 / interface 21 retains and enforces effect-family and operation-local
prerequisites through shared declaration signatures, row-domain checking,
invocation checking and frozen Core application validation. Phantom operation
arguments, quantified bounds, exact callback equalities and capture lifetimes
are no longer dropped at those source boundaries. The eight new source groups
and the 446-test integration plus 171-test effect-boundary gates pass; see `implementation-progress.md` for
the exact scope and logs.

The full-library composition root now reaches body checking beyond the previously
rejected task declarations, but still reaches its unchanged 100-error diagnostic
limit. Its current errors include Bytes/Slice API mismatches, generic graph
projection checking, custom-Drop extraction, unsafe UTF-8 operations, tail
provenance and minimum-use obligations (`target/effect-contracts-library-v14.log`).
General polymorphic operation handlers and task-provider registration remain
unimplemented; this checkpoint is not task execution or library completion.

The following cache 114 and earlier checkpoints are historical.

Cache 114 / native ABI 12 supplies returned borrows of callable-owned capture
storage through the shared invocation input relation and the existing runtime
environment homes. Native initialization ownership is lent through exact sidecars,
not copied into a second active mask; nested VM/native calls and equal-address
zero-byte owners retain their logical identity. Generated imports share the checked
program-wide layout table and native ABI closure producer.

Field writes now share ordinary projection selection. Loan liveness follows live
aliases into their referents, rejecting a discovered short-lived stored-reference
escape in both ordinary and captured aggregates. Independent branded closure
contracts reuse the actual symbolic inputs of their sealed summary; unknown
enclosing mutation coverage is not converted to a fabricated observation.

The integrated gate passes 30 borrowed-callable, 37 native, 15 mutable-binding,
29 public native-bridge and 22 request tests. The twelve capture-storage sources
pass fresh/decoded VM, all-native O0/O2 and all three mixed partitions at O0/O2.
The previous G5023/expired-invocation-frame positive is now covered by that gate.
The final full unit gate passes 365 tests, for 498 distinct passing checks across
these targets. The intermediate adapter fixture correction is recorded separately
in `implementation-progress.md`.

Type-grouped capture updates remain conservative rather than exact storage joins.
Guard-correlated storage, cross-owner generic contract selection, and explicit
environment-death retirement across every runtime capture-home formation path
remain open. The fresh cache-114 source matrix above retains the earlier root
counts. Native handlers, general resumption transfer, full fusion, library
completion and self-hosted compiler acceptance are still outstanding.

The following cache 113 and earlier checkpoints are historical.

Cache 113 / native ABI 11 migrates reference identities into the existing resident
byte-transport domain and removes the per-home reference cache. Generated borrows,
move/restore dereferences, borrowed patterns and callable receivers consult the
backing storage's initialization contract. VM/native crossings retain its exact
logical paths and flags; zero-byte projections do not use address equality as
identity. Partial byte overwrites and frame expiry revoke authority. Generated
reads cannot recreate it from an ambient unsafe-execution flag.

The original captured unique-reference move/restore regression now passes fresh
and decoded VM, all-native and three mixed partitions at native O0/O2. Final
contract checks pass 357 unit, 29 public native-bridge and 22 request tests; the
complete native checkpoint has 35 passes and one new active source failure.
The latter returns a reference to storage owned by a capture, rather than returning
an incoming captured reference. It fails source G5023 before runtime. Its storage
projection and the subsequent environment-lifetime native returned-loan contract
remain open. Direct capture-slot borrows currently have the invocation lease.
Exact gates and stale ABI-test correction are in `implementation-progress.md`.

The freshly repeated source-library matrix above retains the same 15 failing
roots; they are not all classified compiler defects. Float parsing exhausts the
unchanged allocation budget, and shortest formatting lacks a proven tail carrier.
Other source provenance/inference/tail obligations, outdated fixture/API uses and
unfinished library implementations remain. Native owned handlers, full helper-
family and mandatory-tail activation fusion, cross-frame resumptions and guarded
storage also remain open. No conformance or self-hosting acceptance is promoted.

The following cache 112 and earlier checkpoints are historical.

Cache 112 admits captured-reference returns through the shared invocation
relation's complete reference-coverage proof. Ownership and escape authenticate
every non-static returned leaf against their existing input snapshots; incomplete
observations cannot authorize opaque results. Invocation events now retain the
evaluated receiver, while dispatch, fusion and payloads use a shared view through
its borrows. This repairs the previous capture-path coordinate mismatch.

The original factory-reference failure now passes unchanged, along with a unique
reference transfer, across fresh/decoded VM, all-native and all three mixed
partitions at native O0/O2. Source composition and escape/mutation negatives pass
at source O0/O2. The checkpoint passes 354 unit, 28 borrowed-callable, 38 callable-
control, 34 native and 22 request tests. Fusion remains 27 passes / one active
native `InstallHandlerOwned` failure. Exact gates, including the corrected stale
cache-test literal, are in `implementation-progress.md`.

Arbitrary opaque callbacks, complete nominal/array result projection, general
borrowed-referent sidecars, full helper-family and mandatory-tail activation fusion,
cross-frame resumptions and guarded storage remain open. No broad source-library
sweep was repeated; its latest matrix remains cache 105 above.

The following cache 111 and earlier checkpoints are historical.

Cache 111 / native ABI 10 implements typed generated capture loans across VM/native
entry. Both engines share actual capture homes and initialization state; public
native callback permissions and zero-byte scalar budgets are unchanged. The old
mixed captured-callable regression now passes. Pattern inspection also consults
the authoritative initialization state before reading direct/captured payloads.

The final native target has 32 passes and one newly preserved source failure:
a factory-produced callable returning its captured reference lacks frozen result
provenance (G5023), before runtime selection. The final unit target passes 352,
and the public native bridge passes 29. Existing native owned handlers still fail;
general borrowed-referent sidecars, source result provenance, full helper-family
and mandatory-tail activation fusion, cross-frame resumptions and guarded storage
remain open. Exact failed/intermediate and final gates are recorded in
`implementation-progress.md`; no broad source-library sweep was repeated.

The following cache 110 and earlier checkpoints are historical.

Cache 110 / native ABI 9 integrates ordinary callable environments into generated
execution. Native construction, invocation, copying and destruction share the
existing authenticated resident/capture storage, and the native/mixed runtime
consumers use the emitter's retained frame layouts and initialization paths.
All-native O0/O2 checks cover actual captures, factories/products, receiver loans,
independent copies, partial-capture cleanup and raw-memory authority.

The complete native target has 29 passes and one known failure. The original
captured-callable native/mixed fixture now passes its first native execution but
still rejects the mixed graph: capture restoration across generated host wrappers
and VM callback entry remains unimplemented. The failure is preserved, not waived.
Native owned handlers, borrowed/cross-frame resumptions, full helper-family entry,
mandatory-tail activation fusion and guarded storage outcomes also remain open.
No broad source-library/service sweep was repeated; its latest matrix is still
cache 105 above. Exact evidence is in `implementation-progress.md`.

The following cache 109 and earlier checkpoints are historical.

Cache 109 / verifier 38 carries checked factory constructors and typed capture
inputs through the shared invocation payload. Lifetime/place analysis, the
existing quantity solver and structural fusion consume the same relation.
Returned callable representations follow actual values rather than erased type
equality, including compatible branch alternatives. Generic resumption factories,
forwarded/aggregate captures and independently computed capture values execute
fresh/decoded at O0/O2. The main focused gate passes 152 tests.
The final destination-proof safeguard passes 12 supplemental checks.

Factory execution exposed a label-edge ownership bug: predecessor cleanup could
destroy an environment already copied to the successor. Leave now performs
parallel owned transfer across VM, verifier and native emission, preserving
partial initialization and retiring old carriers before installing new owners.
Native/mixed owned nominal-payload checks pass; these do not demonstrate native
captured-callable or handler support.

Full helper-family entry, native owned handlers, ordinary native captured
callables, borrowed/cross-frame resumptions, guarded storage outcomes and
mandatory-tail activation transfer remain open. Unsupported recursive factories,
incompatible joined layouts and borrowed/captured control replacement reject
explicitly. No broad library/service sweep was repeated; the source-library
matrix remains cache 105 above. Exact logs and limitations are recorded in
`implementation-progress.md`.

The following cache 108 and earlier checkpoints are historical.

Cache 108 migrates resumption capture admission into the shared source lifetime
analysis and structural fusion, removing the independent source alias walker
and immediate-closure rewrite. Body-sealed lifetime products are checked before
transformation. Explicit resumption quantities now use UseFlow rather than a
syntactic call counter; nominal label invocation authority comes from the shared
bound control product. Nested partially consumed capture storage relocates with
its initialization holes intact during cleanup. All 86 focused checks pass,
including fresh/decoded O0/O2 capture execution and invalid escape, quantity,
stale-proof, replay-safety and moved-field cases.

Unknown resumption inputs to generic factories still lack complete capture
proof/representation. Native owned handlers, ordinary native captured callables,
borrowed/cross-frame resumption transfer, full helper-family fusion and
mandatory-tail activation transfer remain open. No broad library/service sweep
was repeated; the source-library matrix remains cache 105 above. Exact logs
and limitations are recorded in `implementation-progress.md`.

The following cache 107 and earlier checkpoints are historical.

Cache 107 / verifier 37 fixes the captured-resumption product regression from
cache 106. The verifier now uses one structural resident-value record for exact
handler identity and possible control contents. Field extraction, moves, joins
and handler expiry preserve that distinction; runtime extraction checks a control
token's retained callable signature. All 25 focused resumption checks pass,
including fresh/decoded source execution at O0/O2 and invalid escape/forgery cases.

Native/mixed `InstallHandlerOwned` remains unsupported, as do ordinary native
captured-callable storage, general resumption transfer across borrowed storage or
ordinary call frames, full helper-family fusion and mandatory-tail activation
transfer. The latest broad source-library matrix remains cache 105 above; no
broad suite was repeated for this slice. See `implementation-progress.md` for
the exact final gate and remaining source lifetime-admission migration.

The following cache 106 and earlier checkpoints are historical.

Cache 106 extends lexical fusion through handler and resumption binders. Distinct
delimiters retain exact clause/continuation identities through Core, Evaluation
and Control MIR; resumption name fallback is removed. Nested/deep handler replay,
normal completion and abandonment cleanup execute in focused VM cases. Owned-only
callable captures now retain owned invocation authority.

Two new positive regressions remain active: a captured resumption passes ownership
but loses its snapshot brand at the bytecode verifier's product-extraction boundary
(G7042 `HandlerResumeUnavailable`), and native/mixed handler composition reaches
unsupported native `InstallHandlerOwned`. These are separate from the existing
ordinary native captured-callable ABI failure. Full helper-family fusion and
mandatory-tail activation transfer remain open. The broad service/library matrix
was not rerun; its latest completed evidence remains cache 105 above. Exact focused
logs and snapshot qualifications are recorded in `implementation-progress.md`.

The following cache 105 and earlier checkpoints are historical.

Cache 105 integrates structural fusion for lexical outer-label closures and
captured label aliases. Tagged environment products preserve ordinary residents,
borrowed receiver storage, strict inputs and destruction; mutable callable views
select their current constructor. Source resource/escape checks precede installing
transformed Core, which then receives independent validation and fresh analyses.
Per-callable loan facts are shared by escape and lowering. Reborrow payloads use
the shared invocation product's storage identity, not equality of copied contents.

The formerly failing captured-outer-label ownership source and four original lazy
callback sources now execute. Thirteen new integration groups cover fresh/decoded
O0/O2 execution, invalid ownership and backing-storage escapes, and owned control
capture execution through native/mixed boundaries. The separate ordinary native
captured-callable fixture still fails at its existing unsupported environment ABI;
the plain-label native/mixed forwarding fixture passes. Full helper-family fusion,
handler/resumption and mandatory-tail activation expansion, heterogeneous layouts,
complete proof erasure and unified guarded provenance remain open. This is not
full §11 conformance or completion of the compiler, library or self-hosting goal.
All 891 service and 176 library API tests and the all-target compile check pass.
The source matrix retains the same 15 failures; mandatory-tail retains its
activation-transfer ABI mismatch. See `implementation-progress.md` for exact
final gate logs and named failures; the source-closure audit is not self-hosting
acceptance evidence.

The following cache 104 and earlier checkpoints are historical.

Cache 104 erases resolved label proof values across checked runtime ABI
components. Tuple/array products, generic forwarding and internal projection
references share the physical map; resident data and cleanup remain intact.
Callers, callees and abandonment/environment/host-resident cleanup dependencies
retain their old representation together when a consumer still needs it.
Nominal identities and label-indexed effect families are not collapsed to unit.
Original and transformed Runtime MIR are independently validated.

The final selected run has 1,982 passes and the same 17 named failures as cache
102, with no ignores. The additional tuple-label failure preserved by cache 103
is fixed. All 891 service, 39 array/container and 176 library API tests and the
all-target compile check pass. SourceMap executes; the source matrix remains
16 passes and 15 failures. Separate native/mixed nested-product tests pass at
O0/O2, while a new captured-callable positive remains active and fails at the
backend's existing explicit unsupported-environment boundary.

This does not finish label lowering. Correctness-required helper/outer-label
closure fusion, full proof erasure through remaining callable/nominal/effect
boundaries, and native captured-callable execution remain open. Full
compiler/library conformance and self-hosting remain unfinished. See
`implementation-progress.md` for the exact final and targeted gate evidence.

The following cache 103 and earlier checkpoints are historical.

Cache 103 retains observed label-address obligations across structural callable
inputs, including aliases, captures and unknown prefixes. Exact local label
callees now lower to direct transfers after strict operand evaluation; helper
bodies are not skipped merely because their outcome is a label exit. Simple
aliases and returned labels execute without indirect label calls at O0/O2.

The selected gate has 1,974 passes, the same 17 prior failures plus a newly
preserved tuple-label execution failure, and no ignores. An isolated build of
cache 102 reproduces the tuple's native-storage type mismatch. This is an
existing proof-carrier erasure gap, not permission to give labels addresses.
All 891 service, 39 array/container and 176 library API tests and the all-target
compile check pass. The source matrix is unchanged at 16 passes and 15 failures;
SourceMap still executes. Full helper/outer-label fusion and proof erasure are
the next label-lowering obligations. Compiler/library completion and self-hosting
remain unfinished. See `implementation-progress.md` for exact evidence.

The following cache 102 and earlier checkpoints are historical.

Cache 102 gives compiler-created labels invariant nominal identities. Ordinary
bottom-returning functions cannot satisfy `Label<T>`, and generic inference
cannot unify distinct lexical brands. Invocation consumers share a directional
`Fn` view without replacing nominal value identity; intrinsic label evidence
also supplies unrestricted use. Direct and generically specialized loans of
labels reject, while ordinary generic borrowing remains valid. Frozen ownership
loans supply the specialization obligations, and independent Core/Control and
concrete validation retain the restriction. Replay uses the same quantity and
callable-effect contracts.

The final selected gate has 1,970 passes, the exact same 17 named failures as
cache 101, and no ignores. All 891 service, 39 array/container and 176 library
API tests pass, as does the all-target compile check. SourceMap still executes;
the source matrix is unchanged at 16 passes and 15 failures.

Full label conformance is still open: structural control fusion, active
destination resolution through opaque/structural callable boundaries and full
proof-carrier erasure are not supplied by nominal typing. The VM retains its
existing label control carrier. Guarded resource states, higher-order result
coverage, captured native/mixed execution, compiler/library completion and
self-hosting also remain unfinished. See `implementation-progress.md` for the
unsafe-acceptance regressions and verification results.

The following cache 101 and earlier checkpoints are historical.

Cache 101 retains positively observed invocation result dependencies alongside
unconditional coverage gaps. An unknown callback prefix no longer erases a
later captured-label getter's result, while the public coverage query still
reports unknown and cannot prove normal-only execution. Ownership adds known
result origins without granting disposal permission from partial observations;
escape consumes the same retained payloads. The final selected run has 1,960
passes and the exact same 17 named failures as cache 100, with no ignores.
All 891 service, 39 array/container and 176 library API tests and the all-target
compile check pass; SourceMap still executes. Full guarded resource states,
opaque/higher-order result coverage, generative label authority and structural
fusion remain open. See `implementation-progress.md` for the unsafe-acceptance
regression and the final gate.

The following cache 100 and earlier checkpoints are historical.

Cache 100 retains label provenance through value aliases, aggregate residents,
capture formation and ordinary captured-input returns. Label scope exits check
outgoing results, pre-existing storage identities and pending outer-exit
snapshots. Both escape and ownership consume normal payload projections from
the shared invocation relation while preserving declared result checks and
existing unique-reference result partitions. Previously accepted exported
callables carrying expired factory labels now reject. The final selected run
has 1,958 passes and the exact same 17 named failures as cache 99; all 891
service, 39 array/container and 176 library API tests and the all-target compile
check pass. SourceMap still executes. Structural fusion, full label-bearing
callable authority, opaque result coverage and guarded storage remain open;
the higher-order outer-label positive remains active and failing. See
`implementation-progress.md` for the regression evidence and exact gate results.

The following cache 99 and earlier checkpoints are historical.

Cache 99 consolidates lexical label dependency rules across elaboration,
independent Core validation, tail checks and escape checking. First-class label
values can no longer bypass the early unfused-closure check and surface only
as an internal CFG error. Label declarations discharge only their own body's
dependencies; missing, cyclic or stale input does not prove independence.
The final selected run has 1,950 passes and the same 17 named failures as cache
98. All 891 service and 176 library API tests and the all-target compile check
pass; SourceMap still executes. This is a lexical dependency product, not
complete value-alias propagation, label-bearing callable contracts or structural
fusion. The outer-label closure positive remains active and failing. See
`implementation-progress.md` for exact gate results and remaining boundaries.

The following cache 98 and earlier checkpoints are historical.

Cache 98 feeds sealed body-derived invocation outcomes and typed label payload
projections into shared continuations, ownership and escape checking. Generic
helper label exits preserve their destination's move/minimum-use state and
reference provenance, including backing loans after local rejoin. Static
callee contracts remain usable after an unknown prefix without fabricating an
unresolved label operand's destination. SourceMap now compiles and executes.
The final selected run has 1,944 passes and 17 failures: 15 unchanged source
cases, the existing tail-transfer ABI case and a new active positive for an
outer-label-capturing higher-order closure (G4179). All 891 service,
39 fixed-array/container and 176 library API tests pass, as does the all-target
compile check. Full guard correlation, operation/cancellation resource states,
shared storage identity, outer-label closure fusion and captured native/mixed
execution remain open. See `implementation-progress.md` and
`docs/compiler-architecture.md` for evidence and scope.

The following cache 97 and earlier checkpoints are historical.

Cache 97 consolidates captured and explicit invocation may-store rules across
ownership and escape checking. It retains callback stores through borrowed
receivers, higher-order calls, nested captures and selected trait methods,
without treating an unconstrained generic forwarder as an invocation. Factory
forwarding preserves typed capture inputs; declaration substitution and
selected implementation binding are shared with materialization. Full guarded
control, unified storage identities and captured native/mixed execution remain
open. The final selected run has 1,931 passes and 17 existing failures: the
tail-call ABI case and 16 source-library cases. All 891 service, 39 fixed-array
and 176 library API tests pass, as does the all-target compile check. See
`implementation-progress.md` and `docs/compiler-architecture.md` for exact
logs and the migration's boundaries.

The following cache 96 and earlier checkpoints are historical.

Cache 96 consolidates capture formation rules across Core contracts, ownership,
escape and quantity checking. The factory-local closure escape regression now
rejects borrowed local slots while owned captures preserve their referents'
dependencies. Nested closures and aggregate wrappers retain those dependencies.
One container and five service fixtures had the same invalid source pattern;
their original sources remain rejection checks and their owned positive variants
pass. Final per-target gates have 1,919 passes and 17 existing failures: the
tail-call ABI case and 16 source-library cases. All 891 service, 34 fixed-array
and 176 library API tests pass. Shared invocation/store provenance and complete
guarded control remain open; see `implementation-progress.md` for exact logs
and the limits of this migration.

Cache 95 consolidates local continuation reasoning into a frozen rule product
shared by ownership, escape and quantity checking. Definite and conditional
transfer payloads preserve their actual destinations and rejoined owner states;
missing/stale products are rejected. The selected integration run has 1,913
passes and the same 18 named failures: the factory-local closure escape
negative, tail-call ABI case and 16 source-library cases. All 891 service and
176 library API tests pass. This is the first architectural migration slice;
full interprocedural guarded control and storage/capture provenance remain
open. See `implementation-progress.md` and `docs/compiler-architecture.md`.

Cache 94 enables callable raw storage with execution-domain environment leases;
the previously ignored execution test and all 33 fixed-array/container tests now
pass. The broader runtime batch has 756 passes and the existing tail-transfer
callable ABI failure, with no ignores. A captured-reference receiver regression
also passes fresh/decoded O0/O2 execution after native carrier normalization.
The original returned-closure service fixture borrowed dead factory-local slots:
the lawful positive now explicitly owns its captures, and the original source
is preserved as an active failing escape-checking regression. Captured
native/mixed invocation, higher-order capture/store propagation, guarded
control/resource integration and physical cost conformance remain open. See
`implementation-progress.md` for evidence and the checkpoint's limits.

Cache 92 retains callable capture footprints in logical owners and records
captured owner stores. The combined run passes 1,860 tests, with the same five
generic-helper exit and 16 source-library failures. A separate, explicitly
ignored callable raw-storage execution test was run and fails at unsupported
native Callable layout; its compile/decode positives are not runtime acceptance.
Mixed capture/parameter and higher-order store propagation, nested closure
footprints and guarded ownership integration remain open.

Cache 91 fixes compiler dependence on ambient floating-point modes, including
literal products, cached artifacts and LLVM partition callbacks. Its combined
main-tree run passes 1,687 tests with the same five generic-helper exit and
16 source-library failures. All 891 service and 176 library API tests pass.
Callable raw storage, complete captured native invocation and guarded
control/resource integration remain open.

Cache 90 integrates sealed, body-derived callable control summaries and preserves
earlier invariant-selected callback type arguments while retaining ordinary value
joins. Its combined run passes 2,116 tests; the same five generic-helper exit
cases and 16 source-library cases fail. Per-call summary consumption in ownership
analysis is not active yet. The source matrix and library API counts are unchanged.

Cache 89 shares the floating-environment guard across VM/native execution and
foreign callbacks. Its combined run passes 2,346 tests with the same five
generic-helper exit failures and 16 source-library failures. All 891 service
and 176 library API tests pass. Compiler-time floating-point determinism and
full guarded control contracts remain open; see `implementation-progress.md`.

Cache 88 integrates lifetime-quantified borrowed `Fn`/`RunsIn`, stored callback
implementation bounds and exact associated output/effect equalities. The
isolated array and iterator probes no longer report G4198/G4147/G4169, but still
reject unrestricted callback cancellation over generic linear owners (G5024).
They are guard-negative regressions, not new passing source roots. Stored
capture lifetimes and independently verified receiver permissions are retained;
written callable ABIs cannot erase unproved invocation prerequisites. The
combined main-tree run passes 2,322 tests, with only the five known generic-helper
exit cases and 16 source-library cases failing. All 891 service and 176 library
API tests pass. See `implementation-progress.md`.

The following cache 79 and earlier checkpoints are historical.

Cache 79 fixes the undemanded generic availability-release failure while keeping
unsealed runtime witnesses inadmissible. The native-allocation/array integration
batch passes 1,020 tests; the subsequent GAT integration batch passes 1,701,
including all 891 service and 38 semantic-conformance tests
(`target/integration-gat-broad-v1.log`). General owning-container region preservation
and native partial-owner metadata are newly confirmed open issues. The cache 78
and earlier entries below are historical; see `implementation-progress.md`.

The historical cache 78 checkpoint's mixed LLVM/VM ordinary-call bridge
passes 63 native/bridge/request tests. The explicit availability-release Core
operation still fails lawful generic semantic lowering with G6001 (37/38
semantic-conformance tests pass). The last service diagnostic failure passes
its targeted recheck, but there is no new full green service or source-library
matrix run. See the top checkpoint in `implementation-progress.md`; the cache
77 results below are earlier evidence, not the current complete acceptance state.

Cache 77/interface 18/bytecode 71/verifier 34/schema 115 integrate fixed arrays,
final lexical-label tail discharge, stored-reference/unique-reborrow
provenance and associated-item domain/result/outlives contracts, plus exact
local-label and conditional callable-invocation tail proofs. The associated
and provenance integration suite passes 517 tests. Path, foundation, and
storage have individual passing source checks; the full source matrix has
not been rerun. These diagnoses below are history, not claims that already
implemented mechanisms remain absent. See `implementation-progress.md` for
the exact evidence and limitations.

Lifetime-universal user-trait function/impl predicates and exact associated
equality forwarding are now integrated (`fdf1e948`), with 496 combined
integration tests and five quantified unit tests passing. Remaining lanes:
quantified RunsIn, general quantified projection-domain validation, non-lifetime
binders and borrowed/stored callback evidence; reference-bearing fixed-array
paths. Conditional custom-Drop deconstruction enforcement is now integrated
from `b5fb972e`, with six O0/O2 fresh/decoded and frozen-checker test groups.
General ordinary
minimum-use checking is integrated from `08110256` with 221 focused tests,
including the now-active linear-array regression. Binary passes its real decoded source execution with the
combined verifier (`target/merged-binary-v1.log`, 8.88 seconds). I/O previously
finished compilation under LLVM opt1 and reached VM tail
provenance (`flush_pending`), distinguishing this from its earlier 590-second
Cranelift timeout. The combined-source LLVM opt1 recheck built in 77 seconds,
then exhausted the total 590-second budget (exit 143) without reporting a
semantic result (`target/merged-io-llvm1-v1.log`); this needs stage/cost isolation.
The generic
supertrait facade G4147 is fixed by selecting associated constants from
implementation evidence; its focused service regression passes. Associated
checks exposed SliceIter's missing `T: 'a` source requirement (G4305), now
corrected in all four iterator trait implementations. Nominal declaration
bounds now survive into field checks, native fingerprints and instantiated
application checks. Seven source tests plus two hostile/fingerprint tests
exercise this mechanism. Iterator now reaches later assignment, normalization,
reference and tail diagnostics (`target/nominal-iterator-v1.log`), not a passing
root. Rigid wrapper type/row normalization, inherited method entailment and
transactional associated-row subset matching now have focused regressions;
55 final nominal/row/type tests pass. The latest completed iterator check reaches
eight diagnostics (`target/rigid-iterator-v4.log`), still not a passing root.
Ownership/capture and borrowed-array fixes are integrated with 427 focused tests
passing. The latest combined service recheck reaches 890 passing / 1 failing;
the remaining diagnostic wording fix is under verification. Native LLVM's first
executable checkpoint is integrated with 502 verifier/native/tail/bridge tests
passing (overlapping library unit tests); mixed generated LLVM-to-VM execution
remains in development. Exact `Available<E>` release proof preservation is also
being reconciled with ordinary minimum-use enforcement.

The full float parser has reached execution after compiling and verifying
decoded bytecode, but hit the cumulative 16,777,216-element allocation limit.
The latest conservative callable-mutation refinement passes reduced real
parser execution (`float_tail`: `1.5` and invalid `1x`). Neither full parser
acceptance nor a new complete source matrix is claimed.

## 1. Expected-reference reborrowing — highest immediate shared payoff

Confirmed missing compiler operation: passing an existing `&mut T` to a `&T`
parameter must create a shared reborrow of the referent, not move the unique
handle or equate shared and unique types. Language sections 5.3 and 13 require
expected-reference-selected reborrowing.

`core.rs::align_lifetime_types` requires equal reference mutability, while the
call elaborator subsequently unifies without materializing this shared borrow.
Affected source sites include `binary.glorious` 63/69/99 onward,
`storage.glorious` 49/82/111/129/157/227/244/278, and heap/algorithm calls.
Some moved-place errors follow the initial call failure; do not assume every
remaining ownership/tail diagnostic is a cascade.

Implement a real Core borrow with its place, region, and NLL facts. Verify
repeated shared calls followed by mutation, a returned shared borrow that must
suspend mutation, computed receivers, and fresh/decoded O0/O2 execution.
Keep shared-to-unique conversion, escaping reborrows, and unique-referent
lifetime covariance rejected.

## 2. Generic implementation contract normalization

High-confidence static diagnosis of the four generic I/O G4147 failures:
`signature.rs::validate_associated_type_definitions` normalizes required and
provided method contracts with global solver queries, without the enclosing
implementation's bounds. Under `R: Read`, the selected associated row of
`BufferReader<R>` must reduce to the row of `R`. Concrete MemoryCursor methods
do not show this failure.

Normalize in an isolated lexical implementation environment, preserving
associated equalities as well as ordinary trait assumptions. Add generic
Read/BufferedRead/Write wrapper regressions, imports, mismatched-row negatives,
and a missing-bound negative. Do not grant the implementation's conditional
evidence globally or let a method introduce stronger requirements.

## 3. Fixed arrays — an end-to-end feature, not parser sugar

The initial scanner bug is fixed: bracket groups no longer terminate a
declaration at `[T; N]`'s semicolon. Scanner tests also cover adjacent `=<`,
`>=`, and `>=<` in associated bindings. Array type support is still absent.

Required implementation work:

- Add a distinct fixed-array header/body type form. Both generic-argument
  parsers must distinguish `[T; N]` from quantity `[lower, upper]`.
- Retain a typed `usize` const term in semantic type identity. Reuse existing
  const inference, generic, projection, arithmetic, and substitution machinery;
  do not discard N or replace it with an unchecked runtime length.
- Extend every normalization, unification, substitution, leak/occurs check,
  fingerprint, instance, layout, and closed-type validation walk.
- Give literals compile-time arity, expected element typing and inferred N;
  add exact/remainder patterns and fixed-product exhaustiveness.
- Treat arrays as inline residents for recursion, moves, destruction and
  capability derivation. Zero length is not the same as nonempty zero-byte
  residents: `[LinearZst; 2]` still has two obligations.
- Preserve length through MIR, VM descriptors, codecs, independent admission,
  and both VM implementations. Reject malformed constructors, out-of-range
  projections and dynamic resize operations on fixed storage.
- Add compact contiguous native layout using checked repeated stride/count;
  extend reads, writes, projections, promotion, and raw-memory access without
  expanding huge arrays into tuple metadata. Preserve logical identity of ZST
  residents and partial-initialization cleanup.

Exercise all five library array helpers, failed Vec conversion returning its
owner, callback order/nonlocal exits/partial initialization, nested arrays,
overflow and forged bytecode; then rerun random, format, UTF-8 and composition.
Selected-target pointer width remains a separate required portability gap.

## 4. Associated-item contracts and general quantified evidence

Implementation associated type/effect equalities now survive elaboration and
participate in selection, including inherited items and GAT arguments. This
does **not** finish the surrounding associated-item feature family.

True missing contracts, required by the specs:

- GAT domain requirements such as `type Item<'a> where Self: 'a`.
- Declared result bounds such as Graph's `type Node: Eq + Hash + Use<[0,*]>`.
- General type-outlives and region-outlives predicates, distinct from traits.
- Universal implementation bounds, non-Fn quantified traits, and quantified
  compiler-owned `RunsIn` proofs.
- Borrowed/stored callback evidence: current universal callable checks handle
  known function items but do not justify the library's unique-borrowed stored
  callbacks and their post-call environments.

Introduce explicit predicate kinds and carry contracts through signatures,
substitution, imports and identities. Prove a GAT's domain at projection use;
check result guarantees for defaults/implementations and make those guarantees
available to generic consumers. Use rigid universes and leak-checked scopes
for universal proofs, with separate exact Fn/RunsIn evidence. Audit associated
equalities in coherence as well as selection; selection tests alone do not
prove overlap/disjointness behavior.

Tests must cover sequential vs overlapping lends, escaping results, stronger
impl requirements, Graph consumers, imported/defaulted GATs, captured callbacks
through fields, wrong capture access/After, static-only evidence, and existing
universe leak negatives. Do not delete guards, bounds or quantifiers to compile
the library.

## 5. Library source and test integration defects

Confirmed independently of the compiler feature gaps:

- The source-test dependency lists omit integer/integer_text for codecs and
  UTF-8/FFI users of `integer_digit`; source_map omits its UTF-8 dependency.
- float_shortest calls nonexistent `String::as_bytes`; use the existing
  `String::as_str` then `Str::as_bytes` composition.
- Some application tests call private `__g1_abort`; use public assertion or
  error paths, not increased visibility of the runtime primitive.
- Bool equality needs the specified structural Result/unit Eq implementations.
  Bool is an alias; do not add a compiler exception or overlapping alias impl.

Correct dependency closure and source contracts, then execute the affected
tests. Clearing these errors does not imply those modules have no later bugs.

## 6. Two reduced reproductions still needed

**Path byte literals — medium-confidence cause.** All four G4107 sites compare
u8 slices against `b"."`/`b".."`. All-or-nothing zonking in contextual argument
typing may leave an already-solved element inference variable hidden behind an
unresolved lifetime; literal recognition then falls back to scalar Bytes.
Reduce a generic two-operand slice comparison with independent borrow regions
before changing partial-resolution behavior.

**Float parsing mandatory tail — medium-confidence cause.** The sole G7042
appears after frontend acceptance. A helper's mutation of local scratch Vec
storage appears to clear independence facts for an unrelated incoming ratio.
First retain the failing function/PC in diagnostics. Then distinguish local
write footprints, address independence and resident-content independence.
Keep direct/helper/raw-copy publication of current-frame references rejected;
do not whitelist Vec, source function names, or bypass tail admission.

## Completion evidence still required

Beyond clearing these roots: finish the canonical library API/prelude migration,
remaining concrete iterators/collection operations, owner-bound byte-reader
marks, legitimate UndoLog interior mutation, structured diagnostics and host
adapters, bounded streaming fingerprinting, ownership negatives and portability.
The current library README records these outstanding implementation families.
Full composition, generic API instantiation coverage and the specification's
complete acceptance contracts must all pass before claiming Stage0/library
completion. A green bootstrap suite or a smaller source selection is insufficient.
