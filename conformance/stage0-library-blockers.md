# Stage0 and standard-library blocker map

Updated 2026-09-08 from three independent read-only compiler audits, current
source, and `target/associated-bindings-focused-v5.log`. This is a prioritized
implementation map, not an exhaustive conformance inventory: earlier failures
still mask later ones. The language and standard-library specifications remain
authoritative. Self-hosting is deferred while Stage0 and the library are the
active focus.

The latest completed source matrix is **10 passing / 20 failing roots**, none
ignored. Passing a root is not proof that every generic API in it was exercised.
The 175-test bootstrap library API suite is a different, narrower test target.

### Latest implementation checkpoint

Cache 79 fixes the undemanded generic availability-release failure while keeping
unsealed runtime witnesses inadmissible. The native-allocation/array integration
batch passes 1,020 tests, including all 891 service tests; later GAT contextual
inference passes its focused tests. General owning-container region preservation
and native partial-owner metadata are newly confirmed open issues. The cache 78
and earlier entries below are historical; see `implementation-progress.md`.

The integrating tree is now cache 78. Its mixed LLVM/VM ordinary-call bridge
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
