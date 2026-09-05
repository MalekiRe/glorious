# Source admission

`src/request/request.glorious` implements the first input-admission component
of the request facade. It is not yet `CompilationRequest::normalize` or a
complete immutable world.

Logical paths have a sealed representation. A path builder checks one byte
per step and rejects empty paths, empty slash-separated segments, backslashes,
and the exact segments `.` and `..`. It preserves the accepted spelling:
Unicode, NUL, colons, and dot-containing names are not silently rewritten or
rejected beyond the Rust `LogicalPath::parse` contract.

A source builder consumes a supplied key, package, admitted path, bytes, and
digest. Its transitions preserve the reference normalization order:

1. Derive the exact file key from package and logical path; reject a mismatch
   with both supplied and expected identities.
2. Hash the actual source bytes; reject a mismatch with the file, supplied
   digest, and actual digest.
3. Validate UTF-8 and build the existing sealed immutable source blob.
4. Allow one final extraction of the admitted source after checking cancellation.

Input failures remain distinct from cancellation, work/byte/identity-encoding
limits, closed builders, premature extraction, and invariants. Failed steps,
cancelled extraction, explicit abort, and premature extraction discard owned
staging. Work already performed is not refunded. Ready builders still check
cancellation. Borrowed package/path/blob accessors preserve their owner's
lifetime; callers cannot construct an admitted result by supplying a digest.

The path scan is stepped. Hashing and UTF-8 validation still use the existing
synchronous library leaves, with their logical work charged before execution.
The blob constructor currently rechecks/hashes its owned bytes; both passes
are charged. This does not establish physical allocation, copying, host
polling latency, or hierarchical memory-lease certification.

## Executed comparison

`gsc2_request_source_admission_matches_reference_validation_and_drives_real_queries`
passes with tuple `[22, 20, 10, 46, 2]`:

- 22 exact path outcomes/spellings, generated from Rust `LogicalPath::parse`.
- 20 source cases generated from Rust request normalization: empty and Unicode
  sources, invalid UTF-8, forged file keys, forged digests, and simultaneous
  corruptions. Error fields compare every digest bit, not only the category.
- 10 path lifecycle checks and 46 source lifecycle checks, including step and
  extraction cancellation at every source transition, cancellation after
  readiness, work retention, capacity failure, abort, and one-shot completion.
- Two real line-index demands through the production registry, starting from
  the admitted source, exercising cold execution and a repeated demand.

The audited selected run `target/compiler-check/run-77329q84/report.json`
passes in 112.40 seconds, bound to source-lock SHA-256
`802fb74122125851338f4a929482957b9ebbf9b6ec4b267d7779f4b621ad417d`.
The independently verified artifact is 3,412,815 bytes, digest
`38add25898c397b35bc606888a5886c98bc4b46461cabb3d263ff3b603e2e681`.
The full batch uses 657,239 work ticks and 688,209 charged allocation elements.
This is selected-test evidence, not a complete-suite or bootstrap certificate.

C0's existing authoring profile requires binding custom borrowed path views
before nesting them into other calls. The fixture uses those explicit locals;
no lifetime escape check was relaxed. Initial attempts also used unsupported
destructuring-let and reference-subject enum patterns; production now uses
ordinary handler patterns and a dereferenced borrowed enum subject.

## Package aliases and capability names

`src/request/names/names.glorious` adds sealed, stepped name admission.
Package aliases replace hyphens with underscores in the prefix before the
first `@`, require an ASCII letter/underscore initially and ASCII
letters/digits/underscores afterward, and preserve the full original package
identity separately. The version suffix is deliberately not revalidated:
that matches the Rust package-alias contract.

Capabilities retain exact spelling. Empty strings, any asterisk, and the
Unicode White_Space characters are rejected. NUL, zero-width format characters,
non-ASCII letters, punctuation, and other values are not rejected beyond the
reference contract. A step reads one complete scalar through
`Str::char_at`; it does not split UTF-8 bytes into independent characters.

Both builders check cancellation before each step and final extraction, enforce
their byte ceilings, discard failed/aborted/prematurely extracted staging, and
finish once. Alias capacity is checked before appending. Work is not refunded.
This is logical work/capacity evidence, not physical allocation or memory-lease
certification.

The audited name fixture passes 719 checks with tuple `[277, 342, 100]`:
277 exact aliases/rejections, 342 capability outcomes, and 100 lifecycle/control
checks. Native oracle inputs cover all ASCII code points, the reference's
complete 25-character whitespace set and its neighbors, UTF-8/format characters,
version suffixes, and exact error payloads. Cancellation tests cover step and
extraction at every transition, including readiness.

Evidence: `target/compiler-check/run-vfxzfe45/report.json`, 107.88 seconds,
source lock `dd6607c386e89b4c0c28eaf9f1cc4a811a4c8301cd50184f2cc8ce39294b87bb`.
The 455,340-byte verified artifact has digest
`a17d9b72c71789e48d6c30a3faef52cb8a9ebf85a608d03d98ee83801e530eec`;
the complete batch uses 2,084,879 ticks and 1,916,777 charged allocation
elements. This is selected-test evidence.

## Whole-request package and capability namespace

`src/request/namespace/namespace.glorious` consumes a sealed source collection,
the actual root package, and raw capability strings. It constructs the ordered
set of packages from sources plus the root (which need not own a source),
skips repeated packages, derives aliases, and rejects exact alias collisions
with their first/second full package identities. Root duplication is removed
before enforcing the distinct-package ceiling. Aliases remain in package order;
an exact String-keyed map supports lookup independently of vector order.

Capability strings sort by UTF-8 bytes and all are validated before checking
adjacent duplicates. Thus an invalid capability still takes precedence over
an otherwise earlier duplicate, and package errors precede capability errors.
The version suffix, NUL, Unicode whitespace/format distinction, and every
observable rejection payload retain the native rules. This is namespace
admission, not runtime-manifest validation or a complete normalized world.

The shared `kernel/text_order` adapter drives the stable index merge sorter
with one byte-comparison quantum per step. It moves strings into canonical
slots; extraction leaves holes without changing the fixed extent, shifting
the remainder, or permitting a second take. Both adapters use actual caller
controls, discard aborted/failed/premature staging, and check cancellation
again at final extraction. String hashing/probing and VM physical transfers
remain synchronous substrate work: these tests do not certify physical costs,
per-probe polling, or hierarchical memory leases.

The audited fixture `run-qokylbx8` passes in 192.01 seconds, with tuple
`[22, 116, 8, 7, 11]`: 22 exact native namespace comparisons, 116 lifecycle/work
checks, eight capacity/abort checks, seven text-sort reference cases, and 11
sorter protocol checks. It tests root-only packages, repeated sources/packages,
version/hyphen collisions, genuine `Ab`/`BA` hash collisions, Unicode and NUL,
simultaneous invalid/duplicate capabilities, exact capacity limits, missing
lookups, retained fields after consuming extraction, and repeated/out-of-range
text-slot takes. The verified artifact has 1,551,938 bytes and digest
`5f9f24eb442ce4fa740fa93e55e329b0c902d6665f7b7e4817a5433ad339f8bb`;
the source lock is
`cda11fe875a47e263fefa57a26d8c2134dea8e0541a3450a8527473634ff4dfd`.
The batch uses 6,112,143 ticks and 7,060,564 charged allocation elements, peak
depth 24. This is selected-test evidence, not full-suite or self-host evidence.

The initial fixture failed with hidden-parameter reference provenance errors.
See the minimized reproduction and focused Stage0 correction in A20 of
[authoring.md](authoring.md). A separate new test helper used a non-tail
completion expression that C0 could not lower; an ordinary helper function
preserves that comparison without changing MIR or accepted-language scope.

## Canonical option maps

`src/request/options/options.glorious` consumes an ordinary
`HashMap<String, String>` and builds a sealed canonical index over its residents.
The request's semantic and codegen maps can share this implementation without
sharing their fingerprint sections. Normal map insertion chooses the last
value for an equal key; option admission introduces no duplicate-key rejection
or spelling restriction. Empty keys/values, whitespace, asterisks, NUL, and
Unicode are retained exactly.

`HashMap::entries` and `HashMapEntry::{key,value}` are ordinary shared library
views with explicit owner lifetimes, no hashing/duplication bounds, and no
mutable-key exposure. Resident order is deliberately unspecified. The option
builder owns the map throughout admission, drives the shared stable index
sorter with byte-stepped key comparisons, and checks key/value byte ceilings
in canonical order. No resident key/value needs to be cloned to sort it.
The sealed result offers indexed canonical rows and ordinary exact lookup;
consuming it back into a mutable map relinquishes the canonical wrapper.

The builder checks real caller controls, work/count/byte limits, cancellation
at each transition and final extraction, one-shot completion, and cleanup
after failures, abort, or premature extraction. The comparison driver and
index scheduler share those controls. Hash-table operations and physical VM
transfers retain the substrate caveats above; no physical copying or polling
certification is inferred from these logical bounds.

The standard-library resident-view regressions pass (10.98 seconds), including
move-only values, colliding keys, replacement/removal, and rejection of a
borrow escaping a local map. The source oracle fixture compares ordered rows,
lookup, and consuming extraction with Rust `BTreeMap` histories. A non-audited
smoke run passes `[14, 108, 10]` in 201.30 seconds: 14 reference histories,
108 lifecycle checks, and 10 capacity/abort checks. That snapshot includes the
new role metadata but predates the manifest-input builder. A subsequent
non-audited full-closure smoke including the builder also passes (146.34 seconds).
The audited three-entry run `run-fw0gxn2u` records passing option and namespace
tuples, but fails overall because the manifest fixture's glob import triggers
C0's known private-module resolution issue (169.24 seconds). Its source lock
is `3721cdd07d73239e51256d9681c208299086c6552b1127e409f886c014d7510f`.
The option artifact is 505,721 bytes, digest
`4753a871be6f0e79a5c3f70584609657731910615a75e48b92349b8e07db33d8`,
with 5,941,522 work ticks and 5,930,185 charged allocation elements. Those
individual results do not turn the failed batch into a pass. The subsequent
audited four-entry run `run-_ikml_nz` passes the option, namespace, runtime
manifest, and registry fixtures together in 238.76 seconds. The option tuple,
artifact digest, and execution counters are unchanged. This remains one
normalization component, not an admitted complete world or compiler service facade.

## Runtime-manifest input admission

`src/runtime_manifest/input/input.glorious` owns primitive and host selectors,
sorts through the shared stepped index scheduler, validates all roles before
duplicate-role rejection, then validates all host imports before duplicate
module/name rejection. Only successful final extraction creates its sealed
wrapper. The wrapper retains the standard-library package and all selector
fields; consuming it yields the actual canonical vectors. It does not bind
declarations, prove ABI compatibility, or grant runtime authority.

Comparisons advance by field or UTF-8 byte. Capability validation uses the
same explicit Unicode whitespace predicate as request names, additionally
rejecting asterisks; NUL and non-whitespace format characters are retained.
Capacity guards cover both collection counts and every selector text field.
Error construction charges separately for copied module/name bytes. Cancel,
early extraction, work exhaustion, and abort discard staging. Physical VM
copying and hash/transport polling certification remain open.

`src/runtime_manifest/runtime_manifest.glorious` and `src/types/types.glorious`
represent scalar and existing runtime-role identities. Derived declaration
ordering is separate from stable encoding tags. Malformed raw float conversions
have a total order but no stable tag; validation returns the exact invalid
role, following A22. `spec/runtime-authority.tsv` lists all 183 valid canonical
selector/tag pairs. The native finite-inventory regression checks it against
the private encoding; the new executable source fixture checks source names,
tags, order, all 648 conversion shapes, canonical/error fields, lifecycle
properties, and resource boundaries.

The audited fixture now passes `[69, 183, 648, 1, 20]`:

- 69 complete native canonicalization/error outcomes: all six three-selector
  and three-host permutations, empty inputs/selector spellings, verbatim library
  identities, duplicates, invalid-role precedence, host-validation precedence,
  every Unicode whitespace scalar, accepted NUL/format characters, arbitrary
  module/name/symbol bytes, long shared prefixes, and reversed host lists.
  Successful cases compare every field both through the sealed borrowed view
  and after consuming extraction; rejection cases compare exact error fields.
- 183 role name/tag/validation witnesses in native derived order, with adjacent
  forward/reverse comparisons and reflexive comparisons.
- 648 scalar conversion shapes: all 18 x 18 x 2 possibilities, including 50
  admitted conversions and 598 exact invalid roles without tags. The source
  also checks ordering across the complete raw conversion sequence.
- One exhaustive lifecycle property over the two-selector/two-host fixture:
  cancellation via step and finish, abort at every transition through readiness,
  all premature finishes, every insufficient work budget, exact-budget success,
  one-shot extraction, and retained work charges. The property checks its full
  expected assertion count against the actual positive transition/work counts.
- 20 capacity checks: both collection bounds, every text field, exact limits,
  zero-capacity empty admission, and closed-state cleanup.

It passes alongside namespace/options/registry in 238.76 seconds:
`target/compiler-check/run-_ikml_nz/report.json`, source lock
`fcc5a08568e8e699649fb23ff666a0cbe02b706ba918ae3ae06fd41688d37e86`.
The 1,709,551-byte independently verified artifact has digest
`eccbfdec84f77a125a8246a0db5162fc3d34c790abedbc514e2ff08f6ea1bf7c`,
13,092,852 work ticks, 15,530,292 charged allocation elements, and peak call
depth 18. This is within the unchanged VM limits but is not a physical
allocation or compiler-scale performance certificate. The full source-suite
time gate and self-host bootstrap remain open.

Initial fixture compilation exposed the known glob import/privacy issue,
an incorrect slice borrow, unsupported scalar arithmetic forms, and non-tail
boolean completions. The fixture uses named imports and tail helpers without
removing assertions. A minimized standalone reproducer confirms C0 rejects a
u64 comparison in a call argument but executes the equivalent tail helper;
a temporary MIR trace also identified an argument-position `!=` completion.
That trace and the temporary diagnostic program were removed before the
passing audited run. No Stage0 MIR rule was changed for these authoring forms.
Source selector-name parsing and declaration-bound manifests remain open.

The subsequent complete selected admission/publication/registry group passes
all nine native entries in 381.31 seconds, under the same source lock:
`target/compiler-check/run-wf_8rujk/report.json`. It executes source, name,
bootstrap, collection, namespace, option, and runtime-manifest admission,
the three publication scenarios, and all eight registry histories. Every
recorded result tuple passes its independent harness assertion. Neither the
590-second command ceiling nor the memory/VM limits changed. This verifies
the affected group, not the remaining 31 source-suite entries or self-hosting.

## Bootstrap-stage admission

`src/request/bootstrap/bootstrap.glorious` consumes the actual admitted source
values alongside the stage contract, compiler producer, and optional
`optimization-level` value. It does not trust caller-supplied source lengths.
The header checks preserve Rust's precedence: positive ordinal, optimization
range, positive limits, actual compiler producer, then seed/non-seed predecessor
rules. Source count is checked before a stepped byte total; the byte limit is
checked before exact canonical optimization-option spelling. Successful
extraction retains all stage fields and the original admitted source values.

Builders own their staging, use the caller's controls, charge each step, check
cancellation even when ready, and discard failed/aborted/prematurely extracted
state. Error reasons are owned strings with the exact reference text. The
initial static-view error representation exposed C0's conservative borrow
handling around returning error values; the source uses owned error data.
This does not establish a fix for that authoring limitation. Explicit u64/u8
wrapping helpers and named mode locals also avoid the untyped-generic constant,
direct narrow-integer MIR arithmetic, and borrowed-temporary authoring limits.

The request module now contains all six modes, complete build identity fields,
bootstrap stage/limit types, the exact mode tags, and the current Stage0 build
constructor. These types and the standalone stage builder are not a complete
normalized world. Logical work/cleanup checks do not certify physical memory,
transport polling, or hierarchical memory leases. The overflow guard is present,
but tests using real small source buffers do not execute u64-total overflow.

The audited current-closure fixture passes tuple `[145, 80, 13]`:

- 145 Rust-normalization cases, including individual/pairwise corruptions,
  seed/non-seed provenance, maximal ordinals and limits, every valid
  optimization level, byte/count boundaries, and noncanonical option strings.
  Each case checks the exact rejection payload or all retained stage/source
  fields, closed staging afterward, and retained work.
- 80 lifecycle/control checks: cancellation during stepping and extraction
  at all seven states, budget exhaustion at every state, early extraction,
  abort, and successful one-shot completion.
- All seven build identity fields and all six mode tags.

The combined selected run `target/compiler-check/run-id3jtjtx/report.json`
passes five native entries in 223.51 seconds, including the original
source/name admission, all three publication histories, and all eight registry
histories. It is bound to source lock
`42fccf45472e879963132e443a5e9efe2e113071fe92692aa98a9e0fac964a03`.
The bootstrap fixture's 541,230-byte verified artifact has digest
`fe0510ee5a9a6988159d5644f373b5ed0dc70d919f30ce19bf8a3d0aecca34f9`,
10,127,996 work ticks, 10,178,175 charged allocation elements, and peak call
depth 21 under the unchanged execution limits. These are logical VM charges,
not physical memory certification. This is not a complete-suite or
self-compilation/convergence result.

## Canonical source collections

`src/request/sources/sources.glorious` assembles a nonempty sealed source
collection. It preserves the native ordering `(package, logical path, FileKey)`
and stable ordering of equal keys. Every source is admitted in that order;
only after all identity/digest/UTF-8 checks succeed does it reject adjacent
duplicate keys. A duplicate cannot hide a later invalid source. The result
retains every original package/path/key/content field and can be consumed by
the existing bootstrap-stage builder.

The shared `kernel/order` scheduler is a bottom-up stable merge sort of indices.
Each step initializes or transfers one index, advances a merge boundary, or
suspends for a comparison. Equal comparisons take the left index. Source
comparisons examine one package/path byte per step, then compare the fixed-size
digest. Raw payloads are staged using back-pops and a stepped reversal;
admission takes each indexed slot once. The algorithm does not drain from the
front or clone source records to sort them. This is not a claim that the current
VM physically transfers every aggregate without copying.

Count and run arithmetic is bounded before addition/doubling. The sorter and
source collector own affine staging, charge the actual supplied controls, check
cancellation at readiness, and discard staging after failure, abort, premature
finish, or invalid comparison protocol use. Only the source collector's fixed
canonical comparator can produce `AdmittedSources`; a caller-provided ordering
answer to the general index sorter does not certify source admission.

The audited fixture passes `[20, 238, 33, 1, 21]`:

- 20 complete Rust-reference collection outcomes: all six three-source input
  permutations, empty/single inputs, duplicates, stable equal-key failures,
  simultaneous corruptions, Unicode/NUL paths, and exact retained/error fields.
- 238 collector lifecycle checks, including step/extraction cancellation at
  every transition through readiness, all premature finishes, capacity/work
  failures, and abort.
- 33 exact stable index permutations, including sorted/reversed/uniform/mixed
  inputs and a 255-element reversed case under an explicit scheduling-work
  ceiling. Physical scaling and compiler-wide performance remain uncertified.
- One real collector-to-bootstrap handoff, retaining the admitted source data.
- 21 sorter protocol checks, including repeated suspended observations,
  unsolicited/duplicate answers, maximal-count capacity rejection, cancellation,
  work exhaustion, abort, and one-shot finish.

The current six-entry selected run passes in 243.80 seconds:
`target/compiler-check/run-eyaz4gdr/report.json`, source lock
`0482d0b9cb34037dfa4e7fd0755f15e14821df4b94da49b5d11aa38c61e5f5a8`.
It also reruns source/name/bootstrap admission, publication, and all eight
registry histories. The collection fixture's 841,595-byte independently
verified artifact has digest
`20b8ad3ca8533d5e5a95b10da3220bfcf70d4af1fc99de625309588ae79912f5`,
8,803,821 work ticks, 10,637,572 charged allocation elements, and peak call
depth 22. This is selected-test evidence, not the full-suite time gate or
self-host bootstrap evidence.

The first fixture used expected-record vectors containing static views and
hit C0 `G5023` at their empty-vector constructor. Expected records now own their
bytes. This does not claim a fix for reference-bearing vector construction.
The initial production compile also required explicit usize assignments and
shared reborrowing, with no Stage0 or standard-library change.

## Whole-request successful-input integration

Whole-request integration is implemented in
`src/request/world`. Its affine builder assembles the component validators into
one owned request workflow, preserving the now-reference-tested failure order:
sources, root/source aliases, capabilities, runtime input, then bootstrap-stage
validation. Both ordinary option maps need their canonical indexes, with the
bootstrap optimization option read from the actual admitted codegen map.
Its encoder retains the complete owned data while computing the exact
[world-v2 fingerprint](world-fingerprints.md), including present runtime manifests
and every compilation mode. Each scalar/header step is bounded and text payload
steps append at most 32 bytes, including chunks that split a UTF-8 code point.
The final BLAKE3 leaf still runs synchronously after charging its complete bounded
input; transport polling and physical allocation certification remain open.
Only successful extraction constructs the private `NormalizedWorld` fields.
The import adapter reads the commitment from that sealed value, not a supplied
digest. Reference tests check the full commitment, retained fields, and the
source/package/diagnostic adapters. The four audited groups now pass together
in 364.56 seconds, with 56 successful-input comparisons:

| Group | Cases | Work ticks | Charged allocation elements |
| --- | ---: | ---: | ---: |
| Build identity and modes | 12 | 5,360,198 | 6,912,326 |
| Sources, options, capabilities | 19 | 8,951,864 | 11,462,269 |
| Complete runtime input | 14 | 12,250,004 | 16,108,479 |
| Bootstrap provenance | 11 | 6,313,503 | 8,502,171 |

Evidence: `target/compiler-check/run-x6jhvlvc/report.json`, source lock
`9ca86f3da5808d483e9f9200512d0b8009a548da80342d94afb4b8e162b98e46`.
Every group independently decodes/verifies its actual Stage0 artifact before
execution. Each profile covers its complete group once; peak call depth is 26.
The runtime group is near the unchanged 16,777,216 charged-element ceiling.
These are logical VM charges, not physical allocation/copy certification.

Cases vary all six modes, each build generation, producer identity, root and
target, source package/path/contents/count/order, both option maps and capability
sets. Runtime cases cover absent versus present-empty input, every selector/host
field, empty collections, permutations, and derived role order distinct from
numeric tag order. Text cases cross a 32-byte chunk boundary inside a Unicode
scalar and retain NUL bytes. Bootstrap cases include seed/non-seed stages,
predecessor commitments, optimization levels, actual option omission, and
extreme count/byte-limit encodings. Successful results compare all normalized
request fields, not only the commitment; file-key lookups and the source,
package, and diagnostic-length adapters are exercised too. The A23 authoring
correction was required for lifetime-generic trait adapter calls through maps.

## Whole-request failures, lifecycle, and registry integration

All 47 source-suite entries now pass in one audited run, in 65.94 seconds:
`target/compiler-check/run-jgx73yx0/report.json`, source lock SHA-256
`e1bda6b077fdb53d810c5b0519ac3193c51fa1f29d94f93f4f2918e387067bee`.
The 56 successful-input cases above retain their expected results. Additional
histories exercise the complete builder and actual sealed-world import:

| Fixture | Result | Work ticks | Charged allocation elements |
| --- | --- | ---: | ---: |
| `request/world_failures.glorious` | 27 exact failure comparisons | 4,021,218 | 4,629,697 |
| `request/world_lifecycle.glorious` | `[1, 14, 3, 3, 5, 4]` | 7,115,184 | 10,476,352 |
| `request/world_registry.glorious` | `[1, 1, 1, 1, 1]` | 8,369,496 | 11,334,159 |

Failure cases compare exact reference error fields and cross-component
precedence, including combinations of malformed inputs. The lifecycle fixture
checks seven cancellation checkpoints before step and finish, abort/closed
behavior, premature extraction, exact work-budget boundaries, and exact
fingerprint-buffer boundaries. These checkpoints are not an exhaustive
cancellation-at-every-transition or physical-cost certificate.

The registry history normalizes four complete requests with multiple sources,
option maps, capabilities, and runtime manifests. Permuted equivalent requests
deduplicate. Foreign/unknown parents are rejected before equivalence reuse,
and a retired parent is rejected even if an equivalent active child exists.
Unrelated option/target/capability changes create a new revision but reuse the
same source/line products. An observed-source edit rejects parent reuse and
recomputes both products. The source program checks exact bytes, file identity,
line starts and product fingerprints, memoized/reused/recomputed explanations,
session and memo/edge/product counts, pinned old results, wrong-owner rejection,
and last-owner reclamation down to an empty database.

The native harness derives world identities and parent/retirement behavior from
the real Stage0 `CompilerDatabase`, and line-index expectations from `LineIndex`.
The source registry's line-product digest is an explicitly separate internal
projection, not a claimed Stage0 wire commitment. Its source-owned query-store
counts and provenance are checked against the production engine contract.
The full native workspace also passes 2,449 tests after the required A24
nested-completion lowering correction.

## Next boundary

Complete world commitments and real normalized-world import are now exercised;
caller-supplied component digests are not being substituted for that boundary.
Physical allocation/copy and transport-polling certification, provider-derived
public dependency facts, request outcomes, the remaining query families, and
the full compiler remain in scope.
