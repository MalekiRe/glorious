# Authoring decisions

The historical behavior reference is `cfeab4b58d60754a70c819fdda25a1f1024907af`.
Authoring starts at `8cf378a1f19617e3aeddb18cada22540730323cc`; local source and
authoring deltas are separately recorded in `sources.lock`. No replacement
parity is inferred from an authoring capability test.

The implementation direction was clarified on September 4, 2026: Stage0 and
the standard library may be corrected as needed; known bugs need not be kept
for frozen compatibility. Baseline pins preserve provenance, not bugs. Keep
changes focused, regression-tested, and explicit about affected behavior.

## A01: shared aggregate snapshots across caller frames

`runtime/bytes.glorious` was accepted, encoded, and independently verified by
C0, but failed during execution with `InvalidRegister { register: 2 }`. A
borrowed `Slice` contained a shared reference into a retained caller frame;
`freeze_frame_value` tried to resolve that nested reference with an empty
caller stack. The authoring VM now freezes each reference using its owning
frame's registers and ancestor stack. Unique references still cannot become
snapshots. This corrects execution of accepted source; it does not change the
artifact schema. The complete byte-buffer roundtrip is an
executable regression.

## A02: canonical byte substrate

The canonical library binds the existing `bytes-from-array-move`,
`bytes-to-array`, and `blake3` roles by exact declaration identity. Public
hashing takes a `Slice<u8>` and returns `Vec<u8>`; the old scalar `Bytes` ABI is
private. There are no new native opcodes or compiler semantics. Bounded
`ByteBuf` and position-only `ByteCursor` implement encoding and range policy
in source. Their failure tests check unchanged bytes/cursor positions.
This is the historical initial bridge. A31 below replaces hashing with ordinary
source bytecode while retaining legacy artifact meanings and declarations.

## A03: measured state-loop execution

The accepted standard-library `loop_state` exceeded a 64-frame limit for a
10,000-step owned-record loop. `VerifiedVmProgram::run_i64_for_authoring` now
permits conservative frame recycling for direct self calls whose suffix is
exactly `Return(call_result)`. Recycling requires no active handler/resumption
and no reference, label, or resumption anywhere in the argument graph. The
argument scan is iterative and budgeted. There are no new bytecode opcodes.
The ordinary execution entry points remain unchanged during this initial
capability rollout. The probe executes 1,000 and 10,000 steps and checks equal
peak call depth and bounded growth in work/allocation charges.

This does not certify constant-time aggregate transfer or a packed runtime:
the existing call transfer still rebuilds aggregate representations, and the
profile reports charged VM elements, not every physical allocation. Borrowed
tail calls and G1 execution still need separate certification.

## A04: lexical shadowing in contextual calls

The contextual direct-call path looked up a global declaration before a
same-named local. A non-callable local could therefore hit an `unreachable!`
instead of reporting `G4105`. Local paths now use ordinary call elaboration;
a minimized Core regression checks the diagnostic.

## A05: trait-backed explicit conversions

Per the source-language direction, `as<Target>(value)` is an ordinary library
function backed by `As<Target>`, not cast-expression syntax. An expected result
can infer the target in `as(value)`. Direct function applications now infer
omitted trailing type parameters, and qualified generic functions follow the
same path. Invalid explicit arguments produce diagnostics, not an internal
panic. Existing width-specific numeric roles complete the source conversion
matrix; no new bytecode operations are introduced. Float-to-integer saturation
is source policy and the existing checked APIs remain unchanged. The VM's
integer-to-f32 path now rounds directly instead of double-rounding via f64.
Float prefix lowering uses the existing negation operation for both widths;
subtracting from positive zero was losing negative zero, and f32 prefixes
previously had no MIR instruction. Matrix fixtures use bounded-size helper
bodies: C0's large recursive MIR lowering stack remains a separate limitation.
See the [standard-library conversion contract](../../glorious-standard-library-specification.md#113-conversions)
and the independently verified `conversions` tests.

## A06: borrowed self-tail calls in the authoring runtime

The opt-in authoring runner now also preserves loans into surviving caller
frames and immutable shared captures. Recycling does not push a frame, so
caller-relative references retain their existing coordinates. References into
the recycled frame still prevent the optimization. Captured values are checked
iteratively for hidden frame-relative references, labels, and resumptions;
captured unique references remain rejected. The entire caller-owned value is
also inspected: a surviving owner may itself contain a frame-branded label.
Nested frame-relative loans inside that owner conservatively prevent recycling
instead of following an unproven, potentially cyclic reference graph. Active
dynamic continuations still disable recycling. These scans expose their cost;
they do not establish constant-time eligibility checks for large owners.

C0 emits a result copy at some block boundaries, so a tail call need not be
immediately followed by `Return`. A budgeted straight-line check now accepts
only copy/move forwarding of that result into the return. It cannot skip stores,
jumps, calls, destruction, or other intervening work. Both eligibility scans
charge the execution budget, including unsuccessful scans.

Source regressions exercise 1,000/10,000 mutations through a surviving unique
loan with a shared increment, and returning a unique loan through 10,000 calls
before writing through it. The mutation loop retains peak call depth four and
bounded linear work/allocation charges. A separate local-loan history requires
retaining its owning frames instead of recycling them. Instruction, allocation,
and call-depth limits remain enforced. Ordinary runners retain their prior
behavior; this authoring capability adds no opcode or artifact schema.

This is not G1 certification or a general physical-storage claim. Aggregate
snapshots and array mutation can still rebuild backing objects. Those costs
remain explicit M1 work; A07 replaces the former linear map lookup.

## A07: source-owned hash indexing

The canonical map previously called `Hash` but discarded its result and scanned
every dense entry. It now uses power-of-two open addressing, cached hashes,
and a maximum occupied-plus-deleted load of 7/8. Empty and deleted buckets are
distinct; lookup continues past tombstones, while insertion reuses one only
after checking for an existing resident. Crowded tables grow geometrically or
rebuild at the same size to clear excessive tombstones. Capacity doubling uses
the existing checked `usize` addition; it cannot silently wrap to zero.

Dense keys and values are separate from index metadata. Rehashing never copies
or moves a resident, and swap-removal updates the relocated entry's reverse
bucket link. `HashSet` shares this implementation. Duplicate map insertion now
preserves the resident key, as required by the library design, instead of
replacing it with the incoming equal key. This is a deliberate correction to
the old dense implementation. Set insertion already preserved its resident.
`get_mut` returns an owner-tied unique value loan; `remove_entry` transfers both
fields without requiring either to support erasure. Existing insert/remove
erasure bounds and the ownership-returning set removal remain unchanged.

The `standard_library` regressions cover affine keys/values, growth, complete
collisions, wraparound probes, replacement behind a tombstone, deletion with
relocation, repeated cleanup/reinsertion, and resident-key preservation. The
lookup-work comparison subtracts identical construction from fixed-size read
batches at two table sizes. It measures logical VM work, not physical copying:
shared call snapshots and array backing mutation still need separate cost
accounting and runtime work. No map intrinsic, VM value, or opcode was added.

## A08: test-only physical allocation metering

The `runtime_storage` integration target wraps Rust's System allocator with
non-allocating thread-local counters. Only synchronous verified VM execution
is metered: source compilation, verification, and reporting are outside the
scope. Successful allocation and reallocation requests are counted separately;
cumulative requested bytes are not peak/live bytes or logical VM elements.
The production allocator and compiler/runtime semantics are unchanged.

The logical lookup-work test and physical meter share one source fixture.
Measurements show that constant indexed lookup ticks coexist with increasing
allocation requests. See `runtime-costs.md` for the measured inputs, counts,
and remaining runtime sites. This establishes a baseline for fixing copying,
not a requirement that future implementations retain the current costs.

## A09: retained-owner call transfer and effect-frame translation

Ordinary calls now rebase both shared and unique incoming references to their
surviving caller owner. Already-frozen shared captures retain the same backing
and projection instead of being recursively frozen again. Shared returns from
callee-local storage still become snapshots; unique local returns and unique
callable captures remain rejected. The verifier, opcodes, and artifact schema
are unchanged. This applies to ordinary verified program execution as well as
the opt-in authoring runner.

Live shared arguments exposed missing frame translation in cross-call effect
payloads. On `Perform`, values bound by an ancestor clause are translated to
that frame, while the suspended operation retains its original coordinates.
`Forward` translates from that original performer, not from an intermediate
declining clause. Resumption arguments pass through the installing frame and
then into the suspended call chain. This covers ordinary resumes, returning
replays, and explicit snapshot resumes. Frame crossings charge work; the new
clause-payload vectors charge allocation budget.

Regression tests check backing/projection identity, nested call/return
coordinates, local escape rejection, invalid frame depths, work limits,
borrowed cross-call payloads/results, forwarding, two-shot replay, and a
resumption closure. The physical map meter now also asserts size-independent
added lookup allocation requests at its two measured sizes. This is a focused
transfer correction, not certification of every continuation/loan combination
or a claim that array growth and tail eligibility have become cheap.

## A10: explicit owner lifetimes on vector views

Composing `HashMap::get` with `Vec::get` or `Vec::as_slice` inside a function
returning a named owner lifetime was rejected with `G5017`. The map preserves
that lifetime, but the vector accessors' elided signatures did not carry it
into their results. The borrowed vector accessors now declare the owner/result
relationship explicitly, for shared and unique element loans and slices.
Ordinary inferred calls are unchanged; explicit generic applications now take
the lifetime before the element type, as the map accessors already do. No
existing explicit applications of these vector functions were found in the
current source/test closure. This is a library signature correction, not a
general fix for Stage0 lifetime elision and not a relaxation of escape checks.

`nested_map_vector_views_preserve_the_explicit_owner_lifetime` reproduces the
failure for a reference and a slice borrowed through a map-owned vector. Its
extended regression also checks a map-owned unique element loan and a direct
unique vector slice. A negative regression rejects a local vector loan escaping
through a declared named lifetime. The changed library passed all 113 library
tests; the A10/A11 source closure passed all 24 then-current foundation tests
in `target/compiler-check/run-tp6x_5xj/report.json` (source-lock SHA-256
`076ca38e1b0fc61ac02eace6c51805b999fda06f992329196ed4a9d26b94a1c4`).
This is historical closure-specific evidence, not automatic certification of
subsequent source changes.

An additional composition remains uncertified: returning `Option<SliceMut<'a,
T>>` through a map lookup currently loses nested unique provenance at the
subsequent slice-element call (`G5023`). Explicit lifetimes alone do not repair
that separate Core/PlaceFlow case. Do not generalize the accessor tests into
certification of arbitrary nested unique-view returns.
The inspected completion-origin code currently matches a binder's field path
only by equality: an aggregate binder at `[0]` does not inherit a frozen loan
at `[0, 0]`. A future correction must preserve those suffix projections and
their unique reborrow owners, with escape and conflicting-alias regressions;
merely suppressing `G5023` would not establish the missing provenance.

## A11: trait materialization respects executable reachability

C0 type-checks and lowers all source bodies, while instance discovery starts
at executable roots. Rewriting a concrete trait call in an undemanded body
therefore incorrectly required an instance which discovery had intentionally
not created (`G7032`). Adding the ledger triggered the error in old fixtures
that never use it; the ledger-specific fixtures themselves passed.

Materialization now records absent selected-method targets while rewriting
call edges, then rejects them if their owners are reachable from the rewritten
executable roots. It shares the linker's ordered `Call`/`MakeCallable` traversal,
including lifted closures. Unused bodies remain fully source-checked; their
executable instances are not eagerly demanded. Reachable missing instances
still fail closed, before VM emission. No verifier or bytecode contract changes.

Regressions exercise unused and demanded direct callers, callable values, and
lifted closures. A deliberately incomplete instance graph separately checks
that both direct-call and callable-construction reachability retain the hard
error for a missing method target.

## A12: source decimal formatting for diagnostic counts

The diagnostic suppression contract includes exact unsigned counts. The
canonical library previously implemented `Display` only for `String`; it now
also formats `usize` in source using quotient/remainder digits, without a new
machine binding. On the current 64-bit ABI, the recursion is bounded by twenty
digits. The focused test independently decodes/verifies and executes fourteen
boundary values, including zero, decimal transitions, and unsigned values above
`i64::MAX` through `usize::MAX`. The full standard-library suite passes all 114
tests (452.99 seconds). Expanded compiler source-closure verification remains
required after the request-publication integration.

The test groups its assertions into short functions. A single fourteen-term
addition tree exceeded C0's debug lowering thread stack; grouping avoids that
known authoring-depth limitation without removing any boundary value.

## A13: explicit owner lifetimes on string views

The concrete source blob's `&'a Blob -> Str<'a> -> Slice<'a, u8>` accessors
exposed the same signature-elision limitation as A10. `String::as_str` and
`Str::as_bytes` now explicitly preserve the owner lifetime. The focused
`named_string_views` tests both pass: a nested immutable owner returns its
bytes correctly, and a local string cannot escape through a named output
lifetime (`G5017`). No escape/type checker was relaxed.

The first full library run exposed two existing implicit `&String -> Str`
tests rejected by the old coercion adapter, which required a nongeneric
`string_as_str` signature. That small Core adapter now instantiates the
accessor's lifetime binder through the ordinary call path, retaining its
actual owner provenance. All eighteen string-related tests pass, including
both existing implicit calls and a new negative implicit-view escape test.
The final native library/Core/service/backend run passes 1,276 tests.
The full standard-library rerun passes all 118 tests (193.03 seconds).

## A14: retain the verified element type when borrowing empty arrays

The empty-file source test exposed a runtime `Array(U8)` versus `Array(Unit)`
reference mismatch. `borrow_value` inferred projected referent types from the
first resident, but empty arrays have no resident. A reduced library test
reproduces the failure using an empty byte vector extracted from a nested
vector, validated as a string, and hashed through borrowed views.

Both VM execution paths now carry the verified Borrow destination's element
layout for empty arrays (including structurally nested arrays/tuples).
Nonempty residents still determine their actual type. The strict type matcher,
artifact verifier, unique-loan rules, and wire format are unchanged. A native
regression checks shared/unique projected empty arrays, nested empties,
rejection of nonempty Unit arrays as bytes, and rejection of shared-to-unique
upgrades. The reduced source regression and all 1,041 native library/service/
backend tests pass. Full standard-library and expanded source-closure runs
must separately cover this change; earlier closure hashes do not.

## A15: static literals in generic view contexts

The expanded source suite exposed `G5017`/`G5018` for existing literal calls
such as `Str::as_bytes("stable")` after A13 made that accessor's lifetime
explicit. Literal elaboration recognized `std::Str`/byte `std::Slice` only
when their expected lifetime was static or elided. It now recognizes these
exact standard nominal types with a generic lifetime too, while constructing
the same sealed **static** literal wrapper. Ordinary lifetime checking still
relates that real static value to the expected view; no requested lifetime is
forged onto the literal or a local string.

The subsequent `G4187` exposed an inconsistent reference-shape classification:
a frozen `Paths` call contract was labeled `External` when its particular
argument/result instantiated to static. The classifier now preserves
`CallerPaths` for that contract before the static-only case. Static inputs
carry no local loan. The strict origin/shape validator and escape checks are
unchanged.

Two reduced regressions pass: generic text/byte-literal calls (including empty
and Unicode views), and rejection of a local string escaping through the same
generic view (`G5017`). All three dependency-ledger source histories pass with
the real registry in the production closure. The full standard-library run
passes 120 tests (201.86 seconds). This is an authoring correction, not a G1
format change or self-compilation certificate.

## A16: disjoint runtime-authority fingerprint tags

Tracing complete request normalization exposed a collision in the Rust
reference: `IntCheckedDiv` had been appended to the legacy tag list at 69,
already occupied by `f32-add`. Two otherwise identical requests with those
different grants normalized to the same fingerprint
(`30c210c33b1c14b2ed3449d21f0c2955bed255a127bcbcf5b061a58d97ab2a42`).
The real database consequently returned the same revision ID for both.
Both new request/revision regressions fail before the correction.

Reviewed correction: checked integer division uses the previously unused tag
182; every other existing role tag is unchanged. The canonical cache
generation advances from 2 to 3, so current Stage0 build identities cannot
silently reuse identities produced under the ambiguous tag contract.
This changes runtime-authority fingerprints, not numeric conversion behavior,
declaration binding, any VM opcode, the G0/G1 schemas, or verifier rules.

The new tests pass for world fingerprints, actual revision admission,
bound-manifest fingerprints, bootstrap source-semantics commitments, and
cache-generation separation. A complete explicit inventory checks all 105
non-float and 78 finite float roles: their 183 tags are unique and occupy
0 through 182. The library/Core/service/backend/request/runtime-manifest
run passes 1,322 tests (66 + 235 + 826 + 153 + 17 + 25).
The source lock now also covers the request, runtime-manifest, and bootstrap
authoring files and their request/runtime-manifest regression targets.

This inventory proves disjoint tags for the finite canonical leaves. It does
not certify every malformed `FloatPrimitive::Convert` construction or selector
alias; the runtime-manifest port must separately audit those admission paths.
In particular, source inspection identifies `f32-to-f32`/`f64-to-f64` selector
parsing as needing a regression: parsing admits a same-width conversion while
the fingerprint ordinal expects an integer source in that arm. This is not
covered by the finite-leaf inventory and was not corrected by A16. A22 below
subsequently closes this malformed-role admission issue.

## A17: byte-indexed owned Unicode scalar access

`Str::char_at(view, byte_index)` is an ordinary standard-library function over
the existing private UTF-8 character-read operation. It rejects end/out-of-range
indices as `OutOfBounds` and interior UTF-8 continuation bytes as
`NotCharBoundary`, returning an owned `char` on success. It adds no intrinsic,
host callback, or format change.

The focused 16-check test passes for static and dynamic strings, ASCII,
multi-byte characters, NUL, every interior emoji byte, empty strings, a maximal
index, and a scalar returned after its local string owner is gone. The first
fixture attempt mixed an inferred i64 local with usize counters; a typed
helper fixes the fixture, not the type checker.

This operation lets stepped consumers inspect a scalar without forwarding a
borrowed substring through an iterator-construction call. The latter exposed
the existing C0 `G5023` provenance limitation; no escape check was weakened or
claimed fixed. The source name validator uses the new accessor. Its byte
mapping helper is tail-positioned to avoid the known non-tail completion
`G6005` authoring limitation.
The complete standard-library run passes 121 tests in 192.12 seconds.
The audited current-closure source-admission and eight-scenario registry
batch also pass together in 154.42 seconds (`run-mj3qf1aw`, source lock
`dd6607c386e89b4c0c28eaf9f1cc4a811a4c8301cd50184f2cc8ce39294b87bb`).

## A18: framed world and bootstrap input commitments

Two new request regressions reproduce a second class of Stage0 identity bugs:
a semantic option pair aliases the same pair in codegen options, and capability
strings can impersonate an optional runtime-manifest section. Each individual
value was length-prefixed, but adjacent lists had no counts. The corrected
requests also import as distinct real database revisions.

The bootstrap audit reproduces a codegen-option/capability collision and shows
that source-semantic commitments ignored every host-import field and the four
semantic build generations. Those regressions fail before the correction.
Producer identity remains deliberately excluded from the convergence projection;
adjacent compiler stages must be able to converge under the same input contract.

Reviewed correction: world and both bootstrap projection domains advance to
v2. All variable-length collections have explicit u64 counts and optional
sections have one-byte presence discriminators; these are themselves ordinary
length-prefixed fields. Request/bootstrap hashing shares the complete runtime
input encoding, including both counted primitive selectors and counted host
imports. The bootstrap source projection also binds language, query, interface,
and cache generations. See [the exact encoding](world-fingerprints.md).

Canonical cache generation advances from 3 to 4. Bootstrap-manifest schema
advances from 2 to 3 to reject old evidence carrying the ambiguous commitments;
its field layout is unchanged. Neither VM format, any opcode, FileKey identity,
numeric conversions, nor the independently verified artifact bytes change.
Bound runtime-manifest digest encoding is not changed by A18. The malformed
float-selector admission issue recorded under A16 was still open at this point;
the subsequent A22 correction is recorded below.

Tests cover the two request collisions and real revision separation, bootstrap
codegen framing, each host-import field and removal, all four semantic
generations, producer-independent source commitments, cache-generation
separation, old manifest rejection, and an independently written full world-v2
transcript with reordered inputs, float/integer roles, host imports, Unicode,
NUL, both option maps, and non-seed bootstrap provenance.
The complete selected native library/Core/service/backend/request/runtime
regression run passes 1,330 tests (70 + 235 + 826 + 153 + 21 + 25).
The conversion target also passes all eight tests (12.98 seconds), and the
complete standard-library target passes all 121 tests (205.00 seconds).
The current source closure passes the five selected admission/publication/
registry entries in 223.51 seconds (`run-id3jtjtx`, source lock
`42fccf45472e879963132e443a5e9efe2e113071fe92692aa98a9e0fac964a03`).
This includes the new source bootstrap-stage validator, not self-compilation.

## A19: ordinary owned-string comparison and hashing

The canonical library now implements `Eq`, `Ord`, and `Hash` for owned `String`.
Ordering and equality compare exact UTF-8 bytes; hashing feeds the byte length
and then every byte into the existing source `Hasher`. This adds no intrinsic,
opcode, normalization, case folding, or string operator syntax. Request alias
indexes can now use ordinary `HashMap<String, usize>` with equality checks after
hashing instead of introducing compiler-specific string-key operations.

The regression independently checks 13 byte-pair/hash cases (including empty,
prefix, NUL, Unicode, composed/decomposed, and wrapping-length examples) and six
real map checks. `Ab` and `BA` deliberately collide under the existing Hasher;
both remain separately retrievable and replacement preserves the entry count.
The focused test passes, and the complete standard-library/conversion targets
pass 122 + 8 tests in 195.47 and 12.87 seconds respectively.

The initial implementation nested `string_as_str` directly inside `str_as_bytes`
and received G4107/G5017 lifetime diagnostics. Named borrowed views compile and
execute with the existing lifetime checks; no Stage0 relaxation was made.
Standard-library source bytes already participate in world identity, so this
ordinary trait extension does not require a cache or format generation change.

## A20: hidden reference leaves in caller-owned parameters

The namespace fixture's capability comparator failed with G5023 when it took
a `Slice<Capability>` element and then a `Str` view. Naming both intermediate
references did not fix it. A minimized native Core case reproduced the same
failure without the compiler modules: a nested nominal parameter was passed
to a projection wrapper, but the calling body never spelled the reference
field itself. PlaceFlow seeded incoming reference identities by scanning only
explicit reference-typed parameter projections in that body, so the hidden
field had no registered origin.

PlaceFlow now also traverses each parameter's frozen interface layout with
the same reference-leaf traversal used to establish call contracts. It seeds
only successfully proved leaf paths, preserving their shared/unique kind.
Opaque or ambiguous layouts do not create guessed origins. Explicit projection
seeding remains available, and no-interface analysis still rejects an opaque
nominal caller-path claim. Lifted callable analysis uses its own supplied ABI.
The source audit now locks `placeflow.rs` with the other authoring overrides.

The minimized Core regression fails before the correction and passes after it;
it checks nested private fields, lifted analysis, no-interface rejection, and
rejection of a unique-reference carrier reused after transfer. A separately
compiled/decoded/verified standard-library regression executes the original
slice/string-view pattern and returns both expected rows (10.62 seconds).
This changes reference-provenance analysis, not runtime leaves, bytecode
formats, conversion policy, or the escape/verifier rules. The selected native
regression run passes all 1,462 tests: library 70, conversions 8, Core 236,
request/revision 21, runtime manifests 25, service 826, standard library 123,
and VM backend 153. The namespace fixture also executes successfully with
tuple `[22, 116, 8, 7, 11]`; see [source-admission.md](source-admission.md).

## A21: explicit Slice element-owner lifetimes

`Slice::get` and `Slice::get_unchecked` previously accepted `Slice<'_, T>`
and returned elided element references. A wrapper accepting `Slice<'a, T>`
could not return the promised `Option<&'a T>` or `&'a T`: the minimized
standard-library regression failed with G4110/G5017/G7007 before the fix.
Both ordinary accessors now explicitly tie their result to the slice's `'a`,
matching the existing vector-owner contract. The regression compiles,
independently decodes/verifies, and executes both paths (11.53 seconds).

Four production call sites now name the borrowed custom view before passing
it to a slice accessor: publication's diagnostic batch lookup and source
line-byte, boundary, and column-step helpers. Their original branches and
number of view calls are retained. No lifetime rule, verifier restriction,
runtime leaf, or bytecode format was relaxed. The complete standard-library
and conversion targets pass 126 + 8 tests (217.12 and 13.89 seconds).
The option-map fixture subsequently passes `[14, 108, 10]` in a non-audited
201.30-second smoke run. That snapshot includes runtime-role metadata but
predates the manifest-input builder; broader current-source audit evidence
must be recorded separately.

The subsequent six-entry source run (`run-s78vbb8_`, 293.94 seconds) passes
source, name, bootstrap, collection, and publication fixtures, but fails the
registry fixture's two nested custom slice-view expressions with G4107/G5017.
Those two fixture observations now name their `line_starts`/`bytes` views,
preserving both checked values and the same branches. The failed run is not
a passing combined certificate. The registry rerun in `run-rmq5h6c2` passes
all eight histories after those changes; that two-entry run still fails overall
because the new manifest fixture has an unrelated unsupported MIR form
(200.64 seconds). It is not a complete-suite certificate.
The subsequent four-entry audited run passes registry, namespace, options,
and manifest input together in 238.76 seconds (`run-_ikml_nz`); see
[the source-admission evidence](source-admission.md).
The complete selected nine-entry admission/publication/registry group then
passes in 381.31 seconds (`run-wf_8rujk`) with the same source lock. This closes
the pending affected-group rerun after A21, not the full source-suite time gate.

## A22: reject malformed floating runtime authority before hashing

Runtime manifest inputs can contain directly constructed `FloatPrimitive`
values, not just parsed selector strings. The old canonicalizer accepted
malformed conversions, and a request with an f32-to-itself role panicked in
the private tag ordinal during normalization. Minimized unit and request
tests reproduce the acceptance/panic before the correction.

Canonicalization now validates every sorted role before duplicate rejection;
direct binding validates each role before declaration/signature lookup.
`ManifestError::InvalidRole` retains the exact offending role. Float conversion
selector parsing uses the same validity predicate: unchecked integer-to-float
and distinct-width float-to-float, or checked float-to-integer. Other conversion
shapes are rejected. Historical checked-suffix aliases for the 24 ordinary
float arithmetic/comparison operations retain their existing canonical roles.

The exhaustive native conversion-shape regression checks all 18 x 18 x 2
scalar/checked combinations: 50 admitted conversions and 598 exact invalid-role
errors. Invalid direct binding is also rejected. The request regression now
returns `InvalidRuntimeManifest` rather than panicking. The selected native
regression run passes 1,335 tests: library 73, Core 236, request/revision 22,
runtime manifests 25, service 826, and VM backend 153. Together with A21's
separate library/conversion runs, these are focused current regression evidence,
not a complete source-suite or release certificate.

All 183 valid runtime roles, tags, numeric conversions, and encodings are
unchanged; malformed requests never had a valid commitment. No cache, VM,
bootstrap, or verifier generation is changed by A22. The new source metadata
represents this existing finite protocol, not new compiler intrinsics. The
shared `runtime-authority.tsv` witnesses are checked against the complete
native role/tag inventory and independently consumed by the source fixture.
That source fixture now passes `[69, 183, 648, 1, 20]` in the audited four-entry
run recorded under A21. This validates source input canonicalization and role
metadata, not declaration-bound authority or a complete normalized world.

## A23: open trait-method lifetime applications at their call boundary

Whole-request normalization exposed an unstaged call target in C0's executable
MIR. A reduced source program reproduces it with a lifetime-generic `Lookup`
method over an owned map, calling a lifetime-generic lookup helper. The selected
method's application retained `Lifetime::Generic(0)` even though the invocation's
parameter/result contract had already opened that lifetime to its actual caller
region. Instance discovery therefore skipped the method specialization, and
linking reached unspecialized map templates instead.

The existing `Core::call` lifetime substitution now updates trait-method method
arguments as well as ordinary function arguments. Solver-selected trait relation
arguments are not rewritten. The reference-origin contract is still frozen
before opening; no lifetime compatibility, ownership, or verifier rule is relaxed.
There is no new primitive or VM format. Temporary MIR/key-location diagnostics
used to trace this failure have been removed.

The reduced executable regression passes after the change (11.01 seconds),
including serialized artifact decode/verification and the expected map result.
The companion local-owner escape regression also passes, requiring the existing
`G5017` rejection. The broader runs pass 236 Core, eight conversion, and 128
standard-library tests (247.07 seconds for the library target), plus 73 native
library, 826 service, and 153 backend tests. These are 1,424 tests across separate
runs, not a complete workspace run. All four whole-request source reference
groups subsequently pass in 364.56 seconds (`run-x6jhvlvc`, 56 cases), including
the previously failing normalized-world map adapters. Cross-component failure,
resource, and registry histories remain open; this is not a normalization or
release gate.

## A24: nested normal-completion values

The normalized-world registry fixture exposed `G6005` for a valid nested
completion, reduced to `2 * handle true { true => 21, false => 0 }` inside
another completion arm. The tail-only specialization emitted the outer matrix
but sent the nested operand to the straight-line value emitter. The old
non-tail continuation path also evaluated selected arms/subjects as if they
could not contain further completions.

The direct-return specialization now declines unsupported value-CFG shapes
before emitting any prefix. A shared recursive value-segment builder handles
subjects, arms, and residual expressions, carrying each selected result through
a typed block parameter. Strict prefixes are retained in the evaluated-value
map; arm-local bindings do not leak across the join. Terminal arms have no
normal continuation edge. The change removes the duplicated special-case
nested-subject emitter. No verifier, lifetime, quantity, or VM format rule is
weakened.

Eight reduced executable cases cover nested operands, initializers and
subjects, strict side-effect order, shadowing, an affine result, and a
single-owner mutable-reference result. Artifacts are serialized and
independently decoded/verified before execution. A two-owner reference-return
stress case was initially assumed valid, but inspection established that the
frozen callable/VM contract requires an exact producer path per result leaf.
Both a plain and a nested ambiguous return retain `G5023`; extending that
contract is separate work, not a prerequisite for this correction.

Commit `559fecaa` contains the isolated MIR correction and regressions. The
complete source suite passes all 47 entries in 65.94 seconds
(`run-jgx73yx0`), including the previously failing normalized-world registry
history. The full Rust workspace passes 2,449 tests with zero failures and two
existing ignored manual VM benchmarks in 78.340 seconds, including a
4.17-second incremental build. These timings are not clean-checkout CI timings.
All command, memory, and VM execution guards are unchanged.

## A25: copy-on-write authoring-runtime updates

Mutable reference stores previously rebuilt every aggregate along their owner
path. Fixed-size array set, move-out, and reverse additionally copied the
complete element vector. The runtime now resolves the same checked register
or caller owner, charges the same logical fields, and uses copy-on-write
projection. Unique backing is updated directly; shared tuples/records/enums/
arrays detach before mutation, preserving captured snapshots and other owners.
No bytecode instruction, runtime role, verifier rule, layout, or ceiling changes.

Four native tests cover retained-pointer reuse, shared detachment, budget/path
failure, caller write-back, move holes/reversal, and shared/captured authority.
A new real source fixture performs ordinary vector element writes at 8, 64,
and 512 elements. The previous runtime fails its physical size-independence
assertion; the new runtime passes with identical artifact digests and logical
counters in all six before/after cases. Sixteen 512-element writes request
185,930 additional bytes instead of 2,288,714. The selected native run passes
1,194 tests. See [runtime costs](runtime-costs.md) for the measured scope and
the remaining resizing, transfer, tail-scan, and physical-certification work.
The complete workspace passes 2,455 tests with zero failures and two existing
ignored manual VM benchmarks in 84.670 seconds; all 48 source entries pass
within that run. The source-lock audit is unchanged before/after execution.

## A26: owned patterns, resident destruction and delimited completion

September 6, 2026. Source Vec now destroys application-defined residents through
ordinary specialized source hooks, then frees its raw allocation. Pattern
extraction preserves residual ownership, and selected-variant destructor loans
do not retain unrelated error payloads. Terminal completion returns clean up
their enclosing lexical owners. Explicit unique-reference reborrows remain
required after a call that would otherwise consume the handle.

The authoring runner recognizes vacant structural cleanup CFGs after self-tail
calls with a bounded, allocation-charged proof. Active hooks and all other
source work prevent recycling; ordinary execution is unchanged. An explicit
resumption-completion delimiter separates the resumed computation from its
enclosing suffix, and restored frames synchronize surviving source allocations
without conflating fresh shadowed storage. Stage0 schema/cache/bytecode/verifier
generations are now 100/15/55/14, not an independent G1 format change.

Frozen validation passes 2,577 workspace/all-targets tests with the 48 source
entries excluded, then all 48 entries in the separately audited complete suite:
2,625 passed, zero failed, two existing ignored benchmarks. Source execution
takes 172.79 seconds. `target/compiler-check/run-4hvcrnb9/report.json` contains
50 execution records, a matching source-lock digest, complete-suite pass status
and `release_ready: false`. All original source assertions, complete batches,
590-second command guards and VM budgets remain in force.

See [resident-cleanup evidence and remaining gaps](unsafe-memory-progress.md#source-owned-resident-destruction-and-handler-cleanup).
These are authoring prerequisites, not certification of the source semantic
compiler, service or C2/C3 bootstrap.

## A27: native bridge source contracts and unsafe-result reborrowing

Stage0 schema 101 retains callable and nominal-field source contract digests
through region erasure for capability-bound native linking. Explicitly unsafe
host bindings now support scalar/native-reference calls and synchronous
bytecode callbacks, including source-specialized Vec growth and resident Drop
while native code is active. The fixtures use genuine source-allocated homes,
not copied aggregate payloads or native collection implementations.

An unsafe-created unique reference forwarded through a safe borrowing function
previously lost its parent-loan provenance and failed a legal child reborrow.
Frozen unsafe/external results now introduce explicit reference-leaf origins
that survive forwarding, blocks and reborrowing. Existing overlap, parent-write
and shared-to-unique rejection remain covered; raw pointer bits alone introduce
no checked authority. Cache/bytecode/verifier generations are 16/56/15.

General frame homes, owned/callable ABI, outward callback effects and complete
cleanup remain open. See the [native bridge checkpoint](unsafe-memory-progress.md#native-calls-and-bytecode-callback-checkpoint)
for the exact execution and safety scope. This does not implement compiler
semantics in a host callback or certify G1/self-hosting.

Frozen validation passes 2,592 workspace/all-targets tests and all 48 separately
audited source entries: 2,640 passed, zero failed, two existing ignored manual
benchmarks. The 171.55-second source run has no filters and keeps all original
batches, assertions and budgets. Its evidence is
`target/compiler-check/run-9dlur2gc/report.json`, with 50 execution records,
matching source-lock digest and `release_ready: false`.

## A28: native homes for ordinary source storage

Schema 102 and cache/bytecode/verifier 17/57/16 initialize supported addressable
source locals in native homes before any borrow or engine boundary. Source
cleanup and partial-initialization metadata govern those homes; raw/native
address exposure prevents premature reclamation or frame recycling. Source
Vec callback fixtures use ordinary locals and count actual cleanup homes in
their byte budgets. A surviving unique native-home capture works across the
existing dynamic-label rejoin.

An adjacent single-consumer dereference/projection can read one native field
directly instead of allocating an unobserved aggregate value. It retains both
instruction charges and checks all local uses, including deferred control
payloads. This restores the four source batches exposed by native-home costs
to their original allocation budget. No source assertion or limit is relaxed.

See the [native source-storage checkpoint](unsafe-memory-progress.md#native-source-storage-checkpoint)
for the precise supported layouts, runtime limits and remaining ABI/compiler
work. This does not certify complete U4, G1 or self-hosting.

Frozen validation passes **2,646 tests**, zero failures and two existing ignored
manual benchmarks: 2,598 workspace/all-targets tests and all 48 source entries
in 176.98 seconds. `target/compiler-check/run-9d708b6q/report.json` contains
50 execution records, no filters, a complete-suite pass and `release_ready: false`,
bound to source lock SHA-256
`55825cc00ee932738eb43d441e736c60bf5fba3fc674b7b57e09d3231779f466`.
The Rust and source build-identity constructors both retain the new generations;
the source bootstrap comparator still checks all seven build fields.

## A29: synchronous owned native arguments and results

Schema/cache/bytecode/verifier 103/18/58/17 and native ABI 2 retain owned
aggregate arguments in producer-established native storage and initialize
native results in preallocated caller slots. Callback frames bind the native
caller's existing owned parameter slots and retain native return producers
through ordinary calls. Source Vec growth and element Drop execute as bytecode
during an owned round trip; a zero-size owner crosses both directions without
native payload allocation and is destroyed once by source cleanup.

The [owned ABI checkpoint](unsafe-memory-progress.md#synchronous-owned-native-abi-checkpoint)
records the tests and limits. This is synchronous ownership placement, not
durable external ownership, a general callable ABI, selected drop-code identity,
complete exceptional cleanup, physical allocation-free certification or U4
completion. Both build-identity constructors advance; source comparison batches
and execution limits are unchanged.

Frozen validation passes **2,651 tests**, zero failures and two existing ignored
benchmarks: 2,603 workspace/all-targets tests (23 native-bridge regressions) and
all 48 audited source entries in 168.02 seconds. The unfiltered, 50-record report
is `target/compiler-check/run-xyt6cbon/report.json`, source lock SHA-256
`6811bd9278b2ee73c90bb50d336ec47e0639c5f3960035bdaf7404615cdcd7fb`.
It records a complete current-suite pass, not release readiness or self-hosting.

## A30: selected native destruction and normal-return register reuse

Schema/cache/bytecode/verifier 104/19/59/18 and native ABI 3 bind each native
resident's full source-type identity and selected destructor to its emitted
reachable code. Native code can invoke this specialized bytecode operation
without a separately declared source callback argument. Return-only referents
retain operations too, and ABI matching includes the execution allocation-domain
protocol. This is not complete copy/use-operation identity, durable external
ownership or a general callable ABI. See the
[destructor contract checkpoint](unsafe-memory-progress.md#native-destructor-contract-checkpoint).

The new source Drop fixture exposed prefix-binding mutation in a speculative
root short-circuit lowering path. Declining that path now leaves the lexical
scope unchanged; accepted paths also clean up prefix owners on normal return.
Ordinary native-resident call arguments copy into distinct callee homes without
intermediate field boxing. The opt-in authoring runtime reuses empty register
buffers after ordinary returns, with stable function-keyed cache entries local
to one execution. Only Vec backing survives: all values, native homes, source
brands and continuation state are released. New allocations remain charged;
normal source cleanup, call-depth checks and the original execution limits
remain. `reused_call_register_buffers` records the number of actual reuses.

The complete bootstrap batch initially exceeded its 16,777,216-element limit
after restored cleanup. A temporary larger-limit diagnostic measured 17,557,304
elements; that diagnostic is not a passing original-limit certificate. Its
temporary test edit was restored before validation. The register-buffer and
native-argument changes reduce real allocation work, not comparator coverage.
The physical meter's original size-independence and rational-slope assertions
remain unchanged; [current measurements](runtime-costs.md#september-6-native-destructor-and-register-buffer-checkpoint)
record the executed results separately from logical allocation charges.

Frozen validation passes **2,658 tests**, zero failures and two existing ignored
benchmarks: 2,610 workspace/all-targets tests and all 48 audited source entries
in 174.90 seconds. Bootstrap returns `[145, 80, 13]` with 7,699,624 charged
elements and 495,108 reused buffers under its original limits. The unfiltered,
50-record report is `target/compiler-check/run-47qvcf5a/report.json`, bound to
source lock SHA-256
`4da7e82758161ab0586d5c3a7098c6acf7c746a235d48f082567e359bd620575`.
It certifies the current suite, not language parity, release readiness or C2/C3.

## A31: source-owned BLAKE3

The public `blake3(Slice<u8>) -> Vec<u8>` API now runs unkeyed BLAKE3-256 as
ordinary source bytecode. Compression uses existing scalar leaves; block
loading and digest writing use existing byte-memory operations. Chunk flags,
64-bit counters, message permutation and tree reduction are library policy,
not a new runtime primitive. No input Array/Bytes conversion remains. Legacy
declarations and opcodes retain their explicit artifact compatibility meanings,
but no current source library function calls them. No artifact generation,
runtime authority, budget or accounting rule changes in this checkpoint.

The original complete-digest fixture remains. New regressions cover 35 lengths
through 65,537 bytes in one shared-budget execution, exact emitted-opcode
inspection, six high/low counter cases against non-root reference chaining
values, and a mutated owned input whose first hash releases its loan. The
large batch passes within 64 call frames and a 4,096-byte native-storage budget
with no native allocation over 64 bytes. This limit excludes separately
accounted private VM registers/metadata, not a physical allocator census.

The first high-counter test's nested Boolean-handler comparison encountered an
existing C0 lowering restriction. At this checkpoint its comparison checked all
eight words with the same XOR/OR reduction used by compiler identities; A32
below fixes the restriction and restores the chained comparison. An initial
owned-input fixture referenced a nonexistent unchecked
Vec accessor and was corrected to the actual checked `Vec::get_mut` API. These
were test-fixture failures, not passing executions of the source algorithm.

See [source hashing evidence and remaining gates](unsafe-memory-progress.md#source-blake3-checkpoint).
Compiler identities call the source implementation without test-only selection
or native fallback. This does not establish full U4–U6, G1 or self-hosting.

Frozen validation passes **2,661 tests**, zero failures and two existing ignored
benchmarks: 2,613 workspace/all-targets tests and all 48 audited source entries
in 178.29 seconds. The unfiltered 50-record report is
`target/compiler-check/run-m8odofrz/report.json`, bound to source lock SHA-256
`6457eac1483c3f5375c702239e64d1ec9421f0be7468b97283324dafb22d1d6d`.
Every result matches the preceding native-destructor checkpoint; only actual
code and execution costs change. Original batches and ceilings remain intact.

## A32: nested lazy Boolean values

The authoring compiler now lowers nested `and`/`or` through the value CFG used
by normal completions. Strict evaluation pauses at a control value; its typed
join feeds one shared continuation. The left operand executes first, only the
selected right operand executes, and branch-local bindings do not leak into
the continuation. Literal-skipped operands are not lowered. The existing
specialized handler/label paths remain responsible for their control forms.

A regression failed on `a and b and c` before this fix. The matrix now checks
all eight truth assignments for four nested forms in six contexts: root return,
initializer, call argument, lifted closure, completion subject and tuple field.
Additional tests record exact call-argument side-effect order, skip division
traps, compose Booleans with completion values, and check exactly-once cleanup
of enclosing owners and owners created only in the selected branch. The BLAKE3
high-counter fixture again compares all eight words with chained `and`, without
the temporary bitwise-reduction workaround. Emitted programs are decoded and
reverified before execution. No opcode, artifact generation or budget changes.

This fixes an authoring-language defect, not the remaining source compiler
pipeline, exceptional cleanup, complete U4–U6 ABI or C2/C3 self-hosting gates.

Frozen validation passes **2,664 tests**, zero failures and two existing ignored
benchmarks: 2,616 workspace/all-targets tests and all 48 audited source entries
in 180.46 seconds. The unfiltered 50-record report is
`target/compiler-check/run-szycqpui/report.json`, bound to source lock SHA-256
`facd5ff21c981f4fccde59a572ddff0c8f01999aa7173a9be22bea41e9ea2489`.
Every scalar/tuple result matches A31, and original batches and ceilings remain
intact. The report still records `release_ready: false`.

The first expanded workspace run exposed the separate lifted-closure path;
that failure was fixed before the final workspace run. A concurrent source run
passed its 48 executions but correctly failed its closure audit after that edit.
It is not counted as frozen evidence; the report above is the fresh final run.

## A33: owned callable environment destruction

Concrete lifted environments now retain an authenticated executable cleanup
entry. The destruction planner visits owned captures in reverse layout order;
borrowed captures are not destroyed by the callable. A normal invocation returns
the capture slots' residual initialization state to the owning environment, so
moving a captured field into the invocation does not destroy it again later.
The same normal-return mechanism is used by synchronous native callbacks.

Calling a local closure observes its receiver in place. An ordinary source
copy of a duplicable closure instead creates independent owned capture storage;
borrowed captures retain their original storage. MIR lowering distinguishes
known affine environments from copyable ones and transfers already-evaluated
callable temporaries into bindings. Ordinary aggregate copies without callable
owners retain their existing COW path. Borrowed native-representable captures
retain their source homes, including assignment write-back; immutable scalar
callbacks still require no native allocation.

Regressions cover uninvoked, invoked, transferred, returned and nested owned
closures; retained versus moved-out captures; reverse capture cleanup;
partially consumed aggregate captures; borrowed-owner cleanup; and independent
copies of a capture with a source Drop hook. Callable return checking propagates
the declared contract to a block's tail without erasing preceding invocation
counts. Frozen environment cleanup identity, capture ABI, missing targets and
use of consumed capture operands have codec/verifier regressions.

The source loop gate exposed a tail-call regression: retaining cleanup for
callable parameters made a named-function callback appear to need post-call
work. The budgeted suffix proof can now recognize callable cleanup with no
registered destructor. It still refuses every registered capture destructor
and retains the separate argument/loan checks; no stack limit is increased.

Stage0 program schema is 105. Canonical-cache/bytecode/verifier generations are
20/60/19 in Rust and the source compiler; language/interface generations and the
native ABI generation are unchanged. This does not finish exceptional capture
cleanup, private callable/Array shared layouts, durable external ownership,
the independent G1 extension, U4–U6 or the source semantic compiler.

Frozen validation passes **2,670 tests**, zero failures and two existing ignored
benchmarks: 2,622 workspace/all-targets tests and all 48 audited source entries
in 177.89 seconds. The unfiltered 50-record report is
`target/compiler-check/run-3j7b80x3/report.json`, bound to source lock SHA-256
`e25c2fa291f791530cc75a3274201e90cab49082f0ddf4fa4ce7f91a2d8e25ca`.
All scalar/tuple results match A32. Original batches, assertions and budgets
remain intact, and `release_ready` remains false. The 10,000-step state loop
recycles all 10,000 calls at peak depth 11 under its unchanged 64-frame limit.

The preceding source run passed 47 entries but exposed the tail-call regression
and failed its closure audit after concurrent test corrections. It is not a
passing frozen checkpoint. Earlier focused runs likewise exposed ownership
copy/alias, native-allocation and fixture-contract errors; the final runs above
follow those corrections.

## A34: shared frame ownership and cancellation cleanup

Whole-function cleanup now derives its owner inventory from frozen source
binding identities and ABI parameters, rather than requiring each specialized
return lowerer to enumerate the surrounding bindings. Destruction elaboration
uses this inventory for ordinary returns, protects the transferred result,
excludes invocation captures owned by the callable, and retains conditional
initialization checks. Source binding order determines reverse local cleanup;
owned parameters follow locals. The interprocedural cancellation-handler
lowerer no longer inserts its own duplicate return cleanup.

The same inventory now produces frozen whole-frame cleanup plans. Cancellation
executes compiler-selected destruction glue for abandoned ordinary call frames,
deepest first, retaining checked caller loans and propagating their writes to
surviving source storage. The handler's owning frame survives in its clause and
is cleaned by its own exit. Destruction runs under the ordinary work, allocation
and call-depth budgets. Label and resumption tokens have no captured environment;
disposing a token does not repeat its control engine's Cancel or Leave.

Capture handoff transfers slots into the invocation instead of leaving a second
initialized snapshot in the callable. Normal return and abandoned-frame cleanup
release the invocation loan by transferring only residual slots back. This also
applies to synchronous native callbacks. Tests distinguish retained, transferred,
already-destroyed and partially moved captures; new invocation locals; deeper
owned parameters; reverse frame/local/capture order; and checked caller loans.

Stage0 schema 106 and cache/bytecode/verifier generations 21/61/20 seal the new
frame declarations in Rust and the source compiler. The decoder/verifier checks
header placement, owner uniqueness, capture exclusion and destructor ABI;
linking, host-capability reachability and native destruction-code commitments
retain the new edges. Discovery normalizes associated effect rows consistently
with concrete MIR materialization without moving source diagnostic frontiers.

This is not complete exceptional-cleanup coverage. Lexical inner-scope cleanup
still has lowering-side requests; other nonlocal transfers and retained replay
histories need further ownership integration. General temporary ownership,
private runtime layouts, the exported callable ABI, independent G1 and the
source semantic compiler remain open.

Frozen validation passes **2,685 tests**, zero failures and two existing ignored
benchmarks: 2,637 workspace/all-targets tests plus all 48 audited source entries
in 175.59 seconds. The unfiltered 50-record report is
`target/compiler-check/run-m17oe7s1/report.json`, bound to source lock SHA-256
`b067ba5298964824b1f3da79870353e871f46f67affbd3d23bda8baabf27cc9f`.
All scalar/tuple results match A33. Original batches, assertions and execution
limits remain unchanged, and `release_ready` remains false. Earlier runs
exposed missing cleanup reachability, stale generation assertions and associated
row discovery/diagnostic ordering; this report follows those corrections.
The first source run also passed, but the authoring audit list omitted the new
ownership module. The final report above follows its inclusion in the locked
closure and a fresh complete replay run.

## A35: nonlocal label frame cleanup

Dynamic label calls now use A34's shared frame destruction plan when abandoning
ordinary frames. Cleanup runs deepest first, returns residual invocation
captures before their callable owner is destroyed, and excludes the outgoing
payload. Checked references embedded in that payload are translated into the
surviving destination frame. A runtime label records its executing definition,
not the unspecialized source brand: these differ for lifetime-specialized
functions. Lexical brand validation remains unchanged.

Seven focused regressions pass: abandoned locals and transferred parameters,
owned payloads, three capture ownership states, call-depth enforcement,
deep-frame/local/capture ordering, and partially moved captures. Bytecode
generation 62 mirrors the runtime semantic change in Rust and source request
identity; schema 106 and cache/verifier generations 21/20 remain unchanged.

This does not complete ownership or nonlocal lowering. Retained replay histories
and temporary ownership remain open. Probing also found a label-as-initializer
shape rejected with G6012 and terminal generic-closure calls with non-unit dead
suffixes rejected during VM verification. The focused capture tests use explicit
label parameters and unit dead suffixes; they do not establish those other
source shapes.

Frozen validation passes **2,692 tests**, zero failures and two existing ignored
benchmarks: 2,644 workspace/all-targets tests plus all 48 audited source entries
in 185.92 seconds. The unfiltered 50-record report is
`target/compiler-check/run-0mn6_v5w/report.json`, bound to source lock SHA-256
`72e2add96b6dbf23daa4377698b9ed08d52d86ea82f1f2d6078114cae206ac36`.
All scalar/tuple results match A34; artifact identities change with the
generation. Execution counters match for 49 records; `request/world_registry`
uses 12,187,543 work ticks and 2,896,043 charged elements (previously 12,189,531
and 2,896,166). Original batches, assertions and limits
remain unchanged, and `release_ready` remains false. The first replay attempt
stopped at the stale-lock audit before testing; this report follows a correct
lock refresh and a fresh complete run.

## A36: terminal strict-value control flow

The shared value-CFG lowerer now represents the absence of a normal continuation
explicitly. A terminal call or operation ends its path after evaluating the
strict prefix; no suffix, cleanup return, later operand or join argument is
manufactured. This applies inside lifted closures, initializers, strict call
operands, completion arms and lazy Boolean operands. A computed callee executes
before its arguments. First-class tail-label wrappers use the same segment
result: helpers may return normally to the label destination as well as invoke
it nonlocally.

Bottom-type inference no longer binds an unresolved expected result to `Never`.
A terminal first completion arm therefore cannot erase a later returning arm's
type; completions whose arms are all terminal retain `Never` explicitly. Cache
generation 22 and bytecode generation 63 mirror these changes in Rust and the
source request implementation; schema 106 and verifier generation 20 remain.

Regressions check strict-prefix execution, skipped suffixes and arguments,
callee-before-argument ordering, both lazy Boolean paths, returning versus
terminal completion arms, all-terminal joins, ordinary functions and closure
capture ownership. The label-as-initializer G6012 gap, retained replay cleanup,
general temporary ownership, U4–U6, independent G1, the source semantic compiler
and verified C2/C3 remain open.

Frozen validation passes **2,700 tests**, zero failures and two existing ignored
benchmarks: 2,652 workspace/all-targets tests plus all 48 audited source entries
in 188.40 seconds. The unfiltered 50-record report is
`target/compiler-check/run-bvgwj_9n/report.json`, bound to source lock SHA-256
`7c9ebca1d7d74e48526c7b73fe3ca6aa00e48899405c7081019f57b699fbc2ba`.
All scalar/tuple results match A35; execution counters change with the emitted
control flow, as recorded in runtime-costs.md. Original batches, assertions and
resource ceilings remain unchanged, and `release_ready` remains false. A
15-second CPU sample was collected during this passing run; its wall time is
not an uninstrumented performance comparison. The first workspace attempt found
one additional stale generation assertion. Its concurrent source replay was
deliberately interrupted, not passed; this report follows that test correction,
a fresh source lock and a complete replay.

## A37: indexed ownership-query inputs

Manual `Use` lookup now uses a nominal-head index frozen with the solver's
implementation rules. Core, PlaceFlow and MIR share immutable query inputs;
fresh queries preserve independent tables, cycle state and original default
work limits. Conditional manual ownership still prevents structural fallback
when its proof is unresolved. No schema, cache or bytecode generation changes.

The same eight-worker lifecycle benchmark improves from 26.30 to 10.48 seconds
with identical artifacts, results and counters. These are individual local
runs, not a controlled distribution. The test defaults are now 12 workers and
a 24 GiB cargo-test address-space ceiling; direct commands retain 8 GiB, with
the four-slot gate and 590-second command guard unchanged. CI's workspace job
skips GSC-2 only because the dedicated compiler job audits and runs every entry.

Frozen validation passes **2,702 tests**, zero failures and two existing ignored
benchmarks: 2,654 workspace/all-targets tests and all 48 audited source entries
in 50.03 seconds. The complete 50-record report is
`target/compiler-check/run-2ibhuzod/report.json`, bound to source lock SHA-256
`e2941e18fd203f88c97d84c115aadeb56cec3f0c9ee5caba72b301e21896a06b`.
Every execution record matches A36 exactly. VM budgets and assertions are
unchanged. This improves authoring throughput, not source language coverage;
the remaining ownership, U4–U6, source compiler and C2/C3 gaps remain open.
See [performance measurements](../../docs/stage0-performance.md).

## A38: retained continuation cleanup and replay boundaries

Program execution now destroys abandoned suspended handler branches in
postorder, preserving transferred operation payloads and synchronizing only
activation-branded source storage. Nonlocal label calls, lexical leaves and
cancellation share this cleanup path. Resumed function returns restore their
handler clause before executing the caller suffix; finite replay no longer
repeats that suffix. Existing MIR lowering admits discarded interprocedural
handler leaves and terminal clause paths through the shared value CFG.
Bytecode generation is 64. This is not yet the planned staged-MIR architecture
or a complete continuation-ownership contract.

Focused validation passes 985 destruction, service, runtime-memory and request
tests, plus the subsequently added transferred-payload regression. One audited
source lifecycle entry passes in 10.52 seconds
(`target/compiler-check/run-kuqilgic/report.json`). No full suite was run for
this checkpoint; A37's full-suite numbers are historical. Remaining suspended
return-path ownership and compositional lowering work remain open.

## Source profile established during initial probes

The timings below are historical. One complete-current-suite checkpoint is
`target/compiler-check/run-jgx73yx0/report.json`, recorded after the native
performance changes and A24. See also
[stage0 performance](../../docs/stage0-performance.md).

The later 41-test closure with the first typed source registry reached the
unchanged 590-second command ceiling under the same eight-worker, opt-level-1
profile. It recorded 32 successful executions and exited 143; it is **not** a
passing full-suite run. Evidence is in
`target/compiler-check/run-s1qfvj50/report.json`, bound to source-lock SHA-256
`ced8b98177a4d6b62d121f7aec7c36da23be1156759f20ea86bcb9b33398d9c3`.
This predates key reclamation. Focused history results must not be presented
as completion of the timed-out run. Test compilation throughput needs further
work; the time/memory guards were not increased.

The later audited 13-test selected run (`run-67bunjna`) passes, but is not a
full-suite substitute. Its eight registry modes each compile the same large
fixture/production closure separately. Their combined measured execution
cost is 7,738,393 work ticks and 8,520,167 charged allocation elements—below
the existing per-execution VM limits. The subsequent batched registry run
(`run-5cef3lh6`) passes all eight results in 147.02 seconds, with one independent
decode/verification and one execution budget. Its exact result tuple is
`[35, 96, 47, 235, 750, 466, 91, 91]`; allocation charges are 8,473,372 elements.
The full 45-test attempt still timed out at the unchanged 590-second ceiling
after 29 recorded executions (`run-09yv81mn`, lock
`588a18922ab3515a8171f6f25718b8ac7aff357cb0a76bb7bd4d4f71d3f42060`).
It is not a full-suite pass.

Diagnostics and request-publication histories now also run as independent
scenarios inside a single compiled fixture, returning separately compared
tuple elements. The audited selected run `run-d4w9z5p5` passes all 16 then-named
tests in 259.56 seconds, bound to lock
`017e2180416cb9d896515d1ef25b1da9638904f7aa27e79873239be4c58c21fa`.
The diagnostic batch returns `[42, 42, 42, 42]` against four independently
computed exact-field Rust fingerprints (4,016,234 charged elements).
Publication returns `[27, 23, 26]` (1,196,006 charged elements). The registry
tuple and its profile are unchanged. The separate diagnostic-failure fixture
also passes. These are selected-test results, not full-suite certification.

`VerifiedVmProgram::run_tuple_i64_for_authoring` shares the scalar authoring
runner's execution path and unchanged limits. The new backend regression
checks exact tuple values, strict element/result types, zero work/allocation
limits, independent verification, and unchanged artifact bytes. The native
library/Core/service/backend run passes 1,277 tests. This adds no opcode,
format generation, verifier exemption, or semantic callback.

Evidence has separate `result_i64` and `result_i64_tuple` fields. Each batch
records its profile once for the whole execution; it is not a per-scenario
physical allocation measurement. Do not replace its result vector with a
single sum, reset budgets per scenario, or repeat an aggregate profile as
per-case measurements.
The batch fixtures subsequently moved to one libtest entry each. All original
named comparator functions still execute, but no longer occupy multiple
workers waiting on the same fixture compilation. With the new source-admission
test, the suite has 34 native entries (formerly 46), not fewer scenarios.
The full current run is the time-gate evidence; grouping alone is not a pass.
The grouped 34-entry attempt subsequently hit the same 590-second ceiling
after 25 recorded executions (`run-repdca8p`, source lock
`6d6f4524368ae035ea6b95a3e7b0fe0456c774d649daa1abec509e9e7588adb5`).
It predates name admission, indexed scalar access, and A16. No passing full
closure certificate is inferred from its successful individual executions.
The current C0 service still elaborates body products request-locally, so
retaining its interface cache alone is not evidence of reused body compilation.
Bootstrap-stage admission subsequently adds one native entry, bringing the
current suite to 36. The selected five-entry pass recorded under A18 does not
replace the last full-suite timeout.
Canonical source-collection admission subsequently brings the suite to 37
entries. The current six selected admission/publication/registry entries pass
in 243.80 seconds (`run-eyaz4gdr`, lock
`0482d0b9cb34037dfa4e7fd0755f15e14821df4b94da49b5d11aa38c61e5f5a8`).
No time, memory, or VM execution limit was increased; this selected run also
does not replace full-suite evidence.

The expanded 34-test source-kernel suite passes with the native authoring test
build at optimization level 1 (454.81 seconds; 32.07 seconds for the initial
native build). The unoptimized 20-worker run reached its unchanged 590-second
command ceiling after 21 successful executions. All 21 matching artifact
digests and results are identical in the optimized run. `compiler-check.py`
now defaults only the native Cargo test optimization level to 1 and records it
in its evidence report. Source-program compilation, independent verification,
test/debug assertions, and time/memory/VM guards are unchanged. The 1,040 native
library/service/backend regressions also pass under that test build.

Use explicit record fields and explicit dereferencing on field assignment.
Use named imports across compiler modules: mutually traversed glob imports
can diagnose an unrelated dependency package as private in C0. Tail-position
completion handlers and short helpers avoid C0's unsupported non-tail nested
completion forms. Guard `u64` overflow in source and then use the existing
wrapping primitive; C0 has no direct MIR `+` instruction for every width.

Cursor frames own positions and receive borrowed input per operation. This
also avoids an uncertified nested lifetime-bearing record construction. These
are authoring choices, not reductions to the language accepted by GSC-2.
