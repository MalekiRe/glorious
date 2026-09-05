# Canonical diagnostic products

The source builder retains structured code, class, severity, message, primary
span, input fingerprint, related locations, named facts, and explanation frames.
It is a component of request publication, not the complete service boundary.

Fact identity matches the reference tuple: code, class, severity, primary span,
and message. Input-world fingerprints are deliberately excluded from that key.
A stable identity sort merges duplicate facts without discarding provenance;
related locations, facts, and explanation frames are independently sorted and
deduplicated. Presentation order is source-first, then canonical span, severity,
code, class, and message. Without an explicit request fingerprint policy, the
first duplicate's fingerprint survives, as in the reference's stable sort.

Optional span validation requests one file-length observation at a time. The
builder checks start/end bounds and replaces an invalid primary or related
location with the exact `G7014` invariant diagnostic. A request adapter must
resolve these observations in its authenticated pinned world; the low-level
builder does not itself authenticate a world or the supplied lengths.

Error limiting runs after canonicalization, preserves warnings and notes,
normalizes a zero error limit to one, and reserves the last error slot for the
exact `G7013` suppression fact. The resulting batch is canonicalized again,
including any collision with a pre-existing suppression diagnostic. An explicit
request fingerprint policy also binds generated diagnostics to that world.

Sorting, provenance merging/deduplication, validation, and limiting use explicit
cursors. Every step and length answer charges work. Errors discard unpublished
staging; final extraction checks cancellation and consumes the builder's owned
state. The resulting batch exposes only a shared slice.

The differential fixture encodes every observable field with length prefixes,
canonical digest bytes, and fixed-width integer tags, then compares all 256
BLAKE3 bits against the same encoding of the Rust reference result. That
encoding is test-only, not a compiler wire format. The canonicalization and
validated/error-limited histories, including zero-limit handling and an
unsuppressed invalid-related-span replacement, pass this exact-field comparison.
A separate
executed fixture covers capacity, cancellation before recording and during
stepping/span validation/final extraction, premature extraction, invalid ranges,
and atomic digest-output capacity rejection.

A source-storage liveness failure was traced to passing a unique
diagnostic reference into a helper and then reusing it. The helper call now
uses an explicit reborrow; verifier checks and Stage0 lowering are unchanged.

## Integration and certification still open

- The combined request adapter now binds the builder to stored controls and
  resolves spans in the pinned world; its three integrated histories pass.
  See [request-publication.md](request-publication.md).
- Attach actual typed outcome/artifact ownership and prevent commit while query
  attempts or body scratch are active. No package-only or diagnostic-only
  commit establishes that complete request invariant.
- Port the service's code-driven semantic-provenance enrichment, diagnostic
  constructors/facades, JSON/text rendering, and complete public failure mapping.
- Add hierarchical memory leases and physical cost/retention measurements.
  Current admission bounds raw diagnostic/provenance counts, not all string
  bytes or allocator usage. Sorting is stepped insertion sort, and aggregate
  transfers and final backing-storage release can perform size-dependent work.

Decimal count formatting belongs to the standard library's ordinary
`Display for usize` implementation. It adds no native formatting operation.
