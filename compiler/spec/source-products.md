# Immutable source products

`src/source/source.glorious` implements the first concrete compiler products:
an immutable UTF-8 `Blob` and its immutable `LineIndex`. These are actual source
data, not the arithmetic payloads used by the kernel histories. The closed
registry now connects them to tracked queries and separate typed stores;
see [query-registry.md](query-registry.md) for integration evidence and scope.

The blob accepts an already admitted `FileKey` and owns the input bytes through
the standard `String` representation. It checks the configured byte ceiling,
the u32 span range, and UTF-8 validity, and computes the exact BLAKE3 digest of
the bytes. Invalid UTF-8 reports the reference validator's `valid_up_to` offset.
Only shared text/byte views are exposed, with explicit owner lifetimes. This
does not implement request normalization, path/package identity admission, or
the normalized-world fingerprint.

Line construction starts with offset zero even for an empty source. Each step
examines one byte and records the offset immediately after LF; CR, CRLF,
Unicode separators, and trailing LF have the same behavior as the reference
`LineIndex`. The builder owns its cursor and partial vector. Source file,
digest, and length are checked on every step. The line-count ceiling includes
the initial line and cannot exceed the u32 result range.

Position lookup rejects out-of-range and non-scalar-boundary offsets before
work begins. Its private frame first advances a binary search one comparison
per step, then counts one UTF-8 scalar per step from the selected line start.
Non-BMP scalars contribute two UTF-16 units; combining characters are not
collapsed. A future public facade maps `Failure::Offset` to the reference
API's `None`, while retaining cancellation/resource failures separately. Both
the supplied blob and index must match the frame's immutable source stamp.

Every builder failure discards its private work. Cancellation is checked on
admission, each step, and final extraction. Early extraction consumes/discards
the unfinished frame; successful extraction is one-shot. Construction charges
logical byte work before the existing UTF-8/hash leaves execute; index and
position steps charge one unit each. These are not hierarchical memory leases
or physical allocation/copy/polling certification. The initial hash/UTF-8
leaves still execute synchronously.

The index fingerprint is an internal conservative source-origin projection:
the u64-LE length-prefixed domain `grandiose-line-index-v1`, followed by the
full file digest and source-byte digest, hashed with BLAKE3. Private construction
makes this determine the index. It is not a Stage0 wire-format commitment or
a substitute for any public request/build fingerprint.

## Executable evidence

`source/positions.glorious` encodes exact bytes, file/source/index digests, line
starts/counts, and every byte-offset position through one byte past the end,
plus u32::MAX. Its native test compares the complete encoding's digest against
the Rust reference over twelve inputs: empty text, consecutive/trailing LF,
CRLF and lone CR, NUL, multibyte scripts, emoji, combining/joining sequences,
Unicode scalar-width boundaries, and Unicode separators. Expected buffer size
is checked so test encoding cannot silently truncate.

`source/failures.glorious` compares twelve invalid UTF-8 sequences with Rust's
validator and exercises byte/line capacity, different source revisions,
cancellation, work exhaustion, aborted/early/one-shot extraction, and closed
frame reuse. The initial two source tests pass together (72.27 seconds). The
subsequent extended history adds partial-progress cancellation, successful
one-shot extraction, and identical bytes under a different file identity;
it passes with all 77 assertions. The first full run exposed missing top-level
`source` declarations in older kernel fixtures (`G3103`); the shared harness
now supplies the explicit current root-module list while retaining all
production sources. Full expanded-closure verification is recorded separately.

These tests compile Glorious source through C0, independently decode/verify
its serialized G0 program, and execute that program. They do not establish
G1 execution, a lexer, or self-compilation. Provider dependency tracking and
retention have separate registry integration histories.
