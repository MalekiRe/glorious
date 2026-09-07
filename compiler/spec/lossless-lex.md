# Lossless lexical products

`src/source/lex/lex.glorious` implements the lexical algorithm in Glorious,
over an admitted immutable UTF-8 `Blob`. It does not call the Rust lexer or
read the world. `registry::lex` is the third closed typed query family and
demands `SourceBytes` through the shared journal/replay engine.

The product retains original byte offsets, all trivia, an end token, recovery
codes/messages, and delimiter pairing. Its 13 token kinds correspond to the
Rust lexical reference; punctuation is represented by its ASCII byte. The
grammar covers radix numbers, separators, fractions/exponents and invalid
tails, quoted strings/bytes/characters and escapes, lifetimes, nested block
comments, operators, and malformed delimiters. Source spelling is obtained
from a blob authenticated by file identity, digest, and length. The existing
`LineIndex` query remains separate: this is not the full Rust `LexedFile` API,
nor a parser or a completed frontend milestone.

## Stepping and ownership

Each transition charges the actual request controls and advances by at most
four source bytes. Scanning and token insertion are separate transitions.
Before insertion, `next_memory` exposes the exact next vector backing-capacity
delta using the actual padded element layout. The registry reserves both the
shared root and the lexical phase before the push. Delimiter links temporarily
reuse unresolved opener tokens' matching slots; closing/recovery resolves each
link before publication. There is no separately allocated delimiter stack.
Vector growth and product fingerprinting are synchronous; bounded cursor
progress is not a universal physical-work or allocation-latency bound.

Cancellation, work failure, source mismatch, and premature extraction close
the builder. Registry cleanup destroys partial storage before refunding its
leases. Published lexical products occupy their own typed arena; retained
root/phase ownership survives producer close and parent reuse until final
product disposal. Lexical keys participate in marking and stepped sweeping.
The memo fingerprint hashes a versioned algorithm tag, file identity, and
source digest. It is deliberately conservative, not a semantic token hash.

The public dependency ledger has no lexical node. Publication walks the
committed `Lex -> SourceBytes -> Input(FileKey)` observations and derives the
existing public input fact. It neither invents a node nor authors a second
dependency graph. Semantic families will need their own exact projections.

## Executable comparisons

`tests/source/lex.glorious` compares 357 independent source strings against
the Rust lexer: every token kind, punctuation byte, offset, spelling, recovery
code/message, and delimiter pair. The corpus includes every ASCII byte,
delimiter combinations, numeric prefix/tail combinations, and quoted escaped
and truncated inputs. The independently encoded reference is 113,613 bytes.
The fixture releases each source blob before proceeding to the next case.

`tests/source/lex_controls.glorious` cancels and exhausts work after every
transition prefix, checks bounded cursor progress through a comment with an
8,192-byte body, and compares preflight reservations to actual vector capacity at
every step. It also checks token limits, source mismatch, failed preflight,
and one-shot extraction. Existing execution limits are unchanged.

`tests/registry/lex.glorious` covers cold/memoized/reused/changed products,
phase/root ownership, pinned retirement, foreign-session rejection, repeated
root/phase/store/token-capacity failures, and waiter takeover after closing a
producer with partially allocated lexical storage. The complete existing
public-dependency history also runs with lexical products, including withheld
and failed publication and cancellation at every publication boundary.

## Authoring prerequisites

Named-region `Slice`, `SliceMut`, and `Str` views now preserve their input
region through borrowed subviews and iterators. Core's invariant reference and
mutable-pointer checks first instantiate the callee's expected lifetime before
the reverse comparison, using rigid comparison for the resolved caller type.
Fixed incompatible regions remain rejected. Two Core unit tests cover generic
and bound regions, caller/callee index collisions, and negative invariance;
library fixtures exercise real borrowed helper returns and six illegal static
extensions. These changes do not resolve all outstanding ownership failures.

`Vec` exposes allocation-free backing and next-capacity byte measurements,
including padded and zero-sized elements. `ByteBuf::put_u64` reserves once and
stores eight ordinary bytes, preserving unaligned offsets, little-endian
encoding, and failure atomicity without a host codec. One reserve can select
a different private growth capacity than eight individual pushes. This reduces
the corpus encoder's allocation/work cost without shrinking the oracle corpus
or increasing its VM limits. The standard-library suite includes layout,
region, and unaligned/failed-word-store regressions.

## Revalidation (September 7)

The complete source gate passes all 60 tests in 415.72 seconds, with 62
execution records in `target/compiler-check/run-8wjo_51m/report.json`.
The existing 12 workers, 590-second guard, 24 GiB address-space ceiling, and
VM limits are unchanged. The report remains `release_ready: false`; all 36
profiled records finish with zero live raw/home backing bytes and unsaturated
counters. The 26 unprofiled records have empty counters, not measured zeros.
The closure-tracking regression and source-lock audit also pass.

The lexer corpus reaches 74 frames, 86,170,371 work ticks, 13,976,801 charged
allocation elements, and a 147,307-byte simultaneous native backing peak.
The cancellation/preflight batch returns `[5, 4, 8]` at 33 frames and an
18,624-byte backing peak. Lexical registry ownership returns seven ones;
public-dependency publication returns `[1, 1, 1, 1, 1, 1, 24]`, preserving all
24 cancellation boundaries from the original history. The independent focused
ownership run passes in 127.27 seconds. Its waiter explicitly drives through
setup `Continue` events before requiring `Waiting`; no assertion was removed.

The selected authoring run (`target/lex-authoring-broad.log`) has 1,101 passes
and the same 15 previously recorded failures: eight Core, two destruction,
two lifetime-inference, and three VM-backend tests. All 175 standard-library,
28 native-bridge, 19 runtime-memory, and four runtime-storage tests pass.
These are selected-suite results, not a clean workspace or a self-hosting claim.
