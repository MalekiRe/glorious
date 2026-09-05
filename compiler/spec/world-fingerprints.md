# Canonical input fingerprints after A18

This is an intentional correction to the ambiguous Stage0 v1 commitments,
not a new narrow query key. The source normalizer must reproduce this full
world identity; individual providers still track their actual observations.

Every field below is encoded as `u64_le(byte_length) || bytes`. Integers have
their stated fixed-width little-endian payload. Counts are u64, presence and
mode/role tags are u8, and digests are their existing 32 canonical bytes.
No host paths or input enumeration order are used. Collections are ordered by
the existing normalization rules, not by hash-table iteration or wire-tag order.

## World v2

Fields, in order:

1. UTF-8 `grandiose-stage0-world-v2`.
2. Compiler producer digest, then six u32 generations: language, query,
   interface, cache, bytecode, verifier.
3. Mode u8: Check 0, Build 1, Test 2, Inspect 3, Ide 4, Bootstrap 5.
4. For Bootstrap only: `bootstrap-stage-v2`, ordinal u32, producer digest,
   optimization level u8, maximum source count u32, maximum source bytes u64,
   expected-artifact presence u8 (0 or 1), then its digest when present.
5. Root package and target, both UTF-8 strings.
6. Source count, then each source's package, logical path, FileKey digest,
   and verified content digest. Sources sort by `(package, path, FileKey)`.
7. Semantic option count, then UTF-8 key/value pairs in key order.
8. Codegen option count, then UTF-8 key/value pairs in key order.
9. Capability count, then UTF-8 capability strings in canonical lexical order.
10. Optional runtime input, encoded as below.

The result is the existing `Digest::of_bytes` BLAKE3 commitment over all fields.
Build identities supplied independently still retain their explicit generation
values; the shipped Stage0 constructor now uses cache generation 4.

## Optional runtime input

First emit presence u8. Absent input has no following fields. Present input has:

1. Standard-library package UTF-8 string.
2. Primitive selector count, then each role's stable u8 tag, module path,
   and declaration name. Ordering is the native derived `PrimitiveRole` order,
   then module/name, not numeric tag order. A16's checked integer division
   tag is 182; all other role tags are unchanged.
3. Host-import count, then each module path, declaration name, capability,
   and symbol. These rows sort lexically by all four fields.

This exact helper is used in both world and bootstrap source commitments.
It is not the separate declaration-bound runtime-manifest digest encoding.

## Bootstrap projections

Source semantics encodes `grandiose-stage0-bootstrap-source-semantics-v2`,
four u32 generations (language, query, interface, cache), root package,
source count and `(package, path, content digest)` rows, semantic option count
and key/value rows, then the optional runtime input above.

Codegen encodes `grandiose-stage0-bootstrap-codegen-v2`, target, codegen option
count and key/value rows, capability count and strings, then bytecode and
verifier generations as u32 values.

Producer identity and stage ordinal are provenance, intentionally absent from
these convergence projections. Bootstrap manifest schema 3 attests these new
commitments; schemas using the old semantics are rejected. The existing
manifest layout and independent artifact/byte-equality checks are unchanged.
