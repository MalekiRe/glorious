# Compiler-support primitive boundary

M03 identity requires one additional manifest-bound leaf: `compiler.blake3.v1`.
It is a low-level byte primitive, not a source-semantic fallback.

## Contract

- Input: an immutable `Bytes` value.
- Output: exactly 32 digest bytes, using unkeyed BLAKE3.
- Authority: selected by an exact runtime-manifest declaration identity and
  signature, never by spelling, order, or a host fallback.
- Determinism: equal inputs always produce equal output bytes on every host.
- Limits: input length is bounded by the existing VM/resource limits; the
  operation allocates only its fixed 32-byte result beyond input storage.

The self-host identity module owns domain separation and length-delimited part
encoding in ordinary Grandiose code, then calls this leaf once per completed
digest. A streaming variant may be admitted later only if profiling shows that
the bounded `Bytes` interface is a bootstrap bottleneck.

## Required admission tests

1. Official BLAKE3 vectors plus Stage0 `Digest::of_bytes` parity.
2. Distinct part boundaries produce distinct domain-separated identities.
3. Correct spelling with wrong declaration identity or signature is rejected.
4. Candidate and verified VM artifacts agree on output and resource failures.
5. The primitive is absent from the compiler semantic-fallback capability set.

Stage0 now implements this as the sealed `PrimitiveRole::Blake3` leaf. It has
its own VM opcode, schema 89 encoding, verifier contract, and candidate plus
verified execution coverage against `BLAKE3("abc")`. M03 remains missing: the
self-hosted identity module still needs to bind the leaf through its runtime
declaration and implement Stage0 `Digest` semantics. No alternate hash or
Rust callback is permitted.

`tooling/self-host-stage0-blake3-check.sh` additionally proves the source
boundary end-to-end: `Text -> Bytes -> BLAKE3 -> Bytes -> u8` returns the
first known `BLAKE3("abc")` digest byte (`0x64`) through manifest-selected
leaves.
