# Self-host scalar std-lib parity — g16 milestone

## Status: COMPLETE (scalar ledger row flipped green)

This worktree injects a scalar standard-library mirror into the self-hosted
compiler so scalar arithmetic helpers (`wrapping_*`, `bit_*`, `shift_*`) resolve,
lower, and COMPUTE exactly like the native distributed standard library, and gets
the `scalar_surface` ledger row asserted green by `self_host_stdlib_parity`.

Worktree: `/tmp/grandiose-g16-selfhost-scalar-std`
Branch:   `agent/g16-selfhost-scalar-std` (isolated; not pushed/merged to master)

## What changed (2 files, +170/-11)
- `self-host/src/compiler/compiler.glorious`
- `crates/grandiose/tests/self_host_stdlib_parity.rs`

### compiler.glorious
1. **Scalar prelude injection (root cause fix).** `session_source` previously only
   appended the minimal prelude when `result_prelude_missing()` returned true, and
   that predicate used `lexeme_id(&"Result")`, which returns fals when a source
   never mentions the word `Result`. So a scalar-only program (which never says
   `Result`) got *no prelude at all* and `wrapping_add` did not resolve
   (body-resolution `UnknownFunction`). Added `result_declared()` (correct check:
   source declares its own `Result` type) and made `session_source` ALWAYS append
   the scalar mirror, appending the minimal `Result` nominal only when the source
   does not declare one. Added `scalar_only_prelude()` alongside
   `minimal_interface_prelude()`; both append the injected scalar helpers
   (9 frozen leaves + 9 user-facing generic wrappers) mirroring native
   `distributed_std` `wrapping_*/bit_*/shift_*`.
2. **Primitive authority by wrapper name.** `runtime_leaf_identity` grants
   bytecode primitives by *trusted shell-id position* in the canonical
   standard-library prefix, so an injected `__g1_int_wrapping_add` at an arbitrary
   session position lowered as an *ordinary* function (returning its left operand)
   instead of `IntWrappingAdd`. Added a scoped, name-based fallback mapping the
   user-facing wrapper spellings (`wrapping_add`, `wrapping_sub`, `wrapping_mul`,
   `bit_and`, `bit_or`, `bit_xor`, `bit_not`, `shift_left`, `shift_right`) to their
   primitives (5..13), so the injected wrappers lower truthfully. The wrapper
   bodies are ignored (the primitive lowering rebuilds MIR), which matches the
   native "trusted leaf" behavior.

### self_host_stdlib_parity.rs
- Moved `scalar_surface` OUT of `FRONTIER`; added 10 scalar cases to `SUPPORTED`
  (wrapping_add i64/u8, wrapping_sub i64, wrapping_mul u64, bit_and/or u64,
  bit_xor i64, bit_not i64, shift_left i64, shift_right u64) plus the 2 existing
  Result cases.
- Added `self_host_stdlib_scalar_semantics_match_native` asserting each lowering
  surface COMPUTES the same value through the self-hosted compiler as through the
  Rust oracle (wrapping_add 20+22=42, wrapping_sub 50-8=42, wrapping_mul 6*7=42,
  bit_xor 12^10=6).
- Updated the file header/intro comments to document the scalar surface.

## Validation (exact gated release commands + results)
All run via `ram-gate.sh cargo test --release -p grandiose --test <t> -- --nocapture`
(CARGO_TARGET_DIR=/home/malek/.cache/grandiose-agent-targets/g16-selfhost-scalar-std).

- self_host_stdlib_parity:
  - supported: 2 result + 10 scalar cases => self-host phase 0 (accepted, parity).
  - scalar semantics: wrapping_add=I64(42), wrapping_sub=I64(42), wrapping_mul=U64(42),
    bit_xor=I64(6) — each MATCHES native.
  => `test result: ok. 2 passed; 0 failed` (901s)
- self_host_bytecode: `ok. 3 passed; 0 failed; 1 ignored` (fixed-point is ignored) (2653s)
- self_host_headers: `ok. 16 passed; 0 failed` (1498s)
- self_host_body_grouping: `ok. 26 passed; 0 failed` (3665s)
- self_host_typed_core: `ok. 7 passed; 0 failed; 1 ignored` (700s)

No regressions in the self-host frontend/backend suites.

## Frontier after this milestone (still unported, oracle-valid)
collection_extended_surface / collection_foundations / hash_collections /
index_vec_traversal / range_helpers / option_surface / slot_surface /
toolkit_foundations / vec_copying_growth / vec_deque / vec_destructive_shrink /
vec_into_iter — all rejected by self-host at interface-collection (no Vec/HashMap/
Option/... surface), exactly as before. `scalar_surface` is no longer in the frontier.

## Notes / scope
- The scalar wrapper bodies are placeholders (ignored by primitive lowering), so
  the injected wrappers lower directly to `IntWrapping*`/`IntBit*`/`IntShl|IntShr`.
- `wrapping_neg` and the `wrapping_convert_to_*` cast family are deliberately left
  OUT of the injected prelude this milestone (their generic bodies need integer
  literals / cross-width casts that this self-host slice does not yet handle
  narrowly); they remain future work.
- Nothing pushed or merged to master.
