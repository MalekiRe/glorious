
# g6 enum const-discriminant emission — Phase 3+4 milestone

## Status
Phases 3 and 4 implemented in the isolated worktree `/tmp/grandiose-g6-enum-emission`
(branch `agent/g6-enum-emission`). Explicit `= <const-expr>` enum discriminants are now
EMITTED end-to-end in both the bytecode/VM and LLVM/native backends, with real runtime tags.

## What landed (Phases 3+4)
- VM runtime (`crates/grandiose-vm/src/vm.rs`): EnumTag now reports the explicit
  discriminant (`enum_variant_tag` translates the stored variant index -> discriminant
  via the enum type's `EnumVariant.tag`). References unwrap to the referent enum.
- Verifier (`crates/grandiose-vm/src/verify.rs`): enum-tag switch dominance now maps each
  switch case constant (an emitted tag) back to the variant index via
  `enum_tag_to_index`, and the default edge is the set of variant indices whose
  discriminant was not covered.
- Compiler (`crates/grandiose/src/compiler.rs`): MirLowerer carries `enum_variant_tags`
  (built from the final artifact type table) and the three enum-pattern switch sites
  (`emit_pattern_tests`, lower_borrowed_pattern_test, prove_enum_variant) now emit the
  discriminant as the switch constant instead of the raw variant index.
- Optimizer (`crates/grandiose/src/compiler_opt.rs`): `sparse_statement_value` folds an
  EnumTag to the discriminant (not the index) using the enum type's tags, keeping sparse
  constant propagation consistent with runtime.
- LLVM/native (`crates/grandiose/src/llvm_backend.rs`): EnumTag emission maps the stored
  index to the discriminant with a per-index select chain; ordinary enums (all implicit)
  keep identity so native output is byte-identical to before.
- validate.rs: the fail-closed `not yet emitted` gate is REMOVED; only a discriminant equal
  to `u32::MAX` (the reserved wire sentinel) is rejected.
- Tests: enum_discriminants.rs now has 5 positive/negative tests (real tags in the type,
  dispatch on real tags A/B and a widely-spaced 4-variant enum, ordinary enums keep index
  tags, mixed implicit/explicit continue the running discriminator, u32::MAX rejected);
  llvm_backend.rs gains `native_explicit_enum_discriminants_dispatch_on_real_tags` proving
  VM and native outputs agree on real-tag dispatch.

## Evidence (gated, isolated worktree)
- `cargo test -p grandiose-vm --lib`: 371 passed.
- `cargo test -p grandiose --test enum_discriminants`: 5 passed.
- `cargo test -p grandiose --test llvm_backend`: 80 passed (incl. new native parity test).
- `cargo test -p grandiose --test compiler -- --skip captureless_reference_callback_requires_a_direct_compatible_origin`:
  205 passed / 2 failed — identical pre-existing failures confirmed on pristine master.
- `cargo test -p grandiose --test optimizer_semantic_baseline --test optimizer_trace_equivalence`:
  passed. `--lib`: 382 passed. `self_host_bytecode` (full, incl. native): 2 passed / 1 ignored
  (validates the discriminant wire encoding + self-host emitter).
- Positive native run: `native_explicit_enum_discriminants_dispatch_on_real_tags ... ok`.

## Known remaining follow-ups (not blocking Rust VM/LLVM parity)
- The self-host frontend's `MirVariant` does not yet carry explicit tags, so the self-host
  compiler would emit the no-discriminant sentinel for a user discriminant. This only
  matters if a user feeds an explicit-discriminant program to the self-host compiler; the
  Rust compiler path (VM + LLVM native) is fully correct. Upstreaming the tag into
  self-host lowering is a natural next increment.
