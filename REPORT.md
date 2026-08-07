# g6 enum const-discriminant emission — Phase 2 milestone

## Status
Phase 2 (structural: thread the explicit tag into `Type::Enum EnumVariant(Option<u32>)`,
and keep the serialized bytecode format in sync across the Rust encoder/decoder AND the
self-host frontend emitter) is implemented and validated in the isolated worktree
`/tmp/grandiose-g6-enum-emission` (branch `agent/g6-enum-emission`).

## What landed (Phase 2)
- `crates/grandiose-vm/src/bytecode.rs`: `EnumVariant` gains `pub tag: Option<u32>` plus a
  `discriminant(index) -> u32` helper (`tag.unwrap_or(index)`), preserving implicit-index
  behavior for ordinary enums. The `Type::Enum` wire encoding now carries each variant's
  emitted tag as a u32 (`u32::MAX` = no-discriminant sentinel, which the frontend will reject
  as a source discriminant so it never collides); the decoder reads it back.
- `crates/grandiose/src/compiler.rs`: new `enum_declaration_tags(&EnumDecl) -> Vec<Option<u32>>`
  computes effective per-variant tags (C-style running discriminator for mixed enums; all-`None`
  for enums with no explicit discriminant — ordinary enums untouched). The three
  `Type::Enum` lowering sites (main nominal table, closure nominals, late/generic nominals)
  now stamp the per-variant `tag`.
- self-host frontend `self-host/src/backend/emission/emission.glorious`: `write_enum_variants`
  now writes the discriminant u32 sentinel (`4294967295`) per variant, exactly matching the
  Rust encoder so self-host-emitted artifacts still decode canonically. Self-host `MirVariant`
  does not yet adopt explicit source discriminants (gate still fails closed), so the sentinel is
  always written for the bubble's implicit enums.
- The validate() fail-closed gate is UNTOUCHED in this phase (explicit discriminants still
  rejected with the `explicit variant discriminants are not yet emitted` diagnostic).

## Evidence (all in the isolated worktree with the gated RAM tool)
- `cargo build -p grandiose-vm` / `-p grandiose`: OK (ungated).
- Gated `cargo test -p grandiose-vm --lib enum_`: 25 passed (includes new
  `enum_variant_discriminant_respects_explicit_tags` and
  `enum_explicit_tags_survive_encode_decode_roundtrip`).
- Gated `cargo test -p grandiose --test enum_discriminants`: 2 passed (gate intact).
- Gated `cargo test -p grandiose --test compiler -- --skip captureless_reference_callback_requires_a_direct_compatible_origin`:
  205 passed / 2 failed. The 3 failures (incl. the skipped one) were confirmed PRE-EXISTING by
  running the identical command on a pristine `origin/master` (4432bce) worktree — identical result.
- Gated `cargo test -p grandiose --test type_syntax --test parser_conformance --test llvm_backend`:
  only `retains_kinded_open_effect_row_tails` fails; confirmed PRE-EXISTING on master (unchanged).
- Gated `G1_SELF_HOST_BYTECODE_CHECK_ONLY=1 cargo test -p grandiose --test self_host_bytecode
  self_hosted_frontend_emits_canonical_executable_bytecode_in_vm_and_native`: PASSED (752s) —
  the self-host bundle (including the edited emission.glorious) still compiles, encodes, and
  round-trips through decode+verify.

## Next
Phase 3: make Switch + verifier dominance translate tag<->index and the VM EnumTag report the
discriminant; Phase 4: LLVM/native parity + remove the fail-closed gate + positive parity test.
