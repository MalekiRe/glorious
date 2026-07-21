# G1 compatibility goldens

These checked-in `.grbc` files freeze the canonical major-1 container emitted
by the Rust bootstrap VM library:

- `g1-unit-return.grbc` is the smallest executable and returns `Unit`;
- `g1-i64-return.grbc` loads and returns the signed integer `42`.

The compatibility test must decode, verify, execute, and byte-identically
re-encode every fixture with the newest VM. Do not regenerate fixtures for an
ordinary refactor. When an intentional bytecode-format change has followed the
additive release process in `docs/bytecode.md`, regenerate explicitly from the
repository root with:

```console
cargo run -p grandiose-vm --example update_compatibility_goldens -- \
  crates/grandiose-vm/tests/fixtures
```

Review the binary diff and retain older released-seed fixtures when they exist;
compatibility goldens are additive release history, not disposable snapshots.
