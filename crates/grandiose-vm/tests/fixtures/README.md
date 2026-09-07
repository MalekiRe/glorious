# Current G1 encoding goldens

These checked-in `.grbc` files exercise the canonical major-1 container emitted
by the Rust bootstrap VM library:

- `g1-unit-return.grbc` is the smallest executable and returns `Unit`;
- `g1-i64-return.grbc` loads and returns the signed integer `42`.

The encoding test must decode, verify, execute, and byte-identically
re-encode every current fixture. Do not regenerate fixtures merely to hide a
regression. For an intentional bytecode-format change under the pre-alpha
change policy in `docs/bytecode.md`, regenerate explicitly from the
repository root with:

```console
cargo run -p grandiose-vm --example update_compatibility_goldens -- \
  crates/grandiose-vm/tests/fixtures
```

Review the binary diff against the new contract and update its producers and
consumers together. These are current-contract regression fixtures, not a promise
to preserve old decoders, released seeds, or backward compatibility.
