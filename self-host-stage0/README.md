# Stage0-equivalent self-hosted compiler

This is a new implementation, not a continuation of the retired `self-host/`
prototype. It must port every behavior of the frozen Rust Stage0 baseline
without a Rust semantic fallback before any Stage1 artifact is accepted.

The runtime-support package admits digest, byte-buffer, and `branch-bool`
leaves. Stage0 lowers root calls and strict `i64` arithmetic operand
continuations of manifest-bound `branch-bool` to explicit CFG, invoking only
the selected thunk. General nested/control-combinator forms are not yet a
completed bootstrap control library, so modules must not claim them as general
source control.

`src/` mirrors the 36 Stage0 module names in
[`module-ledger.tsv`](../docs/self-host-stage0/module-ledger.tsv). A module is
added only with its full facade contract, mapped test cases, canonical boundary
snapshot, and no-fallback evidence; empty or fake-success modules are forbidden.

The build, differential, and bootstrap rules are specified in
[`glorious-stage0-self-hosting-plan.md`](../docs/glorious-stage0-self-hosting-plan.md).
