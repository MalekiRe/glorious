# Stage-zero crate boundaries

The compiler now has two small, independently testable lower-level crates:

- `grandiose-compiler-base`: stable identities, quantity algebra, diagnostic
  vocabulary, safety classification, and shared lexical module authority.
- `grandiose-syntax`: lossless source lexing and declaration scanning. It
  depends only on the base vocabulary, not semantic analysis or a VM.

`grandiose-stage0` remains the integrating compiler and depends on both, plus
the existing `grandiose-runtime` storage substrate. Its old `identity`,
`quantity`, `diagnostic`, `source`, and `scanner` modules are compatibility
re-exports, so downstream compiler callers retain the same Rust type identities
and import paths. No source-language or artifact schema changed.

The runtime and base vocabulary can build independently; syntax follows the
small base crate. An edit to stage-zero implementation code does not rebuild
either extracted crate. Base API changes can still invalidate both consumers.
This is a bounded separation, not a claim of maximum parallelism or a measured
build-time speedup. The semantic/trait/MIR/VM implementation remains together:
forcing those mutually coupled stages into separate crates would first require
a larger contract refactor and would interfere with current feature work.

Standalone checks use the single LLVM O1 profile:

```sh
bash tooling/cargo-fast.sh test -p grandiose-compiler-base -p grandiose-syntax
```

Existing stage-zero source, scanner, quantity, visibility, header, and query
tests continue to exercise the compatibility boundary through the integrating
crate. No tests were removed or ignored to perform the split.
