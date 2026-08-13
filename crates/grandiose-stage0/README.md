# Grandiose stage-zero compiler

`grandiose-stage0` is a new Rust compiler implementation. It does not call,
wrap, or share frontend, semantic, MIR, or code-generation code with the
existing `grandiose` crate. It shares only the frozen VM artifact contract at
the eventual compiler/verifier boundary.

The implementation follows `docs/self-hosted-compiler/` in dependency order:

1. Architecture/trust boundaries and immutable request worlds.
2. Typed queries, identities, invalidation, persistence, determinism, and
   operational safety.
3. The complete frontend and static semantics.
4. Typed Core, PlaceFlow, MIR, optimization, and canonical VM emission.
5. Verification, tooling, differential testing, and self-host convergence.

This crate is deliberately not a compatibility wrapper or a reduced "toy"
compiler. A language feature is only marked complete when it has reached the
same semantic, operational, diagnostic, incremental, and verifier contracts
required by the design documents.

