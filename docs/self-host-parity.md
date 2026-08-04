# Self-hosted compiler parity gate

The self-hosted compiler is complete only when it accepts, rejects, types,
lowers, and executes the same generation-1 programs as the Rust bootstrap
compiler. Self-compilation is the final integration test, not the mechanism for
discovering missing language features.

## Required order

1. Add a focused Rust-oracle/self-host parity corpus for the feature.
2. Make lexer, scanner, header, resolution, Typed Core, MIR, bytecode, and
   diagnostic results agree at every layer the feature reaches.
3. Run the relevant ordinary bootstrap tests and self-host parity tests with
   the repository memory limiter.
4. Keep the feature in the cumulative self-host conformance corpus.
5. Attempt stage 1 -> stage 2 -> stage 3 only after the cumulative parity gate
   is green.

## Existing parity layers

| Layer | Test | Current scope |
| --- | --- | --- |
| Lexer | `self_host_lexer.rs` | token stream and lexical rejection |
| Scanner | `self_host_scanner.rs` | declaration shells and nesting |
| Headers | `self_host_headers.rs` | callable signature syntax |
| Interfaces | `self_host_interfaces.rs` | aliases, fixities, structs, enums, callables |
| Bodies | `self_host_body_grouping.rs` | expression grouping and body arenas |
| Resolution | `self_host_name_resolution.rs` | locals, functions, structs, enum variants, modules |
| Typed Core | `self_host_typed_core.rs` | calls, literals, tuples, nominal construction/projection |
| Backend | `self_host_bytecode.rs` | selected Core-to-bytecode behavior and canonical encoding |

Every row must grow from its current focused corpus into the corresponding
bootstrap feature corpus. A feature is not complete merely because a later
layer happens to accept one production example.

## Port sequence

- [x] Distributed lexer/scanner basics, modules, callable headers, aliases,
  nominal declarations, locals, ordinary calls, literals, tuples, nominal
  construction/projection, and basic variant dispatch.
- [ ] Effects slice: effect and operation headers, qualified operation
  resolution, effect-row normalization, `perform`, deep and partial handlers,
  terminal operations, resumption binders/quantities, `resume`, `cancel`,
  outward transfer, and label-indexed effects.
- [ ] Ownership parity: place paths, loans/reborrows, move states, `Use`,
  cleanup, custom `Drop`, and path-sensitive suspension.
- [ ] Generic parity: trait evidence, associated types/effect rows, HRTBs,
  lifetime substitution, callable evidence, and specialization.
- [ ] Pattern/refinement parity: complete decision DAGs, aggregate binders,
  reachability/exhaustiveness, `is`, and joined availability facts.
- [ ] Backend parity: complete Core validation, MIR effects/captures/cleanup,
  optimizer semantic equivalence, bytecode verification metadata, and LLVM
  agreement where the bootstrap suite requires it.
- [ ] Tooling/diagnostic parity: stable phase/category codes, spans, malformed
  input rejection, resource limits, and deterministic output.

## Final gates

- All ordinary Rust bootstrap unit and integration tests pass.
- Every supported bootstrap language corpus has a self-host parity case; the
  self-host result matches the Rust oracle rather than merely succeeding.
- All test executables run with the repository 8 GiB address-space limiter.
- The Rust bootstrap emits stage 1, stage 1 emits stage 2, and stage 2 emits
  stage 3.
- Stage 2 and stage 3 are byte-identical canonical artifacts.

