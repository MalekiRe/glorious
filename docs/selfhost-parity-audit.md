# Self-host parity audit: remaining unported suites and 5 smallest high-leverage ports

Audit date: this commit. Branch: `agent/deepseek-parity-audit`.

## 1. Current ledger state (evidence)

The checked-in inventory `crates/grandiose/tests/self_host_parity.tsv` tracks every
bootstrap integration suite (`crates/grandiose/tests/*.rs`). After this commit:

| Status | Count | Notes |
| --- | --- | --- |
| unported | 95 | no self-host oracle comparison |
| partial | 38 | some cases / infrastructure linked to a named `#[test]` |
| covered | 10 | a Rust-oracle/self-host comparison executes for the suite |

Unported by family: standard_library 23, compiler_pipeline 18, ownership_lifetimes 13,
effects_control 12, types_traits_generics 11, backend_runtime 4, mir_lowering 4,
optimization_specialization 4, modules_cli_sessions 3, syntax_frontend 3.

The eight self-host layers and their live gates (all exercising the `.glorious`
sources under `self-host/src/{frontend,probe}` in both the VM and the native LLVM
runtime):
- Lexer `self_host_lexer.rs`, Scanner `self_host_scanner.rs`,
  Headers `self_host_headers.rs`, Interfaces `self_host_interfaces.rs`,
  Bodies `self_host_body_grouping.rs`, Name resolution `self_host_name_resolution.rs`,
  Typed Core / effects `self_host_typed_core.rs`, Backend `self_host_bytecode.rs`,
  plus the accept/reject semantic control gate `self_host_semantic_control.rs` and
  compiler-pipeline gate `self_host_compiler_pipeline.rs` (baseline-blocked).

## 2. Port shape (how every port is recorded)

A "port" of a suite S moves S from `unported` to `partial`/`covered` by:
1. Distilling S's Rust test sources (positive declarations + stable rejections)
   into the focused `corpus`/`(source, accepted)` array of the appropriate gate.
2. Only when the self-host frontend layer implements the behavior: the Rust oracle
   (`encode_rust_*`/`compile_*` acceptance) and the self-host probe must agree
   byte-for-byte (wire format) or accept/reject identically.
3. Linking S in `self_host_parity.tsv` to the exact `#[test]` function name, so
   `parity_manifest_is_complete_and_truthful` stays green.
4. Never substituting a manifest relabel, a wrapper, or an unsupported fallback
   for real behavior — a `covered` row must point to an executable comparison.

## 3. The five smallest high-leverage ports (prioritized)

Selection criteria: (a) fewest Rust source lines to absorb, (b) the self-host layer
that the suite exercises is already the most mature/high-coverage, (c) the port is
composable with the existing per-family gate (headers / interfaces / typed-core /
name-resolution), and (d) it closes a family gap rather than re-covering a family
that is already mostly done.

### P1 (DONE in this commit) — effects_control headers for shared resumption quantities
Rust suites: `shared_handler_resumption_quantities.rs` (141 lines),
`resumption_closure_capture.rs` (113), `tail_resumption_acceptance.rs` (198).
Exact Rust cases absorbed: the pure effect heads
`effect Carry { [0,1] take() -> i64 }`, `[1,1]`, `[2,2]`,
`effect Gate { left() -> ! right() -> ! }`, `effect Gate { stop() -> ! [1,1] inspect() -> i64 }`,
`effect Pick { [2,2] choose() -> i64 }`, `effect Stop { [0,1] stop() -> i64 }`,
`effect Ask { [1,1] ask() -> i64 }`, `effect Maybe { [0,1] ask() -> i64 }`,
`effect Replay { [2,2] replay() -> i64 }`.
Self-host files: `self-host/src/frontend/headers/*.glorious` (effect header parse +
resumption quantity normalization), `self-host/src/probe/{probe,headers}/**` and the
typed-core effect probe built by `self_host_effect_bundle()`.
Probe shape: `self_host_typed_core.rs#self_hosted_effect_control_headers_match_rust_oracle`
runs `:effect_interface_bytes` in the VM; each `(source, accepted)` row must match
`lex -> parser::parse -> validate::validate` of the Rust oracle AND the self-host
probe's status byte.
Result in this commit: three suites moved `unported -> partial`, corpora extended.

### P2 — mixed_lifetime_nominals (types_traits_generics, 105 lines)
Exact Rust cases: `struct Brand<'a, T> { value: T } pass<'scope, U>(value: Brand<'scope, U>) -> Brand<'scope, U>`
and the ill-kinded/ill-arity/unbound-region rejections
`Brand<i64, 'scope>`, `Brand<i64>`, `Brand<'missing, i64>`.
Self-host files: `frontend/headers/headers.glorious` (mixed nominal application args +
binder-kind/arity span diagnostics), `frontend/elaboration/*.glorious` (binder-kind +
arity + region-scope validation), probe `probe/headers/headers.glorious`.
Probe shape: reuse `self_host_headers.rs#self_host_header_mixed_nominal_arguments_match_bootstrap`
for the accept case; extend `self_host_semantic_control.rs` accept/reject rows with the
three rejection sources so `compile_source_to_phases` acceptance matches. The rejection
arm needs the self-host elaboration to classify binder kind / arity / unbound region
the same way; that is the frontier work.

### P3 — hrtb_universes (types_traits_generics, 164 lines)
Exact Rust cases: `impl Universal for Witness where for<T, 'a> Text: Every<T, 'a> {}`,
`impl Universal for Witness where for<const N: u32> Text: Every<N> {}`,
`impl Universal for Witness where for<r: EffectRow> Carrier: Capability<Effects<r> = {Ask | r}> {}`.
Self-host files: `frontend/headers/headers.glorious` (higher-ranked `for<...>` binders in
where goals, including const and effect-row binder kinds and associated GAT bindings),
`frontend/elaboration/*.glorious` (rigid binder handling).
Probe shape: two layers — header parity via
`self_host_headers.rs#self_host_header_higher_ranked_binders_match_bootstrap` and
`#self_host_header_generic_where_effect_rows_match_bootstrap` for `for<T,'a>`/effect-row
binders; const HRT binders need a span-parity row (currently `encode_where_contract`
early-returns on `Const` binder — see P5 note).

### P4 — const_nominals (types_traits_generics, 527 lines)
Exact Rust cases (header/interface slice): `struct Unsupported<const N: u32> { value: u8 }`,
`enum ConstEnum<const N: u32> { One }`, `const_generic<const Q: Quantity>()`, plus `impl`/
`Drop`/`Use` heads with const params.
Self-host files: `frontend/headers/headers.glorious` (const generic parameters — recently
landed for structural_consts), `frontend/elaboration/*.glorious` (const numeric type
checking), `probe/headers/headers.glorious`.
Probe shape: `self_host_interfaces.rs#self_hosted_interfaces_match_rust_in_vm_and_native_execution`
already carries const-nominal rows in its corpus; extend with the remaining
`const_nominals` nominal heads + where-const binder support (a real gap).

### P5 — generic_alias_shadowing (types_traits_generics, 23 lines)
Exact Rust case: `type A = Text; type E = Text; type F = Text;`
`choose<A, E, F>(answer: A, evidence: E, fallback: F) -> A { evidence; fallback; answer }`.
Self-host files: `frontend/resolution/resolution.glorious` (generic binder shadowing of
global type aliases), `probe/resolution/resolution.glorious`.
Probe shape: `self_host_name_resolution.rs#self_host_resolution_generic_binders_shadow_global_aliases`
already resolves `choose<A,E,F>` (with an added effect-row binder `R`). Completion = assert
the exact suite source's binder/shadwed-alias resolution and the acceptance of `answer()
-> i64 { choose(42, "evidence", ()) }` (needs body/type inference, which the probe does not
currently exercise) so full `covered` requires the typed-core call the probe already emits.

## 4. Why these five are smallest/high-leverage
- All five are in the two most frontend-amenable families (`effects_control`,
  `types_traits_generics`), where the mature header/interface/typed-core/resolution
  gates already exist, so effort is concentrated in `(source, accepted)` rows and
  small header/elaboration additions rather than backend/MIR/VM work.
- Excluded families (standard_library 23, ownership_lifetimes 13, compiler_pipeline 18,
  backend_runtime, mir_lowering, optimization_specialization) are dominated by runtime,
  MIR, borrow-checking or optimizer behavior that the self-host backend does not yet
  lower end-to-end (the compiler-pipeline gate is still baseline-blocked); they are not
  "small" ports today.

## 5. Known blockers (evidence)
- The full self-host compiler pipeline gate
  `self_hosted_compiler_pipeline_accept_reject_matches_rust_in_vm` remains
  `#[ignore = "baseline-blocked"]`: the RAM limiter cannot build the whole
  `self-host/src/{frontend,backend,compiler,diagnostics}` bundle green yet. Until it
  unblocks, pure accept/reject ports of compiler_pipeline suites cannot be `covered`.
- HRTB const binders and associated-GAT bindings (`for<const N>`, `Effects<r> = {..}`)
  are not yet span-parity-encoded by the self-host headers oracle; those rows stay
  header-level semantics rather than byte parity until the encoder is extended.
- Runtime/optimizer/borrow suites need the self-host backend (lowering/emission) which is
  present but not green end-to-end; they are out of the "small port" set.

## 6. How to validate
Run the focused gates under the repository memory limiter (once a RAM slot admits):
  /tmp/grandiose-ram-gate.sh test -p grandiose --test self_host_typed_core self_hosted_effect_control_headers_match_rust_oracle
  /tmp/grandiose-ram-gate.sh test -p grandiose --test parity_manifest
Each newly-touched `.glorious` source is already proven accepted by the existing corpus of
the same gate, so the additions are parity-consistent with the current self-host layer.
