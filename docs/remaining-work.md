# Remaining implementation work

This is the open implementation backlog for the Rust Grandiose compiler and G1
VM. Completed work is intentionally omitted. The eventual wholesale port into
Grandiose and self-hosting convergence are excluded from current
compiler-completion percentages and are tracked separately below.

Further VM hardening is out of the active product scope. Optimizer breadth is
retained below but scheduled after the core language and tooling tranche.

## 3. Effects, handlers, and resumptions

### 3.3 Handler optimizer specialization

- static-handler specialization beyond the implemented direct and one-hop
  forwarded terminal fusion, canonical single-performance one-shot
  resume/cancel composition, replay-safe pure-residual finite multi-shot
  cloning, and arbitrary-depth direct exact-one-shot handler nesting with
  refutable frame forwarding: branching or repeated performances, captured
  continuations, and dynamic multishot/deep-reinstating cases.

## 5. MIR and bytecode backend

### 5.1 MIR infrastructure

- extend the implemented typed `BlockId`/block-kind and `MirOperationId`
  checked editors, transactional block/operation tombstones, persistent
  local/place arenas, and frozen typed control-site tables (labels, handlers,
  performances, and resumptions) to executable source-storage statements and
  frontend-emitted drop flags; frozen bodies now publish typed move-path/
  binding and source-storage scope/lifecycle tables, the full lexical
  label/handler scope tree, and scope-aware handler candidates;
- migrate the remaining edge redirection, block splitting/merging, operand,
  and terminator replacement paths through the checked editor (NormalizeCfg
  unreachable deletion and same-block scalar-`Move` removal are checked and
  invalidate only the analyses they affect);
- extend the implemented deterministic checked predecessor, reachability/RPO,
  dominator, natural-loop/preheader, irreducible-SCC, and edge-liveness bundles
  with place versions, alias sets, integer ranges, aggregate facts, shared
  costs, lazy caching, and general interprocedural widening;
- optimizer-budget remarks and resource limits for the remaining control-site
  categories (block, operation, local, move-path, scope, label, and handler
  limits now fail structurally before optimization).

### 5.2 Register allocation and block layout

- extend the implemented deterministic exact-type, same-block physical reuse
  after proven emptying/loan end to compatible-representation and general
  cross-block coloring once distinct type/drop-glue identities can be proved
  interchangeable;
- use the implemented addressable-place classification for one-to-one place
  allocation and minimal parallel-copy cycle breaking;
- erased/ZST register elimination;
- extend the implemented typed entry/RPO-normal, label, cleanup, handler, and
  resumption grouping through whole successor regions, lexical nesting, and
  stable cleanup interval boundaries.

### 5.3 Instruction selection and cleanup maps

- standalone erased-ZST local/parameter elimination (`Available` fields are
  erased consistently from MIR ownership and VM aggregate/binding-pack
  payload layouts; direct MIR abort selection/no-cleanup semantics and
  binding-pack construction, ownership, reference-origin transport, and frozen
  bytecode selection are implemented). Direct final cleanup serialization,
  including parallel edge-transfer temporaries and arbitrary MIR-derived
  public-`LEAVE` boundaries, now consumes numeric MIR move-path and binding
  identities (with root text retained only for diagnostics) and is
  independently checked by the VM verifier.
- source-storage lifecycle and cleanup-action conformance: frozen MIR still
  lacks executable `StorageLive`/`StorageDead`, per-local storage kind and
  initialization state, compiler-created drop-flag transitions, and ordered
  `EndBorrow`/`Destroy`/`StorageDead` cleanup actions with protected payloads.
  The enabled red forged-MIR matrix covers uninitialized reads,
  unique-loan invalidation, path-dependent initialization at joins, and cleanup
  disarming protected `Leave` payloads. The composite witnesses additionally
  cover nested lexical exits, reverse destruction, loan-before-storage ordering,
  branch-correlated drop-flag transitions, and VM erasure proof.
  `storage_statement_contract.rs` closes the remaining program-point audit:
  store-before-live, reuse after transfer/death, and replacement without a
  zero-use `Destroy` must all fail at MIR validation; its all-false branch
  fixture proves that a `DestroyIf` skip path erases to `StorageDead` without
  inventing a destroy or touching a protected payload. Completing this slice
  requires executable statements to turn those contracts green, including
  direct dead-with-live-loan, wrong drop-flag transitions, and cleanup plans
  that omit or reorder required actions. VM lowering must either execute the
  verified action sequence or prove its compact erasure preserves both true and
  false flag arms exactly; a candidate artifact must be rejected unless its
  decode-time witness is derived from validated MIR rather than a register
  cleanup shape alone. Source-driven red coverage in
  `source_storage_lowering.rs` additionally requires the contract to survive
  parameter shadowing, partial moves, handler payload/resumption and completion
  binders, captured closures, and nonlocal `Leave` exits; current lowering has
  no completion-form MIR path for the composite fixture and does not map
  handler payload/resumption storage to executable locals in lifted closures.

### 5.4 Bytecode peepholes and validation

- move-chain collapse beyond straight-line independent transfer snapshots
  (target-safe NOP/fallthrough-jump removal, identity edge-transfer omission,
  non-entry transfer-temporary `Move`/`Copy` chains across independent
  parallel snapshots, and direct selection without empty switch-transfer
  blocks are implemented);
- redundant `EndBorrow` removal and constant-pool-aware rewrites beyond the
  implemented target-safe retargeting of one-use constant transfer temporaries;
- cleanup/label/handler-safe repatching;
## 6. Optimizer

### 6.1 CFG and sparse simplification

- general, Copy, cyclic, and loop-aware phi simplification;
- scope/cleanup-aware forwarding and special control parameters;
- integer ranges and aggregate constants beyond the implemented scalar
  arithmetic, comparison, boolean, and typed-edge constant facts;
- broader projection/construction folding and Copy propagation;
- load/store forwarding with place/alias kills;
- storage-liveness rules and richer cross-block forwarding.

### 6.2 Scalar replacement and cleanup

- enum, cross-block, nested, and partially moved aggregates;
- loan-aware scalar replacement and custom-`Drop` materialization;
- cleanup-aware reverse destruction, profitability, and escape analysis;
- branch-correlated drop flags across joins/loops;
- constant `DestroyIf` folding for nonempty owners;
- removal of fully moved shells outside all-false residual plans;
- parameterized/canonical cleanup blocks and protected-result cleanup;
- custom-versus-structural drop costs.

### 6.3 Loan-proof erasure, GVN, and callable scalarization

- cross-block ended loans and runtime-versus-proof-only classification;
- reference scalarization, ZST evidence removal, and register reuse;
- place-versioned loads/stores, ranges, aggregate facts, and
  alias/effect-aware GVN preservation;
- guarded multi-target and exact-indirect-call specialization;
- capture shrinking, receiver scalarization, escaping-call analysis, recursive
  callable clones, custom capture shells, and environment lifetime/brand/drop
  preservation.

### 6.4 Effect/resumption specialization

- general static-handler removal beyond implemented direct/one-hop-forwarded
  terminal fusion and canonical one-shot resume/cancel composition (selected
  operation groups and known partial-handler hits specialize; unmatched partial
  fallback remains dynamic);
- residual, conditional, or custom-`Drop` abandoned-continuation cleanup
  (computed scalar, fresh owned aggregate, shared-reference and transferred
  unique-reference payloads, plus ordered whole-owner cleanup are
  specialized; abandoned unique loans remain a barrier);
- one-shot allocation elimination and direct resume/cancel edges beyond the
  implemented canonical single-performance composition;
- deep reinstatement proofs, multishot copy-glue sharing, and resumption escape
  analysis.

### 6.5 Inlining, tail formation, and LICM breadth

- multi-block CFG cloning with fresh scopes, labels, loans, move paths, control
  sites, cleanup plans, and source identities (cleanup-free block identities
  are fresh and checked against ID-space exhaustion);
- cleanup-edge substitution and broader always-inline cases;
- controlled recursive specialization if permitted;
- tail formation through richer cleanup CFG and protected moved arguments;
- tail handling for aggregates, loans, environments, handlers, resumptions;
- LICM for safe loads and richer aggregate/value facts;
- loop normalization without a unique preheader;
- more precise trap, alias, range, and trip-count proofs.

## 10. Testing and release hardening

- coverage-guided hostile decoder/verifier/VM fuzz targets and broader runtime
  OOM corpora (deterministic full-loader truncation, byte/field mutation,
  fixed-seed arbitrary-input, small-input allocation-amplification, hostile
  array-length, sparse extreme label namespaces, and supervised
  allocation-limit corpora are implemented);
- determinism tests for optimizer caches/maps, statistics, and fingerprints;
- resource-limit diagnostics and pass budget/fixed-point remarks.

## 11. Port and self-hosting tracked separately

These are not included in current compiler-completion percentages:

- freeze the completed Rust compiler behavior and port it wholesale;
- replace Rust-only collection dependencies with the source library;
- package canonical `std-lib.glorious` and emit verified compiler `.grbc`;
- produce the first checked-in seed and run stage 1 through stage 3;
- require stage-2/stage-3 byte identity and released-seed compatibility;
- meet the 120-second and 4-GiB self-compilation gate.

## 12. Deliberate G1 exclusions

These are not part of the completion backlog:

- package-manager syntax inside the language (source modules/imports are in scope);
- FFI, unsafe Grandiose, reflection, macros, or derive;
- threads, async executor, networking, or garbage collection;
- shared mutable reference counting, tree maps, regex, locale/date/time,
  arbitrary-precision integers, general serialization, runtime dependency
  discovery;
- borrowed-key raw-entry optimization for `MultiMap` (the deterministic
  arbitrary-key implementation is complete without this performance-only
  specialization);
- compiler-known `if`, `match`, `loop`, or operator semantics;
- unbounded resumption quantities without a generalized runtime
  representation, use tracking, copy-glue policy, and verifier summaries;
- pattern guards, ranges, OR patterns, and user-overloadable pattern protocols;
- borrowed indirect tail-call receivers;
- memoized globals whose value has a restricted `Use` interval;
- host-created or otherwise opaque callable/handler implementations outside
  the artifact's VM-sealed finite producer set (empty or noncanonical producer
  sets fail closed rather than trusting user-authored summary claims);
- unique references across multishot capture, custom-`Drop` values in multishot
  snapshots, cancellation of exact-positive resumptions, resumption use outside
  a handler, and outward-row mismatches;
- optimizer transformations that weaken traps, `Use`, cleanup, or custom-`Drop`;
- O3 legality rules different from O2;
- associated type defaults and open effect-row aliases unless explicitly added
  to product scope.
