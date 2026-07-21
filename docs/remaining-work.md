# Remaining implementation work

This is the open implementation backlog for the Rust Grandiose compiler and G1
VM. Completed work is intentionally omitted. The legacy LLVM compiler, eventual
wholesale port into Grandiose, and self-hosting convergence are excluded from
current compiler-completion percentages and are tracked separately below.

## Current gates

Focused compiler, VM, optimizer, ownership, generic, handler, standard-library,
formatter, LSP, and `grand` suites cover the implemented slices. Before the next
release checkpoint, rerun formatting, strict workspace Clippy, all root and
tooling-workspace tests, and hostile-artifact suites together. Any remaining
failure must be reconciled as either a regression or an explicitly updated
diagnostic expectation; no known failure is considered completed work.

## Active hardest tranche

These are the hardest currently active implementation tasks, in dependency
order. Remove an item when its production behavior, adversarial tests, and
relevant strict gates are complete; then promote the next hardest remaining
item from the backlog.

1. Complete the optimizer backlog after semantic breadth: cleanup/effect
   specialization, CFG cloning, tail formation, scalar replacement, GVN,
   register reuse, and related backend optimization infrastructure.

## 3. Effects, handlers, and resumptions

### 3.3 Handler optimizer specialization

- static-handler specialization beyond the implemented direct and one-hop
  forwarded terminal fusion and canonical single-performance one-shot
  resume/cancel composition: deeper forwarding graphs, branching or repeated
  performances, captured continuations, and multishot/deep-reinstating cases.

## 4. Generics, traits, and lifetimes

### 4.2 Higher-ranked generics and universes

- higher-ranked const and effect binders where permitted;
- higher-ranked outlives constraints;
- deeper nested-universe substitution beyond current trait, callable-marker,
  and associated-equality evidence paths.

### 4.3 Const generics

- const-generic aliases;
- const expressions, arithmetic, and defaults;
- layout-level const consumers such as arrays rather than phantom identity;
- non-`u32`/`Quantity` kinds if G1 intends any.

## 5. MIR and bytecode backend

### 5.1 MIR infrastructure

- extend the implemented typed `BlockId`/block-kind checked editor and
  transactional block tombstones to persistent typed arenas for locals,
  operations, places, move paths, scopes, and control sites;
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
  public-`LEAVE` boundaries, now consumes the single MIR ownership source and
  is independently checked by the VM verifier.

### 5.4 Bytecode peepholes and validation

- move-chain collapse beyond straight-line independent transfer snapshots
  (target-safe NOP/fallthrough-jump removal, non-entry transfer-temporary
  `Move`/`Copy` chains across independent parallel snapshots, and direct
  selection without empty switch-transfer blocks are implemented);
- redundant `EndBorrow` removal and constant-pool-aware rewrites beyond the
  implemented target-safe retargeting of one-use constant transfer temporaries;
- cleanup/label/handler-safe repatching;
## 6. Optimizer

### 6.1 CFG and sparse simplification

- general, Copy, cyclic, and loop-aware phi simplification;
- scope/cleanup-aware forwarding and special control parameters;
- integer ranges and aggregate constants;
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

## 8. Standard library

### 8.1 Scalars and fundamental traits

- exact runtime parsing of the generation-1 decimal float grammar;
- complete the fundamental trait surface for `Option`, `Result`, and tuples;
  close the remaining symbolic/provisional receiver-typing path for bounded
  `Eq`, `Ord`, `Hash`, `Default`, `Display`, and `Debug` calls inside those
  generic implementations (recovery execution is covered);

### 8.2 Result, Option, ranges, and helpers

- deliberately trapping conveniences if desired;
- assertions, `assert_eq`, `unreachable`, abort wrappers, and an
  ownership-aware `Slot<T>` if retained.

### 8.3 Text, bytes, and formatting

- byte/character/index iteration and view hashing;
- escaped output beyond the implemented String `Debug` escapes and arbitrary
  formatting values;
- hex formatting and complete `Display`/`Debug` integration (signed and
  unsigned decimal formatting through 128 bits is implemented);
- ordinary `format` callable;
- `SourceMap`, line tables, labels, severities, notes, and a deterministic
  source-defined diagnostic renderer.

### 8.4 Collections and algorithms

- Vec split/drain APIs, additional iterator forms, restricted-element
  abandonment tests, and unified-PlaceFlow validation;
- extend the implemented private generic `HashMap`/`HashSet` core (deterministic
  open addressing, growth, capacity budgets, insertion/replacement, lookup,
  membership, bounded collision-cluster-repair removal, length/capacity/empty
  queries, `get_mut`, one-probe occupied/vacant entry insertion, deterministic
  exhaustive owning iteration, borrowed iterator representations, O0--O3 VM
  execution, and recovery parity) with reference-returning insert-or-get and
  borrowed-consumer specialization breadth, checked raw-entry probing,
  `remove_entry`/general reserve and clear, and set union/intersection APIs;

### 8.5 Compiler toolkit

- Ordinary source now implements private, checked `Id<Tag>`, `IndexVec`, the
  rollback-capable `Arena`, machine-word `BitSet`, `SparseSet`, a deduplicating
  FIFO `WorkQueue`, arbitrary-key hash-backed `MultiMap<K,V>`, and line/column
  `SourceMap`. Their
  storage, rollback, set-algebra, queue, grouping, capacity, O0--O3 VM, and
  recovery paths have focused coverage. The remaining collection-dependent
  part is an optional borrowed-key raw-entry optimization for `MultiMap`.
  `Interner<T>` is fully generic and hash-backed,
  stores each canonical value once, preserves insertion-order IDs, and checks
  equality within deterministic hash buckets; String and colliding non-String
  heads have O0--O3/recovery coverage.
- Checked counters, monotonic logical `StepBudget`s, and stable-field-order,
  timer-free compiler statistics records are implemented and tested for atomic
  overflow/limit rejection.

## 9. Compiler CLI and tooling

### 9.2 Formatter and LSP

- extend the implemented persistent per-workspace-root document session (root
  transactions, compiler-check diagnostics, and atomic last-good declaration /
  definition snapshots are implemented) with per-body incremental elaboration
  and retained transactional inference arenas;
- add compiler-exported span-to-type and fully resolved local-definition side
  tables (stable top-level identities, exact declaration/name spans, and
  last-good top-level definition tables are implemented);
- extend the authoritative compiler-interface-backed symbols, cross-file
  definition, completion, references, rename, hover signatures/docs, and full
  compiler diagnostics with inferred-type hover, hints, and dependency
  navigation; authoritative callable signature help and semantic tokens for
  compiler-bound declarations/occurrences plus compiler-lexed source classes
  are implemented with UTF-16, multi-file, and transactional last-good
  coverage. Replace the remaining lexical local-scope fallback once compiler
  local-definition tables exist.

## 10. Testing and release hardening

- coverage-guided hostile decoder/verifier/VM fuzz targets and broader runtime
  OOM corpora (deterministic full-loader truncation, byte/field mutation,
  fixed-seed arbitrary-input, small-input allocation-amplification, hostile
  array-length, sparse extreme label namespaces, and supervised
  allocation-limit corpora are implemented);
- determinism tests for optimizer caches/maps, statistics, and fingerprints;
- resource-limit diagnostics and pass budget/fixed-point remarks;
- self-compilation performance gate below 120 seconds and 4 GiB;
- refresh stale documentation that describes completed work as missing.

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

- modules/import/package syntax inside the language;
- FFI, unsafe Grandiose, reflection, macros, or derive;
- threads, async executor, networking, or garbage collection;
- shared mutable reference counting, tree maps, regex, locale/date/time,
  arbitrary-precision integers, general serialization, runtime dependency
  discovery;
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
- associated type defaults, qualified module paths, and open effect-row aliases
  unless explicitly added to product scope.

## 13. Recommended dependency order

1. Finish frontend PlaceFlow consolidation, move-path restoration, nested unique
   projections, and generic borrowing/reference transport.
2. Complete dynamic effect/capture/provenance summaries and handler/outward
   effect breadth.
3. Complete inferred and projection-based trait-method selection,
   higher-ranked/effect-row generics, aliases, and blanket/intrinsic evidence.
4. Add checked MIR mutation, reusable analyses, register allocation, block
   layout, direct cleanup serialization, and bytecode-input validation.
5. Complete nonlocal optimizer breadth: cleanup, scalar replacement, callable
   and effect specialization, multi-block inlining, tail formation, and LICM.
6. Finish continuation/effect-summary compaction.
7. Complete the source standard library/toolkit, canonical CLI/build flow,
   semantic tooling, editor distribution, and multi-workspace CI.
8. Perform the separately tracked wholesale port and stage convergence.
