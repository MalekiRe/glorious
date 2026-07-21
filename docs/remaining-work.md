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

## Active top-five tranche

These are the five hardest currently active implementation tasks, in dependency
order. Remove an item when its production behavior, adversarial tests, and
relevant strict gates are complete; then promote the next hardest remaining
item from the backlog.

### Effects completion gate

Do not remove this gate until all four production paths and their hostile,
O0-O3, VM, formatting, and strict-Clippy gates are complete:

1. bounded recursive/SCC effect reference-origin summaries;
2. closure-origin joins across resume and handler exits;
3. late recursive generic resumption environments;
4. owned cyclic receiver and runtime ownership support.

1. Complete richer closure reference-origin relations across resume and
   handler exits. Exact direct/indirect calls, statically divergent arms,
   non-root aggregate paths, generic effect payload/result routing, bounded
   recursive SCCs, and equal-effect multi-arm joins are implemented; dynamic,
   opaque, or ambiguous selection remains fail closed.
2. Support higher-order lifetime substitution through executable callback
   control-flow joins, opaque calls, recursive or multiple wrapper edges,
   nominal projections, and a general symbolic lifetime environment.
3. Extend cleanup-aware optimizer specialization: direct resume/cancel edges,
   identity-safe CFG cloning, and richer tail formation.
4. Complete general first-class callable breadth: escaping reference-bearing
   environments; effectful, reference-signature, inferred, multi-callable, or
   non-transparent runtime fallback; and late recursive generic
   callable/resumption combinations.
5. Complete handler result inference and nesting across normal completion,
   clause joins, capture/lowering contexts, and forwarded optimizer paths.

## 1. Source-language surface

### 1.1 First-class callables

- repeatable shared-reference environments and uniquely borrowed environments
  with explicit per-callable reborrow ownership;
- effectful, reference-signature, inferred, multi-callable, and
  non-transparent runtime callable fallback;
- broader late recursive generic callable/resumption combinations;
- identity-observation rules if callable equality or reflection is added.

### 1.2 Patterns and enum places

- variant-payload `..` remainder and omission;
- unreachable pattern-row warnings.

### 1.3 Literals

- source integer literals wider than the current signed `i64` token payload;
- contextual `u64`/`u128` selection without eager narrowing;
- exact source-level IEEE float parsing and rounding verification.

## 3. Effects, handlers, and resumptions

### 3.2 Reference payload/result breadth

- richer closure origin relations across resume and handler-result joins.

### 3.3 Handler optimizer specialization

- partial and forwarded handlers in optimizer specialization.

### 3.4 Resumption closure and quantity breadth

- late recursive generic resumption combinations;
- reference-bearing escaping environments;

Every finite bounded `u32` resumption interval is supported. Unbounded
resumptions still require generalized runtime representation, use tracking,
copy-glue policy, and verifier summaries; absent that decision, they remain a
deliberate G1 limitation with a structured source diagnostic.

## 4. Generics, traits, and lifetimes

### 4.1 Trait methods

- dot-call lookup and inferred trait selection;
- receiver access-mode inference beyond the explicit receiver parameter type;
- improved method-call diagnostics;
- associated method values if required.

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

### 4.6 Generic callable evidence

- ordinary trait-method evidence and associated projections in callable
  signatures;
- structural `else` specialization when a generic call returns `Result` or
  `Option`;
- full lifetime/const/effect parameter environments;
- recursive specialization with a general finite-growth proof;
- removal of bounded-discovery restrictions for deeply nested generic
  callable/resumption combinations.

### 4.7 Generic borrowing and references

- executable callback control-flow joins, opaque calls, recursive or multiple
  wrapper edges, nominal projections, and general symbolic lifetime
  environments;

### 4.8 General generic `Use`, `Drop`, aliases, and nominal shapes

- noncanonical coherent generic heads and broader where subjects/arguments;
- associated-equality conditions and grounded specialization discovery;
- generic hook calls outside the current fixed-point slice;
- clearer failure-to-ground diagnostics;
- complex generic alias constructor arguments and aliases in effect signatures;
- symbolic normalization before grounding;
- field/payload shapes beyond the finite supported grammar;
- general finite recursion proofs and binder substitution in alias impl heads.

## 5. MIR and bytecode backend

### 5.1 MIR infrastructure

- typed block kinds and tombstoned arena mutation;
- checked CFG mutation rather than direct vector edits and blanket
  invalidation;
- missing/reusable analysis bundles: predecessor/RPO/loop infrastructure,
  edge liveness, place versions, alias sets, integer ranges, aggregate facts,
  shared costs, and general interprocedural widening;
- block, operation, local, move-path, scope, and control-site resource limits
  with structured diagnostics and optimizer-budget remarks.

### 5.2 Register allocation and block layout

- live intervals and owned/shared/unique register classes;
- register reuse, including after loan end and across compatible types;
- addressable-place allocation and minimal parallel-copy cycle breaking;
- erased/ZST register elimination;
- explicit normal, cleanup, handler, resumption, and label block regions;
- lexical control-aware layout and stable cleanup interval boundaries.

### 5.3 Instruction selection and cleanup maps

- abort, binding packs, `Available` evidence, and complete erased-ZST
  selection;
- serialize MIR-derived cleanup lists directly, including edge-transfer
  temporaries;
- infer arbitrary public `LEAVE` boundaries without compiler-seeded lexical
  facts.

### 5.4 Bytecode peepholes and validation

- NOP removal, move-chain collapse, and empty transfer-block removal;
- redundant `EndBorrow` removal and constant-pool-aware rewrites;
- cleanup/label/handler-safe repatching;
- a distinct `ValidateBytecodeInput` checkpoint;
- optimized-MIR validation against cleanup/drop facts before serialization;
- accurate backend pass reporting.

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

- general static-handler removal and partial handlers;
- residual, conditional, or custom-`Drop` abandoned-continuation cleanup
  (computed scalar, fresh owned aggregate, shared-reference and transferred
  unique-reference payloads, plus ordered whole-owner cleanup are
  specialized; abandoned unique loans remain a barrier);
- one-shot allocation elimination and direct resume/cancel edges;
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

## 7. VM, verifier, and artifact hardening

### 7.1 Compact verified artifact

- decode borrowed strings/blobs directly from an owned byte container;
- an encoded/verified loader that can release raw sections without first
  materializing the mutable public `Artifact`;
- a denser execution-only opcode/operand layout;
- checked IDs for constants, types, imports, protocols, and handler definitions;
- leader-only runtime facts if supervision/JIT work needs them;
- separate the compatibility `artifact()` view from execution.

### 7.2 Continuation and effect summaries

- cancellation-only sparse plans where earlier destruction is observably safe;
- further compact sparse register sets for very large frames;
- dynamic array-slot summaries and precise maybe-cancel/maybe-multishot facts;
- non-pristine effect-payload quantity provenance beyond exact sole-owner
  `perform`, nested forwarding, and terminal clause consume/return
  dispositions;
- general effectful quantity transport beyond converged finite callable SCCs.

### 7.3 Supervisor portability

- non-Unix/Linux adapters or narrower portability claims;
- reliable OOM/memory-limit classification distinct from internal signals;
- platform-specific process-group cleanup tests.

## 8. Standard library

### 8.1 Scalars and fundamental traits

- integer-negation wrappers and numeric `min`, `max`, `clamp`;
- float arithmetic, comparison, conversion, parsing, and formatting;
- character validation, `char`/`u32` conversion, and UTF-8 length/codec APIs;
- integer parsing for every source base and broader numeric diagnostics;
- `Ordering`, `Eq`, `Ord`, `Hash`, `Default`, `Display`, and `Debug`, including
  scalar, String, Bytes, Option, Result, and tuple implementations.

### 8.2 Result, Option, ranges, and helpers

- borrowing projections for `Result` and `Option`;
- deliberately trapping conveniences if desired;
- `take` after `Default`, assertions, `assert_eq`, `unreachable`, abort
  wrappers, and an ownership-aware `Slot<T>` if retained.

### 8.3 Text, bytes, and formatting

- byte/character/index iteration and view hashing;
- `StringBuilder::append_char`, escaped output, and arbitrary values;
- decimal/hex formatting and `Display`/`Debug` integration;
- ordinary `format` callable;
- `SourceMap`, line tables, labels, severities, notes, and a deterministic
  source-defined diagnostic renderer.

### 8.4 Collections and algorithms

- Vec split/drain APIs, additional iterator forms, restricted-element
  abandonment tests, and unified-PlaceFlow validation;
- `HashMap`/`HashSet` with deterministic open addressing, growth, budgets,
  replacement/removal/entry/iteration APIs, and interner probing;
- bounded introsort, heapsort fallback, stable merge sort, binary search,
  bounds, partition, deduplication, lexicographic comparison, and adversarial
  complexity tests.

### 8.5 Compiler toolkit

- `Id<Tag>`, `IndexVec`, rollback-capable `Arena`, `Interner`, `BitSet`,
  `SparseSet`, `WorkQueue`, `MultiMap`, and `SourceMap`;
- checked counters, logical budgets, and deterministic statistics records.

### 8.6 Library size

Decide whether to compact/generate repetitive APIs, express them generically,
or revise the documented 1,500–2,500 nonblank-line target. The generated
checked integer-conversion matrix is the main source of excess size.

## 9. Compiler CLI and tooling

### 9.1 Canonical compiler/build contract

- real `grc`: capabilities, multiple inputs, canonical ordering, O0–O3,
  MIR/bytecode and phase output, JSON diagnostics/interfaces, std interface,
  output/version negotiation, and long-lived sessions;
- migrate `grand` from legacy/fake flows to `.glorious`/`.grbc`, `grvm`, atomic
  toolchain identities, authoritative interfaces, real check-only diagnostics,
  end-to-end tests, and compatibility enforcement.

### 9.2 Formatter and LSP

- shared lossless frontend/trivia rather than duplicated/private lexers;
- AST/document-algebra formatting with fixity context, width grouping,
  structured wrapping, safe normalizations, invalid-input refusal, and corpus
  equivalence tests;
- persistent incremental compiler sessions and transactional inference;
- definition/type side tables and last-good semantics;
- semantic hover, navigation, rename, signature help, completion, hints,
  tokens, ranges, symbols, cancellation, multi-root handling, dependency
  navigation, and full compiler diagnostics.

### 9.3 Editor distribution and tooling CI

- canonical `.glorious` recognition, updated grammar, packaged VS Code/LSP
  distribution, other-editor documentation, and release automation;
- CI for root, `grand`, formatter, and LSP workspaces;
- formatter corpus tests, LSP UTF-16/cancellation fuzzing, resolver
  hermetic/security tests, compiler-contract integration, and extension
  packaging tests.

## 10. Testing and release hardening

- checked MIR builder and ownership-valid MIR generator;
- MIR mutation fuzzing and per-pass differential VM testing;
- trace equality for effects, resume, cancel, leave, host calls, and custom drop;
- hostile decoder/verifier/VM fuzz targets and allocation-amplification/OOM
  corpora;
- golden `.grbc` and released-seed compatibility fixtures;
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
6. Finish compact loading, checked artifact IDs, supervisor portability, and
   hostile-input hardening.
7. Complete the source standard library/toolkit, canonical CLI/build flow,
   semantic tooling, editor distribution, and multi-workspace CI.
8. Perform the separately tracked wholesale port and stage convergence.
