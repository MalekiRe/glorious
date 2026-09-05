# Grandiose Stage0 → Feature-Complete Self-Hosted Compiler Translation Plan

Historical plan, superseded by [GSC-2](../GSC-2-glorious-incremental-self-hosted-compiler-spec.md).
The old implementation and all progress/coverage claims below are retired.

**Repository:** [`MalekiRe/glorious`](https://github.com/MalekiRe/glorious)
**Current required Stage0 baseline:** [`cfeab4b58d60754a70c819fdda25a1f1024907af`](https://github.com/MalekiRe/glorious/commit/cfeab4b58d60754a70c819fdda25a1f1024907af)
**Historical analysis baseline:** [`02ced7ed1894acfd54b0766e2d718b699fc31a8c`](https://github.com/MalekiRe/glorious/commit/02ced7ed1894acfd54b0766e2d718b699fc31a8c)
**Historical self-host prototype used as a postmortem:** [`a62a08316f5b0c81f74c2a975fe7bd9826157a90`](https://github.com/MalekiRe/glorious/commit/a62a08316f5b0c81f74c2a975fe7bd9826157a90)
**Analysis date:** 2026-08-20
**Status:** Revised implementation plan. This version supersedes the earlier reduced-scope proposal.

> **Central recommendation**
>
> Translate the Rust stage0 **module by module**, preserving the complete observable behavior of every stage0 module and every exported compiler mode before the first self-hosted compiler artifact is accepted. The target may be much smaller internally, but only through better representations, generic engines, algebraic effects, source-defined control, manifest-bound primitives, and elimination of duplicated implementation machinery. No LOC reduction may come from narrowing the language, dropping query/revision/cache/service behavior, omitting the stage0 VM candidate/verification APIs, moving semantic work into a Rust fallback, or postponing a stage0 feature until after bootstrap.

---

## Table of contents

1. [Executive summary](#1-executive-summary)
2. [Non-negotiable parity contract](#2-non-negotiable-parity-contract)
3. [Evidence base and repository state](#3-evidence-base-and-repository-state)
4. [Stage0 architecture analysis under a full-port constraint](#4-stage0-architecture-analysis-under-a-full-port-constraint)
5. [Lessons from the retired self-host prototype](#5-lessons-from-the-retired-self-host-prototype)
6. [Target architecture with mirrored module boundaries](#6-target-architecture-with-mirrored-module-boundaries)
7. [Module-by-module translation ledger](#7-module-by-module-translation-ledger)
8. [Using effects to reduce compiler code](#8-using-effects-to-reduce-compiler-code)
9. [Using source-defined control flow to reduce compiler code](#9-using-source-defined-control-flow-to-reduce-compiler-code)
10. [Using new primitive functions responsibly](#10-using-new-primitive-functions-responsibly)
11. [Feature-complete bootstrap standard-library profile](#11-feature-complete-bootstrap-standard-library-profile)
12. [Module-by-module execution plan](#12-module-by-module-execution-plan)
13. [Differential testing and parity program](#13-differential-testing-and-parity-program)
14. [Fixed-point bootstrap and release process](#14-fixed-point-bootstrap-and-release-process)
15. [LOC budget and cleverness-only reduction program](#15-loc-budget-and-cleverness-only-reduction-program)
16. [Performance and memory plan](#16-performance-and-memory-plan)
17. [Risk register](#17-risk-register)
18. [Recommended pull-request sequence](#18-recommended-pull-request-sequence)
19. [Immediate next actions](#19-immediate-next-actions)
20. [Appendices](#20-appendices)

# 1. Executive summary

This revised plan treats the existing Rust `grandiose-stage0` crate as a **frozen behavioral specification with 36 mandatory translation units**. The self-hosted compiler is not allowed to be a smaller-language bootstrap compiler, a compiler that only accepts its own source, or a compiler whose operational features are supplied by a Rust sidecar. It must be stage0-equivalent at the first point it is called a self-hosted compiler.

The governing rule is:

> **Mirror stage0 at module and behavior boundaries; compress only the implementation beneath those boundaries.**

The target source tree therefore retains Grandiose counterparts for:

- `artifact_cache`, `dependency`, `query`, and `revision`;
- `service`, `output`, `lib`, and `main`;
- the complete source frontend and static semantics;
- `PlaceFlow`, `UseFlow`, and `EscapeFlow` behavior;
- the current MIR model, editor, validation, optimization, cleanup, and storage contracts;
- runtime-manifest authority and all current primitive families;
- `vm_backend` candidate/verified program and artifact APIs, canonical encode/decode, verification, execution helpers, limits, and host interfaces;
- bootstrap manifest encoding, compatibility, lineage, and exact convergence checks.

The Rust `grandiose-vm` remains valuable, but its role changes from “the only verifier/runtime implementation” to **an independent second implementation and distribution trust anchor**. The Grandiose port still implements the stage0 `vm_backend` behavior because that behavior is part of stage0. The Rust VM separately verifies every emitted compiler and user artifact before execution and provides process supervision.

## 1.1 What “from the beginning” means

Development can proceed incrementally, but there is no reduced first product.

During translation:

1. Rust stage0 compiles each new Grandiose module and its test probes.
2. Completed Grandiose modules are tested against the corresponding Rust module.
3. An intermediate harness may combine Rust orchestration with Grandiose module probes for testing only.
4. No hybrid harness is published as `grc`, used as the bootstrap seed, or counted as a self-hosted compiler.
5. Stage 1 is attempted only after every required module has reached the module-complete gate.
6. The first checked-in self-hosted compiler artifact must expose the complete stage0 feature set and pass the complete parity matrix.

This interpretation avoids a semantic paradox: modules necessarily land one at a time, but the **first self-hosted compiler release** is feature-complete.

## 1.2 The full parity surface

Parity is broader than “accepts the same valid programs.” It includes:

| Surface | Required parity |
|---|---|
| Source language | Same accepted and rejected programs at the pinned baseline |
| Static semantics | Same types, effects, traits, quantities, ownership, borrowing, cleanup, and diagnostics |
| Compiler modes | `Check`, `Build`, `Test`, `Inspect`, `Ide`, and `Bootstrap` request behavior |
| Queries | Same typed query completeness, recovery policy, dependency recording, memoization, reuse decisions, cycle handling, cancellation, and resource failures |
| Revisions | Same immutable worlds, parent relationships, snapshot pins, retirement, package sessions, rollback, publication, and retention reporting |
| Caches | Same interface-cache, revision-cache, and persistent verified-artifact-cache acceptance/rejection rules and statistics |
| Diagnostics | Same stable codes/classes/severity/provenance, canonicalization, limits, text, and JSON projections |
| MIR | Same executable semantics and current edit/validation/optimization contracts |
| VM backend | Same candidate/verified split, type/instruction vocabulary, canonical bytes, hostile decode rejection, verification, limits, and execution behavior |
| Bootstrap | Same manifest schema, producer lineage, source/codegen fingerprints, artifact and byte commitments, compatibility checks, and stage convergence |
| CLI/service | Same commands, options, runtime-manifest selectors, atomic publication, output categories, and failure distinctions |

Internal Rust implementation traits such as `Send`, `Sync`, `Arc`, `Mutex`, and atomic instructions are not language/compiler features unless they are externally observable through the stage0 API or tests. The Grandiose implementation may use single-owner state and explicit mutation to provide the same externally visible lifecycle and concurrency-safe host behavior with much less code. A host that needs concurrent requests can run isolated compiler instances or serialize access to a compiler database without changing compiler semantics.

## 1.3 Module-by-module translation, not line-by-line transliteration

“Module by module” does **not** mean preserving every Rust struct, helper, allocation pattern, or function body. It means each Rust module has:

- a named Grandiose counterpart;
- a documented public and cross-module contract;
- a complete exported-symbol mapping;
- a mapped test set;
- a differential snapshot boundary;
- a completion gate;
- no remaining semantic fallback.

A Grandiose module may be a thin facade over shared internal engines. For example:

- `placeflow`, `useflow`, and `escape` retain separate module APIs but share one fact graph and walker;
- `dependency`, `query`, and `revision` retain separate contracts but share one transaction/journal substrate;
- `source`, `scanner`, `header`, and `body` share one cursor/checkpoint toolkit;
- `types`, `signature`, `trait_solver`, `instance`, `core`, `mir`, and `vm_backend` share one mixed-kind term vocabulary and schema descriptions;
- `output`, `artifact_cache`, and `bootstrap` share one canonical binary-envelope writer and bounded reader.

This preserves traceability and feature completeness while still allowing aggressive LOC reductions.

## 1.4 Recommended complete bootstrap shape

```text
       all 36 Grandiose stage0 modules + complete bootstrap stdlib
                              |
                              v
                    Rust grc-stage0 seed
                              |
                   emits complete stage 1
                              |
                              v
          Rust grvm verifies + Grandiose vm_backend self-checks
                              |
              stage 1 compiles the identical complete bundle
                              |
                   emits complete stage 2
                              |
                              v
          Rust grvm verifies + Grandiose vm_backend self-checks
                              |
              stage 2 compiles the identical complete bundle
                              |
                   emits complete stage 3
                              |
                              v
               require stage 2 == stage 3 exact bytes
```

No stage uses a language subset or a Rust semantic fallback. The only host-provided operations are the explicit capabilities already represented by stage0: process arguments, file reads/writes, diagnostics, process limits, and VM execution/supervision.

## 1.5 Highest-leverage clever reductions

The primary size wins now come from **implementation unification**, not feature deletion:

1. **One generic typed-query engine.** `query.rs` should be mostly a parametric `QueryFamily<Key, Value>` plus typed adapters, rather than one hand-built control path per query family.
2. **One transaction and publication substrate.** Parser attempts, inference candidates, interface-cache misses, dependency ledgers, query publications, package sessions, artifact-cache stores, and atomic outputs all use a common mark/commit/rollback discipline implemented with affine guards and label cleanup.
3. **One term and substitution engine.** Types, effect rows, lifetimes, structural constants, trait references, projections, signatures, instance keys, MIR types, and VM metadata use typed views over one mixed-kind term substrate.
4. **One flow graph.** `PlaceFlow`, `UseFlow`, and `EscapeFlow` remain separately reported analyses but never rebuild places, control shape, captures, or reference provenance.
5. **One schema for VM metadata.** Type tags, opcodes, section records, primitive roles, feature bits, verifier operand shapes, encoder widths, decoder rules, and interpreter dispatch are described once and consumed by `runtime_manifest` and `vm_backend`.
6. **One diagnostic model.** Every module constructs structured diagnostics directly; text/JSON rendering is centralized in `service`.
7. **One module/definition index.** Scanner shells, interfaces, resolution, fixities, runtime leaves, and service queries share stable definition identities and namespace lookup.
8. **Source-defined control that fuses away.** Worklists, fixed points, parser choice, early exits, result propagation, rollback, and tree walks become compact library code and specialize to direct MIR control.
9. **Manifest-bound primitive families.** BLAKE3, byte-buffer operations, bitset word operations, and other admitted leaves remove repetitive low-level loops without moving compiler semantics into the VM.
10. **Single-owner state instead of Rust synchronization scaffolding.** Grandiose does not need to reproduce `Arc<Mutex<...>>` mechanically when the same database/revision/query semantics can be expressed by owned state and scoped borrows.

## 1.6 Decision summary

| Decision | Revised recommendation |
|---|---|
| Translate stage0 module by module | **Yes. Mandatory.** Preserve a one-to-one responsibility and parity ledger. |
| Translate Rust line by line | **No.** Share engines and redesign storage beneath the module facade. |
| Ship a reduced bootstrap compiler first | **No.** Intermediate probes are not a product. |
| Omit query/revision/dependency/cache | **No.** Port their complete observable behavior. |
| Collapse `service` to a one-shot compiler only | **No.** Port all current service modes and lifecycle behavior. |
| Port `vm_backend` emission only | **No.** Port the complete current module API, including decode/verify/execute behavior. |
| Keep Rust `grvm` | **Yes.** Independent second verifier/runtime and process trust anchor. |
| Move CLI semantics into Rust launcher | **No.** Port `main.rs`; keep the Rust launcher capability-only and generic. |
| Merge implementations internally | **Yes.** Module boundaries may delegate to shared kernels/toolkit. |
| Delete a feature to meet LOC budget | **Never.** Raise an architecture review and find duplication instead. |
| Require stage-2/stage-3 byte identity | **Yes.** After complete stage0 parity, not before. |
| Keep Rust stage0 after cutover | **Yes.** Oracle, recovery compiler, bootstrap root, and differential implementation. |

# 2. Non-negotiable parity contract

## 2.1 Frozen baseline

The port must begin by freezing one exact stage0 baseline. The active parity
baseline is commit `cfeab4b58d60754a70c819fdda25a1f1024907af`; the original
`02ced7ed1894acfd54b0766e2d718b699fc31a8c` analysis remains retained as
historical design evidence.

After the baseline is frozen:

- no Rust stage0 semantic change lands without either updating the port baseline or being explicitly scheduled after first convergence;
- every exported item in `crates/grandiose-stage0/src/lib.rs` receives a parity ledger row;
- every stage0 source module receives a module ledger row;
- every stage0 test is assigned to one or more module gates;
- every CLI command and option is recorded;
- every schema/generation constant is recorded;
- every stable diagnostic code/class used by tests is recorded;
- every binary magic/schema/version/limit constant is recorded.

The baseline may be advanced, but only through an explicit “baseline roll” change that updates both implementations, regenerates all inventories, and reruns the full corpus.

“Same features as stage0” means every behavior implemented by this frozen baseline. Normative backlog items that the baseline itself does not implement are not silently added to the first port unless the baseline is deliberately advanced; conversely, no implemented baseline behavior may be excluded merely because a design document calls it operational, optional, incremental, or host-facing.

## 2.2 Definition of feature completeness

The Grandiose compiler is stage0-feature-complete only when all of the following are true:

1. **Public API completeness.** Every public Rust export has a Grandiose equivalent or a documented representation-neutral host binding with identical behavior.
2. **Module completeness.** All 36 stage0 source modules have passed their module completion gate.
3. **Compile-domain completeness.** Every program accepted by the frozen stage0 corpus is accepted; every rejected program remains rejected for the same semantic reason.
4. **Mode completeness.** All request modes and CLI commands produce equivalent outcomes.
5. **Operational completeness.** Revisions, snapshots, package sessions, dependencies, query memoization/reuse, caches, cancellation, budgets, retention, publication, and atomic writes behave equivalently.
6. **Artifact completeness.** Candidate and verified VM programs/artifacts, encoding, decoding, verification, limits, execution, and canonical byte production are present.
7. **Diagnostic completeness.** Stable code/class/severity/provenance and canonical rendering contracts are preserved.
8. **Bootstrap completeness.** Manifest encoding and validation, producer binding, source/codegen commitments, and exact convergence checks are present in Grandiose and independently rechecked by the Rust host.
9. **No semantic fallback.** No request can silently invoke Rust stage0 for a missing phase, language feature, query, optimization, verification rule, or CLI command.
10. **Resource completeness.** Small-limit and hostile-input behavior is structured and deterministic rather than panicking, hanging, or allocating without bound.

## 2.3 What may differ internally

The port is free to change:

- data layout;
- ownership structure;
- map/set implementation;
- use of synchronization;
- number of helper functions;
- function parameter grouping;
- module-private type names;
- traversal strategy;
- whether data is packed or enum-shaped;
- whether a product is calculated eagerly or lazily, provided query/reuse observations remain equivalent;
- how multiple module facades delegate to shared engines;
- how source-defined control is expressed before optimization;
- which admitted primitive families implement low-level operations.

The port is not free to change:

- accepted/rejected source meaning;
- public stage0 outcomes;
- stable identity formulas;
- canonical fingerprints and bytes where specified;
- runtime-manifest authority;
- ownership, effect, cleanup, resumption, or verification safety;
- revision/query/cache lifecycle observations;
- diagnostic identity and provenance requirements;
- resource and cancellation result categories;
- bootstrap lineage rules.

## 2.4 Module-complete gate

A module is marked complete only when:

1. its Grandiose facade exists under the mirrored module name;
2. all public types/functions/constants exported from that Rust module are mapped;
3. all cross-module invariants are documented;
4. exact positive, negative, recovery, cancellation, and resource cases are in the module corpus;
5. Rust and Grandiose snapshots agree after canonicalization;
6. the module's original Rust tests and all mapped integration tests pass;
7. no test is ignored, relabeled, or satisfied by a nearby behavior;
8. no Rust semantic callback is used by the Grandiose path;
9. normalized LOC and control-plan output are recorded;
10. any use of effects, labels, or new primitives has a proof/authority test;
11. public error categories are complete and exhaustively adapted;
12. downstream completed modules still pass.

A module may be physically split across several Grandiose files for reviewability. It still has one ledger identity and one final completion gate.

## 2.5 First self-hosted artifact gate

The first artifact named `compiler.grbc` or selected by the default launcher must satisfy all of these before it is checked in:

- all module rows complete;
- all public exports mapped;
- all CLI commands available;
- full stage0 compile-domain corpus green;
- operational/query/cache/revision corpus green;
- full VM backend corpus green;
- Rust verifier accepts the compiler artifact and every emitted artifact;
- Grandiose `vm_backend` independently accepts the same artifacts;
- no semantic host fallback capability exists;
- cold self-compile stays inside the provisional resource envelope;
- stage 1 can compile representative external programs, not just the compiler source.

## 2.6 Trust and host boundary

The Rust host remains responsible for operations that are inherently outside a G1 program:

- loading and independently verifying the compiler artifact before execution;
- process isolation, wall-clock and memory enforcement;
- adapting explicit process/file/diagnostic capabilities;
- supervising the Rust VM;
- independently checking emitted artifact and bootstrap commitments;
- selecting a recovery seed when the normal compiler artifact is unavailable.

The host must **not** implement:

- parsing or resolution;
- type/trait/effect/ownership semantics;
- compiler query results;
- revision or cache decisions on behalf of Grandiose modules;
- MIR construction or optimization;
- bytecode selection or canonical writing;
- the Grandiose `vm_backend` verifier/interpreter behavior;
- CLI command semantics beyond locating the compiler and passing arguments/capabilities.

## 2.7 Quality bars

### Correctness

- Complete module/API/test ledger.
- Exact stage0 source semantics.
- Same canonical artifact bytes where stage0 defines canonical output.
- No hidden feature flag weakens semantics.
- Every output is independently verified by Rust `grvm`.

### Determinism

- Stable request, interface, query, dependency, instance, artifact, and bootstrap fingerprints.
- Map order never leaks into externally observed products.
- Repeated, cache-cold, cache-warm, and cross-host builds agree where the contract requires.

### Security

- Primitive and host authority comes only from exact manifest-bound declaration identities and signatures.
- Cache hits remain untrusted until fully decoded and verified.
- No path, cwd, symlink, source spelling, declaration position, or stale cache entry grants authority.
- Host faults and verifier failures retain their correct failure categories.

### Performance

- Full feature parity is mandatory even if the initial complete compiler is slower.
- The eventual release target remains a cold self-compile at `-O2` below 120 seconds and 4096 MiB.
- Performance optimizations may not change the source or verification contract.

### Size

- Size reviews look for duplicated mechanisms, not removable semantics.
- Crossing a budget triggers redesign or better abstraction, never a feature cut.

# 3. Evidence base and repository state

## 3.1 Pinned current state

This analysis is pinned to commit [`02ced7ed1894acfd54b0766e2d718b699fc31a8c`](https://github.com/MalekiRe/glorious/commit/02ced7ed1894acfd54b0766e2d718b699fc31a8c), whose commit message retires the legacy compiler and self-host tooling. At this revision:

- the active workspace centers on `grandiose-stage0` and `grandiose-vm`;
- the former `self-host/` implementation and many parity tools are absent;
- several design documents describing the prior self-host remain;
- the current Rust stage0 is the implementation to treat as the semantic reference.

The current stage0 describes itself as an independent Rust compiler that shares only the frozen VM artifact contract with the runtime. See [`crates/grandiose-stage0/README.md`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/README.md).

## 3.2 Historical evidence

The parent checkpoint [`a62a08316f5b0c81f74c2a975fe7bd9826157a90`](https://github.com/MalekiRe/glorious/commit/a62a08316f5b0c81f74c2a975fe7bd9826157a90) contains the retired source implementation and its audit records. The most useful artifacts are:

- [`self-host/ARCHITECTURE.md`](https://github.com/MalekiRe/glorious/blob/a62a08316f5b0c81f74c2a975fe7bd9826157a90/self-host/ARCHITECTURE.md)
- [`self-host/count-lines.sh`](https://github.com/MalekiRe/glorious/blob/a62a08316f5b0c81f74c2a975fe7bd9826157a90/self-host/count-lines.sh)
- [`docs/selfhost-parity-audit.md`](https://github.com/MalekiRe/glorious/blob/a62a08316f5b0c81f74c2a975fe7bd9826157a90/docs/selfhost-parity-audit.md)

They should be read as a postmortem:

- the architectural direction was often correct;
- the implementation grew to 21,377 normalized production lines;
- production probes and compatibility surfaces contributed additional code;
- parity remained incomplete;
- the integrated pipeline remained resource-blocked.

## 3.3 Normative design sources

The plan follows these current documents:

- [Language core specification](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/glorious-branded-environment-core-spec.md)
- [Compiler architecture](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/docs/architecture.md)
- [Frontend design](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/docs/frontend-design.md)
- [Ownership/control MIR design](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/docs/mir-design.md)
- [G1 bytecode contract](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/docs/bytecode.md)
- [Bootstrap standard-library contract](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/docs/std-lib.md)
- [Compiler size and speed review](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/docs/size-speed-review.md)
- [Source-defined control kernel](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/docs/control-kernel.md)
- [Remaining work](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/docs/remaining-work.md)

## 3.4 Measurement caveat

The current Rust source inventory below uses GitHub blob byte sizes, not Rust LOC. It is useful only to locate concentration and duplicated representation. It must not be compared directly with the Grandiose normalized-line budgets.

The stage0 `src/` tree contains 36 Rust files totaling approximately **4.23 MiB** of source blobs. The three largest files—`mir.rs`, `vm_backend.rs`, and `core.rs`—account for approximately **60.1%** of those bytes.

| Current file | Blob bytes | Share | Interpretation |
|---|---:|---:|---|
| `mir.rs` | 1,335,858 | 30.1% | MIR model, checked editing, control identities, analyses, cleanup, transformations, validation |
| `vm_backend.rs` | 729,157 | 16.4% | MIR→VM conversion, a second VM vocabulary, encoding, decoding/verification/runtime concerns |
| `core.rs` | 600,149 | 13.5% | Typed Core, elaboration, call/handler/closure/refinement semantics |
| `signature.rs` | 268,362 | 6.1% | canonical interfaces, mixed-kind generics, traits, effects, projections, host imports |
| `service.rs` | 190,939 | 4.3% | end-to-end orchestration, queries, diagnostics, output, request/service policy |
| `trait_solver.rs` | 150,915 | 3.4% | tabled solving, projections, HRTBs, explanations |
| `placeflow.rs` | 122,157 | 2.8% | ownership, moves, loans, storage scopes, cleanup facts |
| `useflow.rs` | 111,747 | 2.5% | quantity use, callable capability escape, replay multiplicity |
| `types.rs` | 107,866 | 2.4% | types, rows, mixed generic arguments, inference, const normalization |
| `header.rs` | 94,932 | 2.1% | header parser and source-shaped semantic syntax |
| `resolution.rs` | 87,826 | 2.0% | namespace/index/body resolution |
| `body.rs` | 83,611 | 1.9% | body syntax and parsing |
| `runtime_manifest.rs` | 79,293 | 1.8% | finite primitive/host authority and signature validation |
| `coherence.rs` | 57,240 | 1.3% | global impl legality and overlap |
| `instance.rs` | 53,408 | 1.2% | concrete instance identity and discovery |
| Other 21 files | 487,768 | 11.0% | request, source, query, cache, revision, output, patterns, etc. |

The concentration is healthy evidence that semantics are real, but it also shows where a naïve transliteration would fail. Under this revised plan **all 36 modules remain required parity obligations**, including `vm_backend.rs` and the operational service/query/cache/revision layers. The size strategy is therefore to compress repeated machinery inside those modules, not to remove their behavior.

## 3.5 Documentation reconciliation required before implementation

The repository currently contains historical documentation that refers to removed self-host paths and tests. Before starting the new port:

1. Mark every retained self-host document as one of:
   - normative target;
   - active implementation guide;
   - historical postmortem;
   - obsolete.
2. Reconcile root README bootstrap commands with the tests present at the pinned current tree.
3. Replace references to the deleted `self-host/` implementation with the mirrored `self-host-stage0/` path used by this plan.
4. Preserve old links in a migration note rather than silently repurposing their meaning.
5. Make the fixed-point command and artifact paths executable from a clean checkout before they are advertised.

This is not cosmetic. A bootstrap project is especially vulnerable to accidentally validating a removed harness, stale seed, or different source bundle.

## 3.6 Full-port interpretation of the repository design

The repository's compactness documents remain useful, but their smaller “source compiler” budgets must be read as a budget for the semantic compiler core, not permission to omit current stage0 operational features. This plan tracks two nested products:

1. **Semantic compiler core:** frontend, static semantics, flow, MIR, optimization, and bytecode production.
2. **Stage0-equivalent compiler system:** the semantic core plus requests, revisions, queries, dependency tracing, caches, service orchestration, output publication, bootstrap, CLI, and complete `vm_backend` behavior.

The first self-hosted artifact is the second product.

# 4. Stage0 architecture analysis under a full-port constraint

## 4.1 End-to-end system shape

The frozen stage0 is a compiler system, not only a source-to-bytecode function:

```text
CLI / library request
        |
        v
request normalization + build identity + modes + capabilities
        |
        v
compiler database / immutable revision / request & package sessions
        |
        v
query families + memoization + dependency ledger + interface cache
        |
        v
source -> scan -> modules -> headers/interfaces/fixities -> resolution
        |
        v
types/signatures/coherence/traits -> body -> Typed Core
        |
        v
PlaceFlow + UseFlow + EscapeFlow -> instances -> MIR -> optimization
        |
        v
runtime manifest -> VM candidate -> canonical encoding -> decode/verify
        |
        v
verified program/artifact + diagnostics + stats + bootstrap manifest
        |
        v
artifact cache / atomic output / CLI execution and verification commands
```

A feature-complete port must preserve every layer. The architectural goal is to make the layers **thin views over shared substrate**, not to delete layers.

## 4.2 Request normalization and identity

`request.rs` and `identity.rs` already establish an excellent semantic boundary:

- source identity derives from package and logical path;
- source bytes and supplied digests are checked;
- package aliases are validated and collision-checked;
- capabilities and runtime selectors are canonicalized;
- build generations, mode, target, options, manifest, and bootstrap stage enter the world fingerprint;
- bootstrap requests carry explicit limits and producer expectations.

This must be translated exactly. The LOC opportunity is to use one canonical fingerprint builder and typed key wrapper, not to weaken the world identity.

## 4.3 Source, scanner, header, and body parsing

The source pipeline is already designed for compactness:

- one lossless token stream;
- no copied lexeme per token;
- one delimiter map;
- structural declaration scanning before body parsing;
- body token ranges retained for demand-driven parsing;
- flat operator streams grouped only after fixity collection;
- contextual block interpretation after candidate selection.

The four modules should remain separately testable, but share:

```text
TokenCursor
TokenPattern
DelimiterMap
ParseCheckpoint
IdRange
Diagnostic constructors
```

Parser reductions should come from labels and cleanup-backed rollback, not from accepting a smaller grammar.

## 4.4 Interfaces, modules, fixities, and resolution

`interface.rs` combines stable definition identity, namespace ownership, public fingerprints, header syntax, and a content-validated interface cache. `module_graph.rs` builds exact package topology from the supplied immutable source world. `fixity.rs` freezes source-defined operator semantics and fingerprints imported ambiguity. `resolution.rs` supplies global and body-local resolution, imports, visibility, occurrences, and reference indices.

A literal port would repeat maps and definition-category logic. The compact full-port shape is:

```text
DefTable
NamespaceIndex
ModuleTable
ImportEdges
FixityView
OccurrenceIndex
InterfaceCache<QueryKey<Interface>, InterfaceSet>
```

Each module retains its API and diagnostics, but the underlying tables are shared. Interface-cache hit/miss behavior and transactional publication remain present.

## 4.5 Mixed-kind terms and signatures

`types.rs`, `header.rs`, and `signature.rs` carry the same underlying kinds in different phases:

- value types;
- lifetimes;
- effect rows;
- structural `u32` constants;
- quantity constants;
- trait heads;
- associated type/effect/const projections;
- callable signatures.

The Grandiose port should define one typed generic-argument family and common traversal/substitution machinery. Header syntax remains source-shaped; frozen semantic terms remain canonical. The modules do not disappear, but much of their private walking code does.

## 4.6 Coherence and trait solving

`coherence.rs` and `trait_solver.rs` must retain:

- orphan rules;
- positive and negative overlap checks;
- auto-trait structural/coinductive behavior;
- tabled ordinary solving;
- associated type, associated effect-row, associated const, and method selection;
- higher-ranked lifetime handling;
- scoped assumptions;
- cycle, depth, and step policies;
- deterministic explanations.

The compression seam is a single canonical goal/answer engine plus shared unification/substitution. Coherence uses the solver instead of implementing a second relation evaluator. Explanation trees are constructed lazily from compact selection traces.

## 4.7 Typed Core

`core.rs` is the largest source-semantic module and must be translated in full. Its parity surface includes:

- every `CoreKind` and `CorePattern` form;
- bidirectional elaboration and candidate selection;
- named and anonymous callables;
- callable/environment brands and `Fn`/`RunsIn` evidence;
- labels and nonlocal transfer;
- effects, handlers, forwarding, resumptions, cancellation, and completion clauses;
- contextual callable blocks;
- reference-result origin and shape;
- closures and captures;
- refinements and hidden binding packs;
- literals, aggregates, projection, assignment, calls, host/intrinsic calls;
- all current diagnostics and finalization checks.

The module should be reduced through `BodyContext`, a small ANF/Core builder, shared candidate transactions, generated term walkers, and reusable callable/brand records. It must not be reduced by leaving a source form for a later compiler generation.

## 4.8 Flow analyses

`placeflow.rs`, `useflow.rs`, and `escape.rs` publish distinct products and diagnostics. Those products are part of stage0 and must remain. Their implementation should share:

- lexical binding identities;
- move paths and projections;
- source-storage scopes;
- control successor shape;
- capture facts;
- reference provenance;
- abrupt-exit classification;
- body traversal and branch checkpoints.

The most compact design is one `FlowGraph` and three analysis views:

```text
PlaceFlowView   -> initialization, moves, loans, storage, cleanup roots
UseFlowView     -> quantity demand, callable use/escape, replay multiplication
EscapeFlowView  -> return/suspension outlives and reference-bearing values
```

Separate output types preserve API parity without three unrelated walkers.

## 4.9 Instance discovery

`instance.rs` remains a canonical worklist engine even after `query.rs` is ported. The query layer memoizes and invalidates instance products; it should not obscure the semantic algorithm.

Required behavior includes mixed-kind instance identity, structural constant normalization, concrete-term validation, substitution-depth limits, per-definition and global limits, call summaries, reachability, and deterministic ordering. The clever reduction is one generic worklist/fixed-point helper and reuse of the shared term encoder.

## 4.10 MIR and storage

`mir.rs` and `mir_storage.rs` are mandatory full translations. “Full” means the implemented baseline, including:

- all exported typed IDs and tables;
- scopes, labels, handlers, performs, resumptions, operations, move paths, storage scopes, and tombstones;
- local/place/block/function/program forms;
- lowering from Core and flow facts;
- checked `MirEditor` operations and invalidation masks;
- cleanup plans, drop flags, storage events, source provenance, and validations;
- current optimization reports and implemented passes;
- current trait-method/instance and nominal-copy descriptors;
- exact source-storage erasure witnesses consumed by the VM backend.

The internal representation may follow the normative compact MIR rather than Rust's exact structs. A schema-backed arena and a generic checked editor can remove large amounts of repetitive validation while preserving every operation.

## 4.11 Runtime manifest

`runtime_manifest.rs` is both semantic authority and a major table-generation opportunity. All current `PrimitiveRole`, floating/integer/array/text/bytes/character/control roles, host import selectors, exact signature validation, canonicalization, and trusted declaration binding must be present.

A single declarative primitive-family table should drive:

- source selector parsing;
- stable tags and names;
- expected signatures;
- manifest canonicalization;
- MIR primitive selection;
- VM opcode selection;
- CLI help;
- wrong-identity/wrong-signature tests.

Names never grant authority.

## 4.12 Complete `vm_backend` port

The earlier plan treated much of `vm_backend.rs` as a Rust-only trust boundary. This revision does not. The Grandiose module must implement the complete frozen stage0 behavior:

- `CandidateVmProgram` and `CandidateVmArtifact` construction;
- `VerifiedVmProgram` and `VerifiedVmArtifact` proof-bearing APIs;
- every exported VM type, generic argument, effect row/projection, capture, pattern, cleanup/storage witness, continuation policy, function, instruction, host, and limit;
- MIR-to-VM lowering;
- canonical program and artifact encoding;
- bounded decoding;
- program and artifact verification;
- execution helpers and host-call behavior used by stage0's `run` path;
- canonical bytes and fingerprints;
- hostile decoder/verifier/resource behavior.

This is not permission to create a fourth persistent compiler IR. A compact implementation can use:

1. one immutable encoded buffer plus checked range views;
2. a candidate builder over typed tables;
3. a verifier proof token that upgrades the same owned storage rather than cloning it;
4. one `VmSchema` table for section/type/opcode/operand/feature rules;
5. one verifier dataflow engine parameterized by instruction transfer rules;
6. one interpreter dispatch derived from the same instruction enum/schema;
7. streaming or range-based encoder views over MIR rather than a duplicated full object graph where possible.

The Rust `grandiose-vm` remains an independent verifier/runtime. Both implementations must accept and reject the same canonical artifacts, and every release artifact must pass the Rust verifier even if the Grandiose verifier has already accepted it.

## 4.13 Revision, dependency, query, cache, and service are required

The modules previously proposed for omission are now central parity obligations.

### Revision

Port immutable worlds, parent revisions, snapshots, pins, retirement, weak cache registration semantics, package sessions, body scratch accounting, staged products, commit/rollback, retention reports, and metadata. Replace `Arc`/`Mutex` implementation detail with owned state and explicit scoped handles where possible.

### Dependency

Port typed nodes, staged transactions, canonical dependency lists, green/red value validation, cycle and incomplete states, traces, and revision retirement.

### Query

Port completeness/recovery policy, frames, exact dependencies, memo tables, publication guards, parent reuse, execution explanations, retention stats, cancellation, budgets, cycle detection, and typed failures. Implement one generic query engine and thin typed query families.

### Caches

Port both interface caching and persistent artifact caching. Cache entries remain untrusted. Preserve envelope/checksum/world/artifact validation, size bounds, symlink rejection, atomic store, hit/miss/rejected/store statistics, and “cache failure does not invalidate a fresh successful compile” behavior.

### Service

Port all orchestration and diagnostic publication behavior. `StageZeroCompiler` remains a reusable compiler service over the database and query modules, not merely a direct call chain.

The main LOC opportunity is that all five areas share transaction, publication, dependency-journal, retention, and bounded-reader/writer primitives.

## 4.14 Bootstrap, output, library, and CLI

`bootstrap.rs`, `output.rs`, `lib.rs`, and `main.rs` are not host-only leftovers.

- `bootstrap` must encode/decode/validate manifests and compare convergence.
- `output` must provide the same atomic same-directory publication semantics through explicit host effects.
- `lib` must expose the complete mapped API.
- `main` must support the frozen commands, CLI options, diagnostic formats, runtime manifest arguments, verification commands, run path, and atomic outputs.

The Rust launcher may locate and verify the compiler artifact, then pass argv and capabilities into the Grandiose `main`. It should not reimplement the command parser or command semantics.

# 5. Lessons from the retired self-host prototype

## 5.1 What to preserve

The historical [`self-host/ARCHITECTURE.md`](https://github.com/MalekiRe/glorious/blob/a62a08316f5b0c81f74c2a975fe7bd9826157a90/self-host/ARCHITECTURE.md) contains several sound decisions:

- one `CompilerSession`;
- one body-local compilation object;
- one-body-at-a-time source lifetimes;
- phase libraries separated from executable host orchestration;
- exactly three semantic representations;
- the Callable/Brand/Quantity/PlaceFlow kernels;
- shared typed ranges and cursors;
- structured cross-phase diagnostics;
- probes separated from production;
- deterministic output boundaries rather than deterministic arena allocation;
- source-defined control intended to specialize to direct control;
- stage-2/stage-3 byte identity.

The old parity corpora and exact Rust-oracle comparison cases are high-value assets. Recover them into a new test-only location with their provenance intact.

## 5.2 What not to preserve

The old implementation should not be restored wholesale because:

1. It reported **21,377 normalized production lines**, already far above the historical 14K semantic-compiler review threshold.
2. Its probe tree added roughly another 2,999 normalized lines.
3. Its audit still listed 98 unported suites.
4. The full compiler pipeline was baseline-blocked by resource limits.
5. Backend/runtime/ownership/optimizer coverage remained incomplete.
6. The latest commit explicitly retired the implementation.
7. The implementation accumulated compatibility projections and staging scaffolding that a clean architecture should not carry.

## 5.3 Specific anti-pattern: primitive authority by name

The retained [`REPORT.md`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/REPORT.md) describes a historical experiment that added a name-based fallback mapping wrapper spellings such as `wrapping_add` to primitive IDs. That may have been useful for a branch milestone, but it must not become the new architecture.

The current runtime-manifest model correctly treats primitive authority as a finite trusted binding to exact declaration identity and exact signature. Source spelling, source position, or a wrapper's body must never grant machine authority.

The new implementation must reject:

- “this function is primitive because its name is `wrapping_add`”;
- “this shell is primitive because it is the Nth declaration in a concatenated prefix”;
- “this function is primitive because its body looks like a placeholder”;
- “a user declaration gets primitive behavior by shadowing a standard-library name.”

## 5.4 Specific anti-pattern: parity by nearby behavior

The historical parity audit explicitly warns that an adjacent probe exercising similar syntax is not enough. Preserve that rule. Every migrated ledger row must name:

- exact source cases;
- exact oracle boundary;
- exact self-host entry point;
- exact comparison operation;
- current status: unported, partial, or covered.

## 5.5 Specific anti-pattern: production probe protocol

Do not put phase CLIs, binary snapshot writers, compatibility numeric tags, or test-only projection APIs into production compiler modules. A single test harness can expose typed phase snapshots from test-only adapters.

## 5.6 Specific anti-pattern: advanced language features without optimizer proof

The prior architecture intended source-defined loops and control helpers, but an integrated pipeline that cannot fuse them may become slow or fail to compile itself within resource limits. Every control abstraction used in a hot compiler path must have:

- a structural summary;
- an expected fused MIR shape;
- a control-plan test;
- a runtime allocation/effect-dispatch budget;
- an O0 fallback path that remains correct, even if slower.

---

## 5.7 The key correction: incompleteness is not compactness

The retired prototype's most important lesson is that a small-looking compiler with large parity gaps is not a smaller implementation of stage0; it is a different, weaker product. The new ledger therefore distinguishes:

- **implementation compression:** same contract, fewer mechanisms;
- **test infrastructure extraction:** same behavior, less production code;
- **feature omission:** forbidden;
- **host fallback:** forbidden for stage0 behavior;
- **not-yet-ported module:** development state only, never a release claim.

# 6. Target architecture with mirrored module boundaries

## 6.1 Source layout

The production tree should mirror the stage0 module names so review and parity remain direct:

```text
self-host-stage0/
  grandiose.toml
  src/
    main.glorious
    lib/lib.glorious
    artifact_cache/artifact_cache.glorious
    body/body.glorious
    bootstrap/bootstrap.glorious
    coherence/coherence.glorious
    core/core.glorious
    dependency/dependency.glorious
    diagnostic/diagnostic.glorious
    escape/escape.glorious
    fixity/fixity.glorious
    header/header.glorious
    identity/identity.glorious
    instance/instance.glorious
    interface/interface.glorious
    mir/mir.glorious
    mir_storage/mir_storage.glorious
    module_graph/module_graph.glorious
    operation/operation.glorious
    output/output.glorious
    pattern/pattern.glorious
    placeflow/placeflow.glorious
    quantity/quantity.glorious
    query/query.glorious
    request/request.glorious
    resolution/resolution.glorious
    revision/revision.glorious
    runtime_manifest/runtime_manifest.glorious
    scanner/scanner.glorious
    service/service.glorious
    signature/signature.glorious
    source/source.glorious
    trait_solver/trait_solver.glorious
    types/types.glorious
    useflow/useflow.glorious
    vm_backend/vm_backend.glorious

    toolkit/
      arena.glorious
      cursor.glorious
      transaction.glorious
      control.glorious
      worklist.glorious
      canonical.glorious
      wire.glorious
      schema.glorious
      flow_graph.glorious
      query_engine.glorious
```

The `toolkit` directory is private implementation substrate. It does not replace module facades or create public behavior absent from stage0.

Large modules may be split internally, for example:

```text
core/
  core.glorious          public facade and data model
  elaborate.glorious
  callables.glorious
  effects.glorious
  refinements.glorious

mir/
  mir.glorious
  model.glorious
  lower.glorious
  edit.glorious
  analyze.glorious
  optimize.glorious
  validate.glorious

vm_backend/
  vm_backend.glorious
  model.glorious
  schema.glorious
  emit.glorious
  encode.glorious
  decode.glorious
  verify.glorious
  execute.glorious
```

The ledger still treats each as one stage0 module.

## 6.2 Shared state model

```text
StageZeroCompiler
    database: CompilerDatabase
    interface_cache: InterfaceCache
    artifact_cache: Option<PersistentArtifactCache>
    query_families: QueryFamilies
    runtime_schema: VmSchema

CompilerDatabase
    database_id
    next_revision
    revisions: RevisionStore
    dependency_ledger
    cache_registry

DatabaseSnapshot
    revision
    parent
    world: NormalizedInputWorld
    pin

RequestSession
    snapshot
    cancellation
    root_budget
    package_sessions
    dependency_transaction
    cache_transactions
    publication_guard

CompilerSession
    request: &RequestSession
    sources / modules / definitions / interfaces
    terms / traits / runtime manifest
    instance graph / MIR program / output pools
    diagnostics / statistics

BodyContext
    owner and source tokens
    syntax / scopes / resolution
    inference / candidate undo
    Core builder
    shared FlowGraph
    MIR builder and analyses
```

The design preserves stage0 lifecycle layers but uses ownership instead of synchronization where the VM executes one request at a time.

## 6.3 Module facade rule

Each mirrored module owns:

- its public types and functions;
- its stable errors/diagnostics;
- its serialization/fingerprint boundary if any;
- its test snapshot adapter;
- its module-level documentation.

A module may delegate to toolkit engines, but callers should not need to know which modules share storage. This makes future baseline updates and bisects tractable.

## 6.4 Exactly three compiler semantic representations

Feature completeness does not require representation duplication. The compiler still has exactly:

1. declaration headers/interfaces plus body token ranges;
2. Typed Core;
3. ownership/control MIR.

Query entries, dependency traces, revision worlds, cache envelopes, VM encoded buffers, verification states, and CLI records are operational or boundary products, not extra source-semantic IRs.

The complete `vm_backend` module may expose candidate and verified program models. Internally it should prefer checked views over shared storage and encoded bytes rather than duplicate mutable semantic graphs.

## 6.5 Four semantic kernels beneath the facades

### Callable

Used by `signature`, `trait_solver`, `core`, `useflow`, `instance`, `mir`, and `vm_backend` for named functions, closures, handler clauses, resumptions, captures, calls, receiver forms, effects, and specialization.

### Brand

Used by `core`, `pattern`, `placeflow`, `escape`, `mir`, and `vm_backend` for labels, environments, refinements, continuations, binder keys, lifetimes, and runtime realizations.

### Quantity

Used by `quantity`, `signature`, `trait_solver`, `core`, `useflow`, `placeflow`, `mir`, and `vm_backend` for ownership, invocation, transitions, resumptions, cancellation, and verifier metadata.

### PlaceFlow

Used by `placeflow`, `useflow`, `escape`, `mir_storage`, `mir`, and `vm_backend` for places, moves, loans, captures, storage, cleanup, suspension, and erasure witnesses.

Module APIs remain separate; the kernels prevent parallel implementations.

## 6.6 Operational kernels beneath the facades

### Transaction kernel

Supports:

- parser speculation;
- inference candidate testing;
- scope restoration;
- interface cache staging;
- dependency transactions;
- query frames/publication;
- package sessions;
- artifact cache store staging;
- atomic output cleanup.

Conceptual API:

```text
Transaction<State, Journal>
    mark
    commit
    rollback
    staged_range

Guard<T>
    commit(label/cancellation)
    cleanup -> rollback/discard
```

### Query kernel

```text
QueryFamily<Key, Value> {
    name
    recovery_policy
    memo
    evaluator
    parent_reuse_validator
    fingerprint
}
```

It supplies the behavior currently repeated around frames, memo entries, dependency journals, cancellation, budgets, cycle stacks, reuse, retention, and execution explanations.

### Canonical binary kernel

Supports fixed and variable records, bounded cursors, magic/schema envelopes, checksums, length prefixes, section directories, patching, and canonical sorting. Used by `artifact_cache`, `bootstrap`, `vm_backend`, and test snapshots.

### Schema kernel

Describes enums with stable tags and exact payloads. Used for primitive roles, VM types/instructions/sections, diagnostic JSON shapes, and test-only snapshots. The schema is data consumed by handwritten semantic transfer functions; it is not reflection or a general macro system.

## 6.7 Effects and explicit state

Effects are used where they eliminate cross-cutting control:

```text
Report<CompilerDiagnostic>
AbortPhase<PhaseError>
BudgetExceeded<BudgetError>
Cancelled
Trace<TraceEvent>
ProcessArgs / FileRead / FileWrite / DiagnosticWrite
VmHostCall
```

Hot semantic state remains explicit in contexts. Query dependency recording may be implemented as a scoped effect handled by the generic query engine because the handler is exactly the query frame journal; this removes parameter threading without making dependencies ambient outside a query.

## 6.8 Host and verifier split

### Grandiose stage0-equivalent compiler owns

- every mirrored module behavior;
- all compile modes and CLI semantics;
- revisions, queries, dependencies, caches, service lifecycle;
- full source semantics and MIR;
- runtime manifest;
- VM candidate construction, encode/decode, verify, and execute behavior;
- bootstrap and atomic output logic expressed through host effects.

### Rust launcher/supervisor owns

- locating and authenticating the bundled compiler artifact;
- supplying argv and explicit host capabilities;
- enforcing process-level time/memory/output limits;
- running `grvm`;
- independently verifying compiler and output artifacts;
- a recovery path to Rust stage0.

### Rust `grvm` owns independently

- the distribution security boundary for bytecode decoding, verification, and execution;
- host capability adaptation;
- process isolation and runtime faults.

Duplicate verifier implementations are intentional defense and parity, not duplicated compiler IR.

## 6.9 Determinism

The full system must canonicalize:

- request worlds and revisions;
- query dependencies and execution explanations;
- dependency traces;
- cache envelopes;
- diagnostics;
- interfaces and fixities;
- instance keys and worklist publication;
- MIR externally observed dumps;
- VM tables/sections/bytes;
- bootstrap manifests;
- CLI JSON output.

Internal arena allocation and hash-map order remain free where they cannot escape.

## 6.10 Bootstrap source discipline

The compiler source may use a carefully selected subset of Grandiose for bootstrap ergonomics, but that is a **source-style choice**, not a capability limit. The compiler it produces must still accept the complete stage0 language and operational surface.

# 7. Module-by-module translation ledger
## 7.1 Ledger rules

Every module below is mandatory. “Complete” means the gate in section 2.4, not “enough for the compiler to compile itself.” The order is a dependency order, not a ranking of importance. A later module may force an earlier module's internal refactor, but may not bypass its facade or invalidate its completed parity corpus.

## 7.2 Summary table

| Order | Rust module | Grandiose module | Scope | First-release status |
|---:|---|---|---|---|
| 01 | `diagnostic.rs` | `diagnostic.glorious` | Stable diagnostic vocabulary: severity, class, code, source span, request diagnostics. | **Required** |
| 02 | `quantity.rs` | `quantity.glorious` | Checked interval algebra used by ownership, callables, environments, and resumptions. | **Required** |
| 03 | `identity.rs` | `identity.glorious` | BLAKE3 digests and stable package/file/module/definition/revision identities. | **Required** |
| 04 | `operation.rs` | `operation.glorious` | Request-scoped cancellation, hierarchical budgets, leases, and publication guards. | **Required** |
| 05 | `request.rs` | `request.glorious` | Compilation modes, build generations, source inputs, normalized immutable worlds, fingerprints, and bootstrap limits. | **Required** |
| 06 | `output.rs` | `output.glorious` | Atomic same-directory output publication. | **Required** |
| 07 | `source.rs` | `source.glorious` | Lexer, tokens, spans, line index, delimiter pairing, scalar-literal classification. | **Required** |
| 08 | `scanner.rs` | `scanner.glorious` | Structural top-level declaration scanning and body/header token ranges. | **Required** |
| 09 | `header.rs` | `header.glorious` | Complete source-shaped header syntax. | **Required** |
| 10 | `interface.rs` | `interface.glorious` | Canonical definitions, namespaces, header/public fingerprints, interface diagnostics, and transactional interface cache. | **Required** |
| 11 | `module_graph.rs` | `module_graph.glorious` | Exact package/module topology over supplied source blobs. | **Required** |
| 12 | `fixity.rs` | `fixity.glorious` | Source-defined prefix/infix fixity tables and fingerprints. | **Required** |
| 13 | `resolution.rs` | `resolution.glorious` | Global definition index, imports/visibility, body scopes, occurrences, references, and resolution states. | **Required** |
| 14 | `types.rs` | `types.glorious` | Canonical mixed-kind terms, effect rows, lifetimes, structural constants, and body-local inference. | **Required** |
| 15 | `signature.rs` | `signature.glorious` | Header elaboration, canonical interfaces, intrinsic identities, substitutions, and instantiation. | **Required** |
| 16 | `coherence.rs` | `coherence.glorious` | Global implementation legality. | **Required** |
| 17 | `trait_solver.rs` | `trait_solver.glorious` | Deterministic tabled trait/projection/method solving and explanations. | **Required** |
| 18 | `pattern.rs` | `pattern.glorious` | Pattern binding/elaboration and shared decision plans. | **Required** |
| 19 | `body.rs` | `body.glorious` | Transient body syntax and parsing. | **Required** |
| 20 | `core.rs` | `core.glorious` | Complete bidirectional elaboration and Typed Core. | **Required** |
| 21 | `placeflow.rs` | `placeflow.glorious` | Ownership, moves, loans, bindings, storage scopes, refinements, events, and cleanup facts. | **Required** |
| 22 | `useflow.rs` | `useflow.glorious` | Quantitative callable/value use and escape analysis. | **Required** |
| 23 | `escape.rs` | `escape.glorious` | Reference/lifetime escape checks at return and suspension boundaries. | **Required** |
| 24 | `mir_storage.rs` | `mir_storage.glorious` | Persistent source-storage scope and lifecycle identities. | **Required** |
| 25 | `instance.rs` | `instance.glorious` | Canonical instance identity, summaries, reachability, and limits. | **Required** |
| 26 | `mir.rs` | `mir.glorious` | Complete ownership/control MIR, editor, lowering, validation, and implemented optimizer. | **Required** |
| 27 | `runtime_manifest.rs` | `runtime_manifest.glorious` | Finite primitive and host authority. | **Required** |
| 28 | `vm_backend.rs` | `vm_backend.glorious` | MIR-to-VM lowering, VM model, canonical encode/decode, verification, execution, artifacts, hosts, and limits. | **Required** |
| 29 | `bootstrap.rs` | `bootstrap.glorious` | Bootstrap manifest commitments and convergence. | **Required** |
| 30 | `dependency.rs` | `dependency.glorious` | Revision-owned typed dependency ledger. | **Required** |
| 31 | `revision.rs` | `revision.glorious` | Compiler database, immutable revisions/snapshots, package/request sessions, cache retirement, retention. | **Required** |
| 32 | `query.rs` | `query.glorious` | Typed revision-qualified memoization and query execution. | **Required** |
| 33 | `artifact_cache.rs` | `artifact_cache.glorious` | Persistent content-addressed cache of verified programs. | **Required** |
| 34 | `service.rs` | `service.glorious` | End-to-end StageZeroCompiler orchestration, outcomes/errors, diagnostics and query families. | **Required** |
| 35 | `lib.rs` | `lib.glorious` | Complete public module and re-export surface. | **Required** |
| 36 | `main.rs` | `main.glorious` | Full stage0 CLI and command adapter in Grandiose. | **Required** |

## 7.3 Detailed module cards

### M01 — `diagnostic.rs`

**Responsibility.** Stable diagnostic vocabulary: severity, class, code, source span, request diagnostics.

**Exact parity contract.**

- All exported enums/records and constructor behavior.
- Stable ordering/equality and source fingerprint attachment.
- Every diagnostic class including cache, verification, runtime, cancellation, and invariant.

**Clever reduction strategy.**

- Represent codes as interned or static text IDs with one display table.
- Use one generic diagnostic builder shared by all modules.

**Primary test ownership.** diagnostic unit tests plus all service canonicalization/rendering tests.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M02 — `quantity.rs`

**Responsibility.** Checked interval algebra used by ownership, callables, environments, and resumptions.

**Exact parity contract.**

- All constants and checked constructors.
- sequence, branch hull, multiplication, containment, intersection, ordering, and errors.
- Finite/infinite overflow and boundary behavior.

**Clever reduction strategy.**

- Tiny nominal record and source-defined arithmetic.
- Use labels for overflow/invalid-interval exit.

**Primary test ownership.** quantity.rs and every quantity-sensitive Core/UseFlow/VM test.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M03 — `identity.rs`

**Responsibility.** BLAKE3 digests and stable package/file/module/definition/revision identities.

**Exact parity contract.**

- Exact digest bytes and length-delimited part hashing.
- Package-module alias normalization.
- File/definition/method identity formulas.
- Database-local revision IDs and fresh database identity behavior.

**Clever reduction strategy.**

- Manifest-bound BLAKE3 primitive or streaming hash leaf.
- Generic typed-key wrapper over Digest.
- No copied hex-format implementation per key type.

**Primary test ownership.** identity-dependent request/interface/instance/bootstrap/cache golden tests.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M04 — `operation.rs`

**Responsibility.** Request-scoped cancellation, hierarchical budgets, leases, and publication guards.

**Exact parity contract.**

- Cancellation check/cancel semantics.
- Parent/child charges, rollback on failed child charge, release and overflow.
- Affine budget leases.
- Publication stage/commit/discard and last-moment cancellation.

**Clever reduction strategy.**

- Use affine cleanup guards instead of atomics.
- Represent cancellation as scoped state/effect in single-thread VM.
- One generic Guard<T> implementation.

**Primary test ownership.** operation.rs, request/revision/service cancellation and small-budget tests.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M05 — `request.rs`

**Responsibility.** Compilation modes, build generations, source inputs, normalized immutable worlds, fingerprints, and bootstrap limits.

**Exact parity contract.**

- All modes and generation constants.
- Logical path and package alias validation.
- Source identity/digest/UTF-8 checks.
- Capability and runtime-manifest canonicalization.
- Bootstrap stage validation and all world fingerprint inputs.

**Clever reduction strategy.**

- One canonical fingerprint builder.
- Use shared sorted/dedup helpers and structured validation labels.

**Primary test ownership.** request_and_revision.rs, source_and_query.rs, bootstrap request tests.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M06 — `output.rs`

**Responsibility.** Atomic same-directory output publication.

**Exact parity contract.**

- Invalid-target handling.
- Private sibling creation with collision retries.
- write, flush/sync, rename, cleanup-on-error.
- No implicit parent creation.
- Existing target preservation on failure.

**Clever reduction strategy.**

- Expose host atomic-write operation as a narrow effect while retaining Grandiose policy and error mapping.
- Cleanup guard removes staging file.

**Primary test ownership.** output unit tests and CLI/cache publication tests.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M07 — `source.rs`

**Responsibility.** Lexer, tokens, spans, line index, delimiter pairing, scalar-literal classification.

**Exact parity contract.**

- Complete token grammar and diagnostics.
- UTF-8 byte spans and UTF-16 positions.
- All numeric/string/character/lifetime/operator corner cases.
- Delimiter map and ordering.
- Exact scalar literal classification.

**Clever reduction strategy.**

- Single byte cursor and table-driven ASCII classes.
- Label-based token scanning and one delimiter work stack.
- Borrow source slices rather than copy lexemes.

**Primary test ownership.** scanner.rs, source_and_query.rs, scalar/literal conformance, hostile lexical corpus.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M08 — `scanner.rs`

**Responsibility.** Structural top-level declaration scanning and body/header token ranges.

**Exact parity contract.**

- All declaration kinds including host imports, bare callables, aliases, modules, imports, fixities.
- Braced effect rows/generic arguments and initializer delimiters.
- Body/semicolon boundary behavior.
- Inline range scanning and diagnostics.

**Clever reduction strategy.**

- Shared TokenCursor and delimiter jumps.
- Generic find-boundary state machine rather than kind-specific loops.

**Primary test ownership.** scanner.rs, header.rs, module_graph.rs, CLI source-bundle cases.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M09 — `header.rs`

**Responsibility.** Complete source-shaped header syntax.

**Exact parity contract.**

- Mixed generic kinds, defaults, structural expressions and projections.
- Callables/effects/rows/lifetimes/references.
- traits, supertraits, associated types/effect rows/consts, methods.
- positive/negative impls and method bodies.
- nominal layouts, enum payloads, imports, fixities, host declarations.
- All recovery diagnostics and spans.

**Clever reduction strategy.**

- Parser transaction toolkit and range builders.
- One generic argument parser keyed by expected/source kind.
- Schema-driven syntax visitors.

**Primary test ownership.** header.rs, signature.rs, coherence.rs, runtime_manifest.rs and self-host header parity corpora.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M10 — `interface.rs`

**Responsibility.** Canonical definitions, namespaces, header/public fingerprints, interface diagnostics, and transactional interface cache.

**Exact parity contract.**

- All Definition fields and namespace rules.
- Header/constant value fingerprinting.
- Public fingerprint semantics.
- Duplicate detection and deterministic ordering.
- Cache keys/context generation, hits/misses, staging and commit.

**Clever reduction strategy.**

- One DefTable and one generic transactional cache.
- Shared canonical fingerprint writer.
- Owned cache state instead of Mutex scaffolding.

**Primary test ownership.** interface.rs, module_graph.rs, retention and incremental interface tests.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M11 — `module_graph.rs`

**Responsibility.** Exact package/module topology over supplied source blobs.

**Exact parity contract.**

- Root selection, inline/external modules, canonical child paths.
- Missing, duplicate, orphan, and cyclic module diagnostics.
- Lex/scan/interface propagation.
- Interface-cache transaction behavior.
- Canonical module ordering.

**Clever reduction strategy.**

- Worklist/DFS helper with branded early cycle exit.
- Reuse Def/Module tables instead of copying interface records.

**Primary test ownership.** module_graph.rs and module/source-bundle integration tests.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M12 — `fixity.rs`

**Responsibility.** Source-defined prefix/infix fixity tables and fingerprints.

**Exact parity contract.**

- Prelude entries, local replacement, imports, ambiguity retention.
- Prefix/infix namespaces, forms, precedence.
- Exact fingerprint content and deterministic order.

**Clever reduction strategy.**

- One generic ordered map view and schema enum tags.
- Share operator NameId rather than String copies internally.

**Primary test ownership.** fixity.rs, body operator grouping and imported-fixity tests.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M13 — `resolution.rs`

**Responsibility.** Global definition index, imports/visibility, body scopes, occurrences, references, and resolution states.

**Exact parity contract.**

- All namespaces and path roots.
- explicit/group/glob/self imports and fixed-point re-exports.
- ambiguity/inaccessibility/unresolved/recovered states.
- body-local ScopeMap shadowing and restoration.
- Occurrence/ReferenceIndex roles and stable ordering.
- Fixity visibility integration.

**Clever reduction strategy.**

- Journaled ScopeMap cleanup.
- One find-unique helper for ambiguity.
- Worklist fixed point for imports.
- Shared target enum instead of parallel maps.

**Primary test ownership.** resolution.rs, module tests, body/Core name-resolution corpus.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M14 — `types.rs`

**Responsibility.** Canonical mixed-kind terms, effect rows, lifetimes, structural constants, and body-local inference.

**Exact parity contract.**

- Every exported type/kind/argument/variable/error.
- Structural u32 normalization/substitution/resource limits.
- Effect-row canonicalization and projection identity.
- Type unification, occurs/kind checks, fingerprints and canonical encodings.
- No unresolved terms across frozen boundaries.

**Clever reduction strategy.**

- One generated/handwritten fold over term views.
- Intern only frozen terms.
- Undo-log inference assignments.
- Common generic-argument encoder.

**Primary test ownership.** types.rs, signature/trait/instance/Core type tests.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M15 — `signature.rs`

**Responsibility.** Header elaboration, canonical interfaces, intrinsic identities, substitutions, and instantiation.

**Exact parity contract.**

- All elaborated headers and associated item forms.
- Mixed-kind generic slot validation.
- Callable/effect/trait/impl/nominal/alias/host-import semantics.
- Intrinsic Fn/Label/RunsIn/Environment/Available identities.
- Projection/default/method substitution and all errors.

**Clever reduction strategy.**

- Reuse term substitution and one header-to-semantic visitor.
- Data-driven associated-item kind handling.
- Thin intrinsic fast paths returning ordinary evidence.

**Primary test ownership.** signature.rs, interface.rs, trait_solver.rs, runtime_manifest.rs.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M16 — `coherence.rs`

**Responsibility.** Global implementation legality.

**Exact parity contract.**

- Trait/self resolution, privacy and orphan checks.
- positive-positive, negative-negative, and positive-negative overlap.
- negative generic constraint validation.
- where-bound-aware overlap through the canonical solver.
- deterministic related spans and messages.

**Clever reduction strategy.**

- Reuse solver unification/candidate engine.
- One generic term free-variable collector.

**Primary test ownership.** coherence.rs and semantic conformance suites.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M17 — `trait_solver.rs`

**Responsibility.** Deterministic tabled trait/projection/method solving and explanations.

**Exact parity contract.**

- Ordinary, auto/coinductive, negative, supertrait and scoped-assumption solving.
- Associated type/effect-row/const/method answers.
- HRTB scopes, GAT arguments and mixed kinds.
- cycle/depth/step handling.
- query reset and stable evidence.
- Complete explanation trees and candidate rejections.

**Clever reduction strategy.**

- Generic Goal/Answer table.
- Lazy explanation reconstruction.
- Worklist/fixed-point control helpers.
- Shared substitution/unification.

**Primary test ownership.** trait_solver.rs, signature.rs, coherence.rs, Core call-selection tests.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M18 — `pattern.rs`

**Responsibility.** Pattern binding/elaboration and shared decision plans.

**Exact parity contract.**

- All pattern kinds and binding modes.
- binder keys, generic scopes, field visibility, duplicate/unknown fields.
- ownership/discard outcomes and diagnostics.
- decision plan semantics used by Core handlers and refinements.

**Clever reduction strategy.**

- One decision-DAG builder and walker.
- Brand kernel for binder/refinement identities.

**Primary test ownership.** pattern.rs, core.rs, ownership pattern and handler pattern suites.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M19 — `body.rs`

**Responsibility.** Transient body syntax and parsing.

**Exact parity contract.**

- Every ExprKind/PatternKind/HandlerClause/ClosureParameter form.
- Flat operator chains and contextual block preservation.
- left-to-right source ranges and all diagnostics.
- labels, effects, handle/completion, calls, assignment, aggregates, closures, patterns.

**Clever reduction strategy.**

- Shared parser toolkit, checkpoints and range builders.
- Direct enums rather than universal tagged nodes.
- No production snapshot protocol.

**Primary test ownership.** body.rs, core.rs, source assignment and parser conformance suites.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M20 — `core.rs`

**Responsibility.** Complete bidirectional elaboration and Typed Core.

**Exact parity contract.**

- All exported Core records/kinds and every current semantic rule.
- candidate selection, inference, traits, effects, environments, labels, callables, closures, captures, patterns/refinements.
- handlers, forwarding, resumptions, cancellation and terminality.
- reference-origin/shape, host/intrinsic calls, assignments and storage semantics.
- finalization, evidence sealing/erasure and diagnostics.

**Clever reduction strategy.**

- BodyContext methods instead of long parameter lists.
- CoreBuilder/ANF bind helper.
- Callable/Brand kernels.
- Shared term and pattern walkers.
- Effects for diagnostics/abort only.

**Primary test ownership.** core.rs, semantic_conformance, effect/control, callable, ownership and source-lowering suites.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M21 — `placeflow.rs`

**Responsibility.** Ownership, moves, loans, bindings, storage scopes, refinements, events, and cleanup facts.

**Exact parity contract.**

- All exported identities/facts/states/events/diagnostics.
- shadow-safe lexical binding identity.
- projection overlap and move-path tree.
- shared/unique/reborrow/NLL behavior.
- label storage exits, closure/lifted bodies, partial moves, assignments and cleanup roots.

**Clever reduction strategy.**

- Shared FlowGraph and one body walker.
- Bitsets/sparse maps and branch undo log.
- Range-based facts.

**Primary test ownership.** placeflow-related core/service suites, source storage/assignment/ownership tests.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M22 — `useflow.rs`

**Responsibility.** Quantitative callable/value use and escape analysis.

**Exact parity contract.**

- Callable use facts and boundaries.
- principal/actual quantities, branch hull, sequence and replay multiplication.
- aggregate callable fields, closure captures, handler/resumption use.
- value dispositions and all diagnostics.

**Clever reduction strategy.**

- Consume shared FlowGraph/Core summaries.
- Quantity kernel and generic fold.
- No second place/control reconstruction.

**Primary test ownership.** quantity/use tests, handler replay, callable evidence and must-move suites.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M23 — `escape.rs`

**Responsibility.** Reference/lifetime escape checks at return and suspension boundaries.

**Exact parity contract.**

- All reference provenance shapes.
- parameters, aggregates, assignments, calls, effects, closures, handlers and completions.
- outlives diagnostics and fail-closed cases.
- Interaction with PlaceFlow loan roots.

**Clever reduction strategy.**

- Shared provenance graph and Core walker.
- Use Brand/Flow facts rather than textual root maps where possible.

**Primary test ownership.** escape/lifetime/reference effect tests and semantic conformance ownership suites.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M24 — `mir_storage.rs`

**Responsibility.** Persistent source-storage scope and lifecycle identities.

**Exact parity contract.**

- All scope/event/table records and validation.
- StorageLive/StorageDead ordering, binding identity and scope parentage.
- Freeze/import behavior used by MIR and VM erasure.

**Clever reduction strategy.**

- Reuse shared scope/range arenas.
- Schema-derived validators.

**Primary test ownership.** source_storage_lowering, source_storage_cleanup, storage_statement_contract, VM storage tests.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M25 — `instance.rs`

**Responsibility.** Canonical instance identity, summaries, reachability, and limits.

**Exact parity contract.**

- Every InstanceKey/Argument/Error/Limit/Root/Graph/Summary behavior.
- Mixed-kind concrete checks and const normalization.
- Substitution depth, total/per-definition limits.
- Call summary solving and deterministic work order.

**Clever reduction strategy.**

- Shared canonical term encoder.
- Generic work queue and fixed-point runner.
- Query adapter is thin around semantic worklist.

**Primary test ownership.** instance/specialization/service and generic call tests.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M26 — `mir.rs`

**Responsibility.** Complete ownership/control MIR, editor, lowering, validation, and implemented optimizer.

**Exact parity contract.**

- All exported models, IDs, tables, instructions, terminators, patterns, cleanup, continuation policies and reports.
- Core/Flow/Instance lowering.
- checked edits, tombstones, invalidation, CFG/analysis behavior.
- all implemented optimization and canonicalization.
- all validation and diagnostic contracts.

**Clever reduction strategy.**

- Compact schema-backed arenas.
- One generic checked editor/operand/edge API.
- Shared analysis bundles and invalidation bitmask.
- Control helpers that fuse to direct CFG.

**Primary test ownership.** mir.rs, vm_backend.rs, source storage/assignment, optimizer and semantic conformance suites.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M27 — `runtime_manifest.rs`

**Responsibility.** Finite primitive and host authority.

**Exact parity contract.**

- Every PrimitiveRole and float/int/array/text/bytes/char/control family.
- selector parse/name/tag and canonical ordering.
- exact declaration identity and signature validation.
- host import selectors, manifest digest and errors.
- all trusted runtime tables.

**Clever reduction strategy.**

- Single primitive schema drives parser, validator, CLI and VM selection.
- Family loops instead of repeated match trees while retaining exhaustive stable IDs.

**Primary test ownership.** runtime_manifest.rs, CLI selectors, malicious shadowing/wrong-signature tests.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M28 — `vm_backend.rs`

**Responsibility.** MIR-to-VM lowering, VM model, canonical encode/decode, verification, execution, artifacts, hosts, and limits.

**Exact parity contract.**

- Every export listed by lib.rs.
- Full instruction/type/effect/capture/pattern/cleanup/storage vocabulary.
- candidate-to-verified proof boundary.
- program/artifact encode/decode/verify and exact bytes.
- execution, host calls, display/run behavior.
- all decode/execute resource limits and hostile rejection.

**Clever reduction strategy.**

- VmSchema and shared transfer-rule tables.
- Proof token upgrades shared storage.
- Range views over encoded buffer.
- One dataflow engine and one interpreter loop.
- Primitive families generated from manifest schema.

**Primary test ownership.** vm_backend.rs, vm_storage_erasure/identity, semantic conformance backend, hostile artifact and runtime suites.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M29 — `bootstrap.rs`

**Responsibility.** Bootstrap manifest commitments and convergence.

**Exact parity contract.**

- Exact magic/schema/encoding/decoding.
- stage validation and producer expectations.
- world/source/codegen/artifact/byte fingerprints.
- adjacent-stage convergence and artifact compatibility errors.
- all limits and trailing/corrupt input behavior.

**Clever reduction strategy.**

- Shared fixed-record bounded codec.
- Generic digest-field encoder.
- Label-based decode failure.

**Primary test ownership.** bootstrap tests, CLI verify-bootstrap, stage harness and exact convergence tests.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M30 — `dependency.rs`

**Responsibility.** Revision-owned typed dependency ledger.

**Exact parity contract.**

- All nodes, statuses, traces and transactions.
- canonical dependency sorting/dedup.
- green/red value validation, first-changed explanations.
- cold, cycle and incomplete handling.
- commit and revision removal.

**Clever reduction strategy.**

- Generic DFS/worklist over typed nodes.
- Transaction guard and one canonical trace builder.

**Primary test ownership.** dependency/query/revision/service invalidation and explanation tests.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M31 — `revision.rs`

**Responsibility.** Compiler database, immutable revisions/snapshots, package/request sessions, cache retirement, retention.

**Exact parity contract.**

- All public errors/metadata/statuses/stats.
- database-local IDs, parent revisions and world pins.
- snapshot acquisition and stale/retired behavior.
- cache registration/discard safe points.
- package session open/stage/commit/rollback.
- body scratch/staged product accounting.
- request publication and retention collection.

**Clever reduction strategy.**

- Single-owner revision store.
- Affine snapshot/session handles and cleanup.
- Generic registry callbacks without Arc/Weak scaffolding.
- Effects only for cancellation/resource exit.

**Primary test ownership.** request_and_revision.rs, retention.rs, source_and_query.rs, service lifecycle tests.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M32 — `query.rs`

**Responsibility.** Typed revision-qualified memoization and query execution.

**Exact parity contract.**

- Completeness/recovery policies.
- frames, exact dependencies and recovered dependency rules.
- memo entries/tables, publication guards, reuse, discard and retention stats.
- execution kinds/reasons.
- QueryContext, nested dependency observation, cancellation, budget, invariant, cycle and recovered-product failures.

**Clever reduction strategy.**

- One parametric QueryFamily engine.
- Scoped Depend effect handled by frame.
- Generic publication transaction and retention counter.
- Thin typed family adapters.

**Primary test ownership.** source_and_query.rs, request_and_revision.rs, service tests, cache/reuse/cycle/cancellation corpus.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M33 — `artifact_cache.rs`

**Responsibility.** Persistent content-addressed cache of verified programs.

**Exact parity contract.**

- Exact envelope magic/schema/world/program/checksum/length.
- entry-size cap and bounded reads.
- symlink/non-file/unreadable/corrupt/stale/verifier-rejected misses.
- hit/miss/rejected/store stats.
- atomic store and nonfatal store failures.

**Clever reduction strategy.**

- Shared Envelope codec and bounded reader.
- Host file effects plus cleanup-backed atomic writer.
- Owned stats rather than Mutex.

**Primary test ownership.** artifact cache unit/integration tests and hostile cache corpus.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M34 — `service.rs`

**Responsibility.** End-to-end StageZeroCompiler orchestration, outcomes/errors, diagnostics and query families.

**Exact parity contract.**

- All compilation modes and phase ordering.
- database/revision/request/package/query/cache integration.
- all diagnostic adapters, canonicalization, span validation, error cap, JSON and text.
- artifact/bootstrap outcomes, verification and runtime categories.
- retention/dependency/query inspection APIs and statistics.

**Clever reduction strategy.**

- CompilerSession groups parameters.
- Generic query family registration.
- Report effect and one diagnostic adapter table per phase.
- Phase labels for terminal exits.

**Primary test ownership.** service.rs, cli.rs, semantic_conformance, all end-to-end request/cache/retention tests.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M35 — `lib.rs`

**Responsibility.** Complete public module and re-export surface.

**Exact parity contract.**

- Every module declaration and public re-export mapped.
- Stable public naming or documented Grandiose naming translation.
- No hidden Rust-only semantic entry point.
- Public API inventory generated and checked.

**Clever reduction strategy.**

- Generate/test inventory from a checked manifest rather than handwritten duplicate lists.
- Thin facade only.

**Primary test ownership.** public API manifest test plus downstream harness compilation.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

### M36 — `main.rs`

**Responsibility.** Full stage0 CLI and command adapter in Grandiose.

**Exact parity contract.**

- check/run/emit-vm/emit-bootstrap-vm/verify-vm/verify-bootstrap.
- all diagnostic formats and option parsing.
- root/additional source mapping.
- capability and runtime leaf/host selectors.
- request construction, run behavior, atomic outputs, exit categories and usage.

**Clever reduction strategy.**

- Use source-defined option parser with labels.
- Primitive schema drives role help.
- Host effects only at this outer module.

**Primary test ownership.** cli.rs and exact command-line golden/negative/integration tests.

**Done when.** The exported-symbol inventory is complete, all mapped positive/negative/resource/cancellation cases agree with Rust stage0, no Rust semantic callback remains, and all previously completed downstream-compatible snapshots remain green.

## 7.4 Cross-module sharing constraints

Shared implementation is encouraged only when these rules hold:

1. Each module can still be tested through its own facade.
2. Shared storage has one authoritative owner and typed views.
3. Module-specific diagnostics and fingerprints are not collapsed into generic strings.
4. A shared helper exposes all facts required by every participating module; no module reconstructs hidden state.
5. Refactoring a shared helper reruns every module gate that consumes it.
6. The parity ledger records cross-module dependencies so “green” modules are invalidated truthfully after substrate changes.

## 7.5 Public API inventory

Generate a checked manifest from `lib.rs` that records:

```text
module
exported name
kind: type | function | constant | trait-like contract
Rust signature summary
Grandiose signature summary
owner module
parity test
status
```

The manifest is test input, not generated production code. A changed Rust export fails CI until mapped or explicitly baseline-excluded.

# 8. Using effects to reduce compiler code

Effects are one of Grandiose's most valuable self-hosting tools, but they can either remove boilerplate or create a hidden state machine. The deciding rule is:

> Use effects for **cross-cutting control capabilities with narrow operations**. Keep hot, high-volume compiler state as explicit borrowed context.

## 8.1 Effect-use principles

1. An effect operation must represent a real capability or nonlocal phase action.
2. The operation's effect row must improve API clarity by exposing a dependency.
3. The handler must be installed at a deliberate architectural boundary.
4. The hot implementation must control-inline or lower without avoidable allocation/dynamic lookup when used per token, per node, or per instruction.
5. One-shot operations are preferred in compiler implementation.
6. Multi-shot resumptions are not a parser backtracking mechanism.
7. Effect operations must not hide ownership that the compiler needs to reason about explicitly.
8. Tests should be able to install deterministic mock handlers.

## 8.2 Recommended compiler effects

The exact syntax below is illustrative but follows the language core's nominal effect, quantity, label, and handler model.

### 8.2.1 Recoverable diagnostics

```rust
effect Report {
    [1,1] emit(diagnostic: Diagnostic) ->
}
```

Use it for errors that allow safe local recovery:

- invalid token;
- missing delimiter;
- unresolved name with a poison term;
- failed candidate summary;
- nonfatal interface conflict where later declarations can still be scanned.

A phase-level handler accumulates structured diagnostics, enforces the 100-error cap, and optionally suppresses cascades.

Advantages:

- no `&mut Vec<Diagnostic>` threaded through every parser/checker function;
- phase APIs state that they may report;
- test handlers can capture exact diagnostics;
- host rendering remains outside semantic phases;
- recovery and terminal failure stay distinct.

Do not use `Report` to represent internal invariant failures. Those should transfer to a separate compiler-failure boundary.

### 8.2.2 Phase abort

A terminal effect is possible:

```rust
effect AbortPhase<E> {
    stop(error: E) -> !
}
```

However, a label is often smaller and more precise:

```rust
@phase: Result<PhaseProduct, DiagnosticBundle> {
    ...
    @phase(Result::Err(errors))
}
```

Recommended rule:

- use a typed lexical label for one function/phase's early terminal return;
- use a terminal effect only when the abort capability must cross several independently reusable callback layers and cannot be represented as an ordinary label-generic argument without clutter.

### 8.2.3 Resource budget

```rust
effect Budget {
    [1,1] charge(kind: BudgetKind, amount: u32) ->
    exhausted(kind: BudgetKind, limit: u64) -> !
}
```

Or, more compactly, pass an explicit `&mut Budget` and use a label for exhaustion. Choose based on call frequency:

- per AST node/solver step: explicit state is likely smaller and faster;
- per recursive phase boundary: an effect can remove repetitive checks.

A hybrid is recommended:

```text
hot loop updates local counter
boundary invokes Budget::charge(total)
```

### 8.2.4 Optional tracing/statistics

```rust
effect CompileTrace {
    [1,1] event(event: TraceEvent) ->
}
```

Handlers:

- no-op release handler;
- counter-only `--stats` handler;
- detailed debug handler.

The compiler should not construct formatted strings in normal mode. Events carry IDs and counts. Control fusion or a static no-op specialization must remove calls entirely when tracing is disabled.

### 8.2.5 Host effects

The standard-library design already identifies host capabilities such as process arguments, file reads, file writes, and host diagnostics. Keep them at the outermost driver:

```rust
compiler_application() -> / {
    ProcessArgs,
    FileRead,
    FileWrite,
    Diagnostic
}
```

Semantic compiler functions should receive an immutable request and have no host effect row.

### 8.2.6 Source/provider effect: usually reject

An effect such as:

```rust
effect SourceAccess {
    text(file: FileId) -> &Text
}
```

looks convenient but is too frequent and obscures lifetime/ownership. Prefer `&SourceMap` in `CompilerSession`. Use an effect only for genuinely virtual or remote source acquisition in a future host shell.

### 8.2.7 Fresh-ID effect: usually reject

Do not model every allocation as:

```rust
Fresh<TypeTag>::next()
```

Arena allocation is hot explicit state. A generic `Arena::push` is smaller, easier to inline, and makes lifetime ownership obvious.

### 8.2.8 Speculation effect: use checkpoints instead

Candidate testing needs rollback, but multi-shot effects are the wrong tool. Use one undo log and cleanup-backed checkpoint guards:

```text
mark = body.checkpoint()
candidate()
mark.commit()
```

If the candidate exits through a label or diagnostic failure, cleanup restores:

- inference assignments;
- emitted goals;
- scope bindings;
- scratch arena lengths;
- temporary diagnostics.

This uses Grandiose cleanup semantics without capturing arbitrary continuations.

## 8.3 Diagnostic architecture using effects and labels

Recommended pattern:

```rust
check_body(
    session: &mut CompilerSession,
    owner: DefId,
) -> BodyResult / {Report} {
    @body: BodyResult {
        ...
        ensure(valid, diagnostic, @body)
        ...
    }
}
```

Conceptually:

- `Report::emit` records recoverable facts;
- `@body` transfers a terminal body result;
- checkpoint cleanup restores speculative state;
- the outer phase handler canonicalizes and caps diagnostics;
- the host later renders them.

This avoids nested `Result<Result<...>>` plumbing while preserving explicit effect rows and lexical terminal destinations.

## 8.4 Effects for testing

Effects make compiler tests smaller when handlers substitute boundaries:

| Effect | Production handler | Test handler |
|---|---|---|
| `Report` | append/canonicalize | capture exact diagnostics |
| `CompileTrace` | no-op or counters | assert event sequence/budgets |
| `ProcessArgs` | host ABI | fixed array |
| `FileRead` | host ABI | in-memory package map |
| `FileWrite` | host ABI | capture bytes |
| `Diagnostic` | host renderer | capture structured output |
| `Budget` | configured limits | tiny deterministic limit to test exhaustion |

This reduces fake filesystem scaffolding and makes capability dependencies visible.

## 8.5 Effects and LOC reduction opportunities

Effects can remove code in these areas:

- repetitive diagnostic-vector parameters;
- repetitive phase-abort propagation;
- test-only host adapters;
- optional tracing conditionals;
- deeply nested host I/O plumbing.

They should **not** be expected to reduce code in:

- unification;
- type substitution;
- parser cursor state;
- arena allocation;
- PlaceFlow transfer functions;
- MIR editing;
- byte writing.

Those are data transformations, not capability boundaries.

## 8.6 Effect-specific optimizer obligations

For every compiler effect used in a hot path, add a control-plan assertion:

```text
Expected after specialization:
  no handler object allocation
  no dynamic protocol search
  no captured continuation
  no residual generic callable allocation
  direct branch/LEAVE or direct inlined operation
```

`--emit control-plan` should identify residual effect costs. A release bootstrap fails if a whitelisted hot helper remains dynamically handled without explicit approval.

---

# 9. Using source-defined control flow to reduce compiler code

Grandiose deliberately does not hardcode `if`, loops, `break`, `continue`, `return`, or short-circuit operators. That is a compiler-size advantage only if the compiler itself builds a disciplined control library and the optimizer fuses it.

The current [control-kernel design](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/docs/control-kernel.md) should become an implementation requirement, not an optional library experiment.

## 9.1 The control kernel

Build a small set of composable helpers.

### 9.1.1 Label-aware fold

```text
fold_until(range, initial, @stop, step)
```

The callback can:

- return the next accumulator;
- transfer a final result to `@stop`;
- propagate a diagnostic/terminal label;
- remain effect-polymorphic.

Uses:

- token scanning;
- candidate search;
- field traversal;
- first mismatch;
- verifier-table construction;
- canonicalization.

### 9.1.2 Stateful loop

```text
loop_state(initial, body)
```

Internally it may use the label-indexed effect described by the language core:

```rust
effect LoopControl<L, B, S>
where
    L: Label<B>,
{
    break(value: B) -> !
    continue(state: S) -> !
}
```

Derived helpers:

```text
while_state
repeat_until_stable
drain_worklist
for_each_index
find_first
find_unique
all
any
```

Each specialization must lower to a direct CFG loop with no runtime protocol lookup.

### 9.1.3 Structured walker

```text
walk(root, visitor)
```

Visitor result:

```text
Descend
Skip
Stop(value)
```

Uses:

- type terms;
- patterns;
- Core;
- MIR;
- dependency traces;
- canonical encodings;
- diagnostics.

Do not build a class-like visitor hierarchy. Use a small callable plus one stack representation. Provide specialized wrappers only when they remove repeated boilerplate.

### 9.1.4 Checkpoint and cleanup guards

Required guards:

```text
CursorCheckpoint
ScopeCheckpoint
InferenceCheckpoint
ArenaCheckpoint
DiagnosticCheckpoint
ByteBufCheckpoint
MirEditCheckpoint
```

Each guard records compact lengths/undo positions. Normal `commit` disarms rollback. Every other scope exit—including label transfer, diagnostic abort, or effect transfer—runs cleanup and restores state.

This is one of the strongest places to use Grandiose ownership and cleanup semantics directly.

### 9.1.5 Worklist and fixed-point runners

```text
drain_worklist(queue, visit)
repeat_until_stable(state, round)
solve_scc(graph, ...)
propagate_bits(seed, transfer)
```

Use the same runners for:

- import fixed points;
- trait goals;
- instance discovery;
- flow propagation;
- liveness;
- effect summaries;
- type-property SCCs;
- MIR optimization rounds.

### 9.1.6 Range builders

```text
with_range(arena, build)
try_with_range(arena, @fail, build)
with_section(writer, section_id, build)
with_record(writer, tag, build)
```

They replace repeated:

```text
start = arena.len()
...
count = arena.len() - start
checked integer conversions
rollback on failure
```

### 9.1.7 Early-exit helpers

Small helpers:

```text
ensure(condition, diagnostic, @fail)
bail(value, @destination)
some_or_leave(option, value, @destination)
ok_or_report(result)
find_or_report(...)
```

These are ordinary source definitions parameterized by `Label<T>` evidence. They must control-inline to direct transfers.

## 9.2 Parser toolkit

A deliberately small imperative parser toolkit should include:

```text
peek
eat
expect
mark
span_from
enter_delimited
attempt
choice
optional
many
separated
recover_until
commit
```

### Result discipline

Distinguish:

```text
NoMatch       // caller may try another production
Matched(T)    // success
Recovered(T)  // success with poison/diagnostic
Fatal         // cannot continue safely
```

Do not use a generic monadic parser framework. Do not allocate parser objects. Do not use multi-shot resumption for backtracking. All speculation uses the same cursor/arena/diagnostic checkpoint.

### Example: declaration alternative

```text
parse_item(cursor):
    @done: ParseItem {
        attempt(cursor, { => parse_function(cursor) }, @done)
        attempt(cursor, { => parse_struct(cursor) }, @done)
        attempt(cursor, { => parse_effect(cursor) }, @done)
        @done(report_expected_item(cursor))
    }
```

After control fusion this should be direct tests and branches with one shared rollback path.

## 9.3 Candidate selection toolkit

Type/call candidate testing repeats the same transaction pattern:

```text
for candidate in candidates:
    checkpoint
    seed constraints
    check contextual arguments
    solve local goals
    if viable:
        freeze answer summary
    rollback
select unique/equivalent answer
commit selected candidate once
```

Provide a focused helper:

```text
select_candidate(
    candidates,
    test,
    equivalent,
    explain_failure
)
```

This helper should own no semantic policy. It only manages:

- checkpoint;
- deterministic iteration;
- viable-answer collection;
- equivalence collapse;
- lazy failure summaries.

Uses include call overloads, receiver modes, `RunsIn` access modes, trait methods, contextual trailing blocks, and possibly literal defaults.

## 9.4 ControlSummary: structural optimization contract

Each specialized callable used as a control helper should receive a compiler-derived summary:

```text
ControlSummary {
    static_labels
    direct_label_exits
    callback_quantities
    callback_effect_rows
    tail_calls
    captures
    recursive_edges
    may_allocate_callable
    may_install_handler
    can_form_control_loop
}
```

The summary is derived from finalized Typed Core, not from function names or annotations that can lie.

The control inliner uses it to prove:

- label brands resolve to concrete destinations;
- callback invocation counts match quantities;
- helper recursion forms a reducible loop;
- environment captures can be eliminated;
- handler/control effects are statically scoped;
- cleanup order remains valid;
- code growth is within budget.

## 9.5 Control-plan diagnostics

Add:

```text
--emit control-plan
```

For each relevant specialization, print or encode:

- helper callable;
- concrete label destinations;
- callback bodies fused;
- loop backedges formed;
- residual handler operations;
- residual callable allocations;
- cleanup edges;
- reason fusion failed;
- estimated code growth.

Add compiler-development lints:

```text
CONTROL001 hot helper retained dynamic handler lookup
CONTROL002 label-generic helper could not resolve concrete destination
CONTROL003 avoidable closure allocation remains in parser/solver/MIR loop
CONTROL004 recursive control helper did not become a loop
CONTROL005 control fusion exceeds body budget
```

These are compiler-internal diagnostics, not user-language errors.

## 9.6 Expected high-value applications

### Lexer

- `while_state` for byte scanning;
- `find_first` for closing literal/comment boundaries;
- label exit on invalid UTF-8/literal;
- no iterator object or closure allocation after fusion.

### Scanner/header/body parsers

- `attempt`/`choice`;
- delimiter-aware `with_range`;
- checkpoint cleanup;
- `recover_until`.

### Resolution

- import `repeat_until_stable`;
- scope frame cleanup;
- `find_unique` ambiguity helper.

### Trait solver

- `drain_worklist`;
- cycle label;
- resource-budget early exit;
- lazy explanation walker.

### PlaceFlow

- sparse CFG worklist;
- branch checkpoint/rollback;
- projection walker;
- fixed-point propagation.

### MIR

- checked editor transaction;
- pass worklists;
- `repeat_until_stable` bounded optimization rounds.

### Emitter

- `with_section`;
- `with_record`;
- `ByteBufCheckpoint`;
- canonical-pool freeze walker.

## 9.7 Control abstractions to avoid

Do not introduce:

- dynamic iterator trait objects;
- a universal stream/transducer framework;
- monadic parser combinators;
- a generic mutable-state effect;
- multi-shot parser backtracking;
- compiler-recognized helper names;
- runtime label objects;
- an erased “control token” ABI;
- a generic recursive visitor with boxed callbacks for every node;
- helper libraries whose O0 behavior is so expensive that stage1 cannot compile stage2.

## 9.8 LOC-reduction expectation

The control kernel can plausibly remove hundreds to low thousands of normalized lines by centralizing:

- loops and worklists;
- early exits;
- rollback;
- parser choice;
- scope restoration;
- range construction;
- byte-writer patching;
- repetitive walkers.

The exact saving must be measured in the LOC ledger. A helper that adds more wrappers and diagnostics than it removes should be deleted.

---

# 10. Using new primitive functions responsibly

## 10.1 Authority model

The language may declare functions that are bound to machine primitives, but source text alone is not trusted. The current [`runtime_manifest.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/runtime_manifest.rs) follows the correct model:

1. the request selects an exact standard-library package identity;
2. the manifest names a finite primitive role;
3. the selector resolves to an exact declaration identity;
4. the compiler validates the exact signature and generic kinds;
5. Typed Core/MIR retains the sealed primitive role, not a source name;
6. bytecode emits the corresponding permanent primitive/opcode contract;
7. the Grandiose `vm_backend` verifier validates operands, types, effects, and feature bits;
8. the independent Rust `grvm` verifier applies the same permanent contract;
9. both the Grandiose interpreter and Rust VM implement the leaf where execution is exposed.

Adding a new primitive is therefore a cross-layer protocol change, not merely writing a special function declaration.

## 10.2 Primitive admission checklist

Every proposed primitive must specify:

| Field | Required content |
|---|---|
| Stable role/ID | Permanent, never reassigned |
| Source declaration | Exact package/module/Def identity selected by manifest |
| Generic kinds | Type/lifetime/effect-row/const slots in order |
| Signature | Exact parameters, result, and outward effects |
| Ownership | Move/copy/borrow behavior of every operand |
| Trapping | Whether and why it may trap |
| Determinism | Cross-host exact semantics |
| VM representation | Opcode or generic primitive encoding |
| Feature bit | Existing or new permanent G1 feature |
| Verifier rule | Operand/result state transformation |
| Runtime implementation | Grandiose `vm_backend` and Rust `grvm` code/tests |
| Source fallback | Reference implementation when feasible |
| Conformance | Positive, negative, malformed-artifact, and dual-verifier/interpreter differential tests |
| Size/performance case | Measured reason for trusted-surface expansion |

## 10.3 Primitive budget

Adopt a governance rule for compiler-specific primitives:

- initial target: **zero to twelve** new leaves beyond the standard library's required primitive table;
- each leaf must show either:
  - at least ~2% cold self-compile time improvement on the release benchmark; or
  - removal of at least ~200 normalized lines of unavoidable, low-level source implementation; or
  - elimination of a bootstrap dependency that cannot be implemented safely/portably in the source profile;
- composite high-level semantics do not qualify;
- every added primitive increases verifier/VM maintenance and bootstrap compatibility cost.

The numerical thresholds are review heuristics, not language law. They force evidence.

## 10.4 Strong candidates

### 10.4.1 BLAKE3 or canonical digest primitive

The current stage0's only external Cargo dependency is BLAKE3. Stable digests are used for request worlds, declaration identities, instance keys, artifacts, and bootstrap manifests.

Options:

1. implement BLAKE3 in the bootstrap standard library;
2. add a host-independent VM primitive family;
3. temporarily compute digests in the host envelope, which weakens compiler autonomy and can complicate semantic identity.

Recommendation: add a small pure digest primitive API, unless a compact source implementation meets the performance gate.

Potential API:

```text
digest.new() -> DigestState
digest.update(state: &mut DigestState, bytes: &Bytes) ->
digest.finish(state: DigestState) -> Digest
digest.bytes(parts: Slice<Bytes>) -> Digest
```

The state must have a fixed deterministic representation or be opaque with verifier-controlled ownership. It must have no host capability effect.

### 10.4.2 Bitset word operations

Flow, liveness, solver, and canonicalization frequently need bitset operations. Candidate leaves:

```text
bitset.or_changed(dst: &mut Array<u64>, src: &Array<u64>) -> Bool
bitset.and_not_changed(dst: &mut Array<u64>, src: &Array<u64>) -> Bool
bitset.popcount(words: &Array<u64>) -> usize
bitset.next_set(words: &Array<u64>, from: usize) -> Option<usize>
```

Prefer a very small set. `or_changed` is especially valuable because it combines mutation and fixed-point change detection.

### 10.4.3 Bulk byte/word memory operations

Potential leaves:

```text
bytes.copy_into(dst: &mut Array<u8>, at: usize, src: &Bytes) ->
array_u64.fill(dst: &mut Array<u64>, value: u64) ->
array_u64.copy(dst: &mut Array<u64>, src: &Array<u64>) ->
```

Only add these if existing array primitives cannot compile to efficient loops and profiling shows a bottleneck.

### 10.4.4 Byte writer fixed-width leaves

The G1 writer repeatedly emits and patches little-endian integers:

```text
bytebuf.push_u16_le
bytebuf.push_u32_le
bytebuf.push_u64_le
bytebuf.patch_u32_le
bytebuf.patch_u64_le
```

These may remain ordinary source wrappers over array operations. Promote them to primitives only if:

- wrapper/control fusion is inadequate;
- bounds checks dominate emission;
- the primitive significantly reduces writer code or time.

A single generic “write fixed integer” primitive may be less code than many widths, but the verifier/runtime signature must remain simple.

### 10.4.5 Integer scanning helpers

A low-level digit classifier or checked accumulation leaf could speed lexing:

```text
ascii.digit_value(byte: u8, radix: u8) -> Option<u8>
```

This is probably too small to justify a primitive because source code is compact. Measure before adding.

## 10.5 Candidates to reject

Do **not** primitive-ize:

- tokenization;
- parsing;
- delimiter matching;
- name resolution;
- type unification;
- trait solving;
- effect-row subtraction;
- pattern matching/decision DAGs;
- ownership/borrow checking;
- `if`, loop, return, break, continue;
- worklist iteration;
- MIR optimization;
- bytecode section construction;
- diagnostic formatting;
- sorting or hash-map policy as a compiler-semantic black box.

Those operations contain source-language semantics or policy and must remain inspectable Grandiose code.

## 10.6 Primitive wrappers

High-level APIs stay in source:

```text
Interner
HashMap
BitSet
ByteBuf
TextBuilder
SourceCursor
```

They may call small primitive leaves. This preserves:

- type safety;
- ownership policy;
- diagnostics;
- deterministic iteration;
- compiler-specific ergonomics;
- source-level testability.

## 10.7 Primitive addition workflow

For each new role:

1. add the normative role and permanent ID;
2. add the exact source declaration to the bootstrap standard library;
3. add manifest selector validation;
4. add Core/MIR primitive representation;
5. add bytecode encoding and feature requirement;
6. add verifier transfer rule;
7. add VM implementation;
8. add source fallback/reference oracle when feasible;
9. add positive execution tests;
10. add wrong-signature/wrong-identity manifest tests;
11. add malformed-bytecode verifier tests;
12. add stage0/self-host differential tests;
13. bump all relevant generation numbers;
14. verify old artifacts remain valid;
15. record benchmark and LOC evidence.

No name-based fallback is permitted at any step.

---

# 11. Feature-complete bootstrap standard-library profile

The earlier standard-library profile remains necessary but must be expanded to support the operational modules that are no longer omitted.

## 11.1 Layer 1 — manifest-bound leaves

Required low-level leaves include the frozen scalar, text, bytes, array, character, float, integer, control, and host-import surfaces already specified by the repository, plus any newly admitted compiler-support primitives such as BLAKE3 or bulk bitset/byte operations.

Rules:

- exact declaration identity and signature select a primitive;
- source spelling and declaration order do not grant authority;
- every leaf has deterministic VM semantics and verifier rules;
- public wrappers remain ordinary Grandiose source;
- stage0 and self-host use the same canonical manifest.

## 11.2 Layer 2 — ownership, results, control, effects

Required:

- `Result`, `Option`, result-based truth and operators;
- labels and branded propagation helpers;
- `fold_until`, `loop_state`, worklist/fixed-point control;
- affine checkpoint/rollback guards;
- `Slot`, `replace`, `swap`, `take`, and zero-use-safe helpers;
- exact quantity arithmetic;
- `Report`, cancellation, budget, tracing, and host capability effects.

All helpers used in hot paths need control-plan tests proving they fuse to direct control where expected.

## 11.3 Layer 3 — deterministic collections and text

The complete compiler requires:

- `Vec`, slices, arrays, deques, stacks;
- deterministic `HashMap`, `HashSet`, `MultiMap`, interner;
- `BTreeMap`/`BTreeSet` behavior **or** an API-compatible ordered-map view implemented by hash/dense storage plus explicit sorting;
- stable and unstable sort, binary search, partition, dedup;
- strings, bytes, text views, builders, formatting;
- bounded readers and writers;
- borrowed iteration and draining ownership behavior.

The goal is behavioral support, not a literal clone of Rust collection internals.

## 11.4 Layer 4 — compiler substrate

Required reusable types:

```text
Id<Tag>
IdRange<Tag>
IndexVec<Tag, T>
Arena<Tag, T>
BitSet<Tag>
SparseSet<Tag>
WorkQueue<Tag>
ScopeMap<Name, Binding>
UndoLog
Transaction<State, Journal>
CanonicalPool<Key, Tag>
ByteBuf
BoundedCursor
SchemaTable
FlowGraph
QueryFamily<Key, Value>
MemoTable<Key, Value>
RevisionStore
DependencyJournal
RetentionCounters
```

Each must have at least two real compiler consumers or be required for exact stage0 parity.

## 11.5 Layer 5 — operational/compiler-service toolkit

To port `operation`, `revision`, `dependency`, `query`, `artifact_cache`, `service`, and `output` compactly, the library needs:

- affine leases whose cleanup returns a reservation;
- owned cancellation cells and scoped cancellation checks;
- publication guards;
- typed transaction journals;
- revision pin handles;
- cache stats counters;
- bounded file reads;
- same-directory atomic write effect;
- deterministic JSON writer;
- canonical dependency sorting and graph walk;
- optional weak-registration semantics represented by explicit registration tokens and owner lifetimes rather than reference counting.

A single-threaded implementation is acceptable when it preserves stage0's observable lifecycle and the host serializes access. Rust synchronization types are not themselves part of the compiler language contract.

## 11.6 Layer 6 — VM schema, verifier, and interpreter support

The complete `vm_backend` port needs:

- packed word/byte readers;
- canonical section directory builder;
- opcode/type/feature schema tables;
- small verifier dataflow maps and work queues;
- checked register/type state arrays;
- arena-backed runtime values and frames;
- host-call effect dispatch;
- snapshot/copy/cleanup helpers for resumptions;
- exact numeric/float/text/array primitives through layer 1.

This layer remains ordinary Grandiose code except for admitted machine leaves.

## 11.7 Layer 7 — host capabilities

The outer compiler program uses:

```text
ProcessArgs
FileRead
FileWrite
AtomicFileWrite
DiagnosticWrite
VmHost
```

The Rust launcher/VM installs handlers. Semantic modules never receive ambient filesystem, cwd, clock, randomness, or network access.

## 11.8 Acceptance gate

Before module translation reaches `core`, the standard library must compile and test all foundational facilities. Before `query`/`revision` land, the operational toolkit must be green. Before `vm_backend`, the schema/bounded-reader/dataflow/runtime-value facilities must be green.

A compiler module may not introduce a private collection, parser checkpoint, memo table, binary reader, work queue, or control loop already promised by this profile.

# 12. Module-by-module execution plan

## 12.1 Phase A — freeze, inventory, and truthfulness infrastructure

### Deliverables

1. Pin the exact stage0 commit and toolchain.
2. Generate the 36-module inventory and public export manifest.
3. Assign every stage0 test to module owners.
4. Recover historical parity corpora without production probe code.
5. Define canonical snapshot formats for each module boundary.
6. Add normalized LOC, compile-time, memory, instance, query, cache, and control-plan dashboards.
7. Add a CI rule forbidding a “complete” module row from pointing at an ignored or partial test.
8. Add a semantic-fallback audit that scans the self-host harness and capabilities.

### Exit gate

The repository can answer, mechanically, which module/export/test/CLI/schema item remains unported.

## 12.2 Phase B — complete bootstrap standard library and private toolkit

Implement section 11 in dependency order. This is not a compiler-feature subset; it is the reusable substrate required to express all stage0 modules compactly.

Mandatory proof programs:

- arena/range/interner stress;
- transaction rollback through normal return, phase label, loop break/continue, cancellation, and diagnostic abort;
- query-family toy example with parent reuse and dependency traces;
- revision pin/retire toy example;
- cache envelope hostile-input corpus;
- VM schema encode/decode/verify toy bytecode;
- control-plan output showing direct fused loops and leaves.

### Exit gate

No planned module depends on an unimplemented basic collection, binary, transaction, worklist, query, or control facility.

## 12.3 Phase C — module translation protocol

Translate one module at a time in the order from section 7. Every module follows the same protocol:

1. **Contract extraction.** Freeze exports, constants, errors, fingerprints, and mapped tests.
2. **Facade skeleton.** Add the mirrored Grandiose module with no fake success behavior.
3. **Positive core.** Implement valid cases through shared toolkit.
4. **Negative/recovery core.** Implement all source/input/invariant/resource/cancellation failures.
5. **Boundary snapshot.** Add deterministic test-only encoding of the module's semantic product.
6. **Differential corpus.** Compare exact Rust and Grandiose cases.
7. **Integration.** Replace the probe's upstream mock with completed Grandiose dependencies.
8. **No-fallback audit.** Prove the module does not call Rust semantic code.
9. **Cleverness review.** Record shared mechanisms, effect/control use, primitive use, fused plan, and LOC.
10. **Completion.** Flip the module ledger row only after all mapped tests pass.

The next module may begin in a branch, but it cannot merge against a knowingly incomplete dependency without an explicit temporary test adapter that is absent from production.

## 12.4 Translation waves

The module order remains strictly module-gated, while waves describe dependency milestones.

### Wave 1 — fundamental values and request spine

Modules: `M01 diagnostic`, `M02 quantity`, `M03 identity`, `M04 operation`, `M05 request`, `M06 output`.

This wave establishes stable errors, quantitative arithmetic, identities, bounded/cancellable execution, world normalization, and host publication. It also proves the cleanup-guard design on real stage0 contracts.

**Wave gate:** byte-identical request/world/bootstrap fingerprints for all current request tests; exact budget/cancellation/publication behavior; atomic output corpus green.

### Wave 2 — structural source pipeline

Modules: `M07 source`, `M08 scanner`, `M09 header`.

Each module is completed independently. The header module includes the full current grammar from the start, not only the forms needed by the compiler source.

**Wave gate:** complete lexical/scanner/header corpora, exact spans and diagnostics, no missing header variant.

### Wave 3 — interfaces and names

Modules: `M10 interface`, `M11 module_graph`, `M12 fixity`, `M13 resolution`.

The interface cache is implemented now, including transactional misses and statistics. Resolution includes all import and occurrence/reference behavior.

**Wave gate:** multi-package/module/import/fixity/interface cache tests agree across cold and warm runs.

### Wave 4 — static term system

Modules: `M14 types`, `M15 signature`, `M16 coherence`, `M17 trait_solver`.

No “bootstrap trait subset” is allowed. The current stage0 associated types/effect rows/consts, HRTBs, GATs, negative impls, auto traits, methods, limits, and explanations all land before the wave closes.

**Wave gate:** complete type/signature/coherence/solver suite green, including resource and explanation parity.

### Wave 5 — syntax decisions and Typed Core

Modules: `M18 pattern`, `M19 body`, `M20 core`.

`core` may land through several internal PRs, but the module row remains incomplete until every `CoreKind`, effect/control/callable/refinement/reference rule is covered.

**Wave gate:** full stage0 frontend/static semantic corpus produces equivalent Typed Core or equivalent diagnostics.

### Wave 6 — ownership and instantiation

Modules: `M21 placeflow`, `M22 useflow`, `M23 escape`, `M24 mir_storage`, `M25 instance`.

The three flow facades share one graph but publish all current facts. Instance discovery is complete before MIR lowering depends on it.

**Wave gate:** ownership, borrowing, quantities, escapes, storage, continuation capture, cleanup roots, and generic reachability agree on the full corpus.

### Wave 7 — MIR

Module: `M26 mir`.

Translate the complete implemented module. Internally split model/lowering/editor/analysis/optimization/validation. Do not mark complete after O0 lowering alone.

**Wave gate:** all MIR tests, edit/validation tests, optimizer tests, source-storage tests, and Rust/Grandiose MIR snapshots agree.

### Wave 8 — runtime authority and complete VM backend

Modules: `M27 runtime_manifest`, `M28 vm_backend`.

This is a full verifier/interpreter port, not only emission. Implement schema-driven model/codec/verifier/executor. Run every candidate through both Grandiose and Rust verification.

**Wave gate:** all runtime-manifest, VM backend, storage erasure/identity, hostile artifact, execution, effect/resumption, and resource-limit tests agree.

### Wave 9 — bootstrap and incremental/service system

Modules: `M29 bootstrap`, `M30 dependency`, `M31 revision`, `M32 query`, `M33 artifact_cache`, `M34 service`.

This wave ports the full operational compiler. Query and revision behavior is not deferred until after self-hosting.

**Wave gate:** cold/warm/reused/red/green/cycle/incomplete/cancelled/retired/cache-corrupt/service outcome matrix agrees exactly.

### Wave 10 — public surface and CLI

Modules: `M35 lib`, `M36 main`.

Map every public export and command. The Rust launcher becomes generic: verify compiler, pass argv/capabilities, run VM, independently verify outputs.

**Wave gate:** public API inventory complete; all CLI and downstream integration tests green.

## 12.5 Full-system parity phase

Only after M36:

1. Run every stage0 unit and integration test against Rust.
2. Run the full Grandiose self-host parity corpus.
3. Run all compile modes and query/service inspection APIs.
4. Run cold and warm cache/revision sequences.
5. Run hostile source, cache, manifest, artifact, and resource corpora.
6. Compare canonical output bytes where defined.
7. Execute emitted programs in both Grandiose `vm_backend` interpreter and Rust `grvm` where practical.
8. Prove no Rust semantic fallback or hidden capability.
9. Produce a full parity report with zero missing/partial rows.

This is the first point at which a stage-1 compiler build is authorized.

## 12.6 Stage 1 build

Rust stage0 compiles the complete Grandiose module tree and complete bootstrap standard library. The result must:

- verify under Rust `grvm`;
- verify under the Grandiose `vm_backend` implementation when run as a test program;
- expose all stage0 modes and CLI behavior;
- pass representative external compile/run/inspect/IDE/query/cache scenarios;
- remain within the provisional bootstrap resource envelope.

## 12.7 Stage 2 and stage 3

Stage 1 compiles the exact same complete source world to stage 2. Stage 2 compiles it to stage 3. The source, runtime manifest, semantic options, codegen options, target, limits, and compiler mode are identical. Stage 2 and stage 3 must be byte-identical.

## 12.8 No feature-completion phase after bootstrap

After stage-2/stage-3 convergence, work may improve speed, memory, diagnostics, or architecture, and may add features that were not in the frozen stage0 baseline. It may not be used to finish baseline modules that were knowingly absent from stage 1.

# 13. Differential testing and parity program

## 13.1 Three ledgers

Maintain three machine-checked ledgers:

1. **Module ledger:** 36 rows, one per stage0 source module.
2. **Public API ledger:** one row per `lib.rs` export and one row per CLI command/option.
3. **Test ledger:** one row per Rust test/suite/case mapped to exact Grandiose execution.

Statuses are deliberately strict:

```text
missing
scaffolded
structural-parity
behavioral-parity
complete
```

Only `complete` counts toward first-release parity. “Partial” never becomes a release-green category.

## 13.2 Module boundary snapshots

Every module has a test-only canonical projection. Examples:

| Module | Snapshot |
|---|---|
| `request` | normalized world fields and fingerprint |
| `source` | token kinds/spans/text ranges/diagnostics/delimiter pairs/line positions |
| `scanner` | declaration shells and ranges |
| `header` | full parsed header tree and diagnostics |
| `interface` | definitions, header/public fingerprints, cache observations |
| `resolution` | targets, states, occurrences, references, fixities |
| `types` | canonical terms, substitutions, inference outcomes/errors |
| `trait_solver` | answers, evidence, terminal reasons, explanation tree |
| `core` | source-free Core, brands, environments, reference origins, diagnostics |
| flow modules | all published facts and diagnostics over stable binding/path identities |
| `instance` | keys, summaries, reachability and limit errors |
| `mir` | complete typed MIR, tables, edits, analyses, reports and diagnostics |
| `runtime_manifest` | bound roles/imports/signatures/digest/errors |
| `vm_backend` | candidate/verified models, canonical bytes, verification/execution outcomes |
| `dependency` | canonical traces and statuses |
| `revision` | metadata, pins, sessions, retention and collection reports |
| `query` | memo/reuse/recompute/dependency/retention/failure records |
| `artifact_cache` | envelope bytes and hit/miss/rejected/store traces |
| `service` | outcome, diagnostics, artifact/manifest/stats/inspection products |
| `main` | exit category, stdout/stderr/diagnostic JSON and files |

Raw arena IDs are normalized through stable owner/preorder schemes before cross-implementation comparison.

## 13.3 Exact source compile-domain parity

Build a manifest of every source case from:

- `crates/grandiose-stage0/tests`;
- semantic conformance submodules;
- current `crates/grandiose/tests` cases that exercise stage0-equivalent language semantics;
- historical self-host parity corpora with exact provenance;
- bootstrap standard-library and compiler source;
- hostile and resource-limit corpora.

For each case record:

```text
source segments and logical identities
request mode/options/limits/capabilities/runtime manifest
expected accept/reject
expected stable diagnostics
expected module boundary snapshots
expected artifact bytes or semantic result where applicable
mapped test function
```

The full compile domain, not just self-source, is a release gate.

## 13.4 Operational sequence parity

Single-request tests are insufficient for revision/query/cache modules. Add scripted sequences:

```text
R1 compile cold
R2 body-only edit
R3 public-interface edit
R4 fixity edit
R5 source removal/addition
R6 cancelled request
R7 resource-limited request
retire R1/R2 while pins exist
release pins and collect
load valid cache
load stale/corrupt/oversized/symlink cache
store success and store failure
```

Compare:

- revision metadata and parentage;
- query execution kind;
- dependency green/red/first-changed traces;
- interface and artifact cache stats;
- retention and retirement reports;
- published versus rolled-back products;
- final compiler outcomes.

## 13.5 VM backend dual differential

For every VM corpus case:

1. Build/obtain candidate bytes.
2. Decode and verify with Rust stage0/Rust `grvm`.
3. Decode and verify with Grandiose `vm_backend`.
4. Compare accepted model/fingerprint/canonical bytes or exact error category.
5. For executable cases, compare observable traces and results under both interpreters when supported.
6. Mutate/truncate/oversize the input and compare fail-closed behavior.

Neither verifier is allowed to “normalize” a noncanonical input into acceptance.

## 13.6 Diagnostic parity

Compare stable facts first:

- code;
- class;
- severity;
- primary and related source locations;
- named facts;
- explanation frames;
- input fingerprint;
- canonical ordering and deduplication;
- error-limit suppression count.

Text rendering may differ only where the baseline contract does not freeze exact wording. JSON field order and escaping should remain deterministic and stage0-compatible.

## 13.7 Metamorphic testing

Required transformations include:

- physical checkout path changes with identical logical paths;
- source input order perturbation before normalization;
- map hash seed/order perturbation;
- equivalent structural constant spelling;
- alpha-renaming of bound lifetimes/generics;
- harmless private body edits versus public interface edits;
- cache cold/warm parity;
- revision pin/retire timing variations;
- optional debug metadata present/absent;
- repeated stage builds.

Expected products must remain equal according to their semantic or exact identity contract.

## 13.8 Negative trust-boundary tests

Required attacks:

- primitive name shadowing;
- correct primitive name with wrong declaration identity;
- correct identity with wrong signature;
- forged host capability/symbol/signature;
- cache symlink and path escape;
- cache world/fingerprint/checksum mismatch;
- malformed bootstrap producer lineage;
- hostile section counts/offsets/operand lists/registers/cleanup plans;
- forged query dependency or recovered product;
- publication after cancellation;
- reuse across wrong revision/database;
- invalid diagnostic spans;
- semantic host fallback capability.

## 13.9 Coverage completion rule

A module or test row is complete only when the exact case runs in CI against both implementations and no ignored test, alternate fixture, nearby syntax, or host-computed semantic answer stands in for it.

The full-system parity report must show:

```text
modules:       36 / 36 complete
public exports: all mapped, all complete
CLI commands/options: all complete
tests/cases:   all complete
fallbacks:     0
ignored release gates: 0
```

# 14. Fixed-point bootstrap and release process

## 14.1 Canonical bootstrap input

Define a machine-readable source manifest listing:

```text
logical package
logical module path
content digest
source role:
    compiler
    bootstrap stdlib
    runtime declaration
entry definition
semantic options
codegen options
runtime manifest digest
```

The host assembles files in canonical logical order. Physical checkout paths are not semantic input.

## 14.2 Stage directories

Use explicit, disposable directories:

```text
bootstrap/stage0/
bootstrap/stage1/
bootstrap/stage2/
bootstrap/stage3/
```

Each contains:

```text
compiler.grbc
compiler.bootstrap-manifest
compile-request.digest
verification-report
stats.json or canonical stats text
```

Do not let a later stage discover an earlier artifact through cwd conventions.

## 14.3 Producer lineage

For stage N+1, request data includes the exact digest of stage N as producer. The host validates:

- stage ordinal;
- producer digest;
- source semantics digest;
- codegen digest;
- emitted artifact digest;
- exact bytes.

The Grandiose `bootstrap` module performs the same validation as stage0, and the Rust host independently recomputes all observable digests. A false compiler manifest therefore fails the second check.

## 14.4 Reproducibility modes

### Semantic reproducibility

Same source world and semantic options produce the same verified program meaning and semantic digest.

### Exact reproducibility

Same source world, codegen generation, target, optimization options, and canonical writer produce byte-identical `.grbc`.

Bootstrap fixed point requires exact reproducibility.

Debug/build metadata is omitted from fixed-point artifacts. If emitted for development, it must live in optional nonsemantic sections and not participate in program semantic digest.

## 14.5 Cross-host checks

Where supported, build S2/S3 on multiple hosts:

- Linux x86-64;
- another architecture or OS supported by the Rust VM.

Because G1 defines fixed-width scalar and `usize`/`isize` semantics, artifact bytes should remain identical when host-independent inputs match. Any host-specific nondeterminism is a release blocker.

## 14.6 Seed update policy

A new checked-in seed is accepted only when:

1. generated by the previous trusted seed or Rust stage0;
2. independently verified;
3. S2/S3 fixed point passes;
4. required parity and resource gates pass;
5. source and manifest digests are checked in;
6. change summary identifies compiler semantic/codegen generation changes;
7. previous seed remains available for rollback.

Do not update the seed merely because a branch compiler can compile itself once.

## 14.7 Default compiler launcher

A small Rust launcher should:

1. locate the bundled compiler artifact through installation metadata;
2. verify its digest and bytecode;
3. pass the original argv plus explicit host capabilities to the Grandiose `main`;
4. enforce CPU/memory/output limits;
5. run the compiler under `grvm`;
6. independently verify every emitted artifact and bootstrap manifest;
7. expose a recovery switch to Rust stage0.

CLI parsing, command selection, request construction, compiler-service calls, diagnostic formatting choices, cache policy, and atomic-output policy remain in the ported Grandiose modules. The launcher is capability and trust adaptation only.

## 14.8 Failure categories

Bootstrap tooling must distinguish:

```text
SeedMissing
SeedDigestMismatch
CompilerArtifactVerificationFailed
CompilerRuntimeFailure
CompilerReportedSourceErrors
CompilerInvariantFailure
CompilerResourceLimit
EmittedArtifactVerificationFailed
ManifestLineageMismatch
SemanticConvergenceMismatch
ExactByteMismatch
HostCapabilityDenied
```

Do not collapse these into “compilation failed.”

## 14.9 Release artifacts

A release should include:

- Rust `grvm`;
- Rust capability-only `grc` launcher;
- optional Rust `grc-stage0`;
- verified `compiler.grbc`;
- compiler bootstrap manifest;
- runtime primitive manifest;
- bootstrap stdlib source or packaged source bundle;
- exact source manifest;
- license and provenance information;
- commands to reproduce S1/S2/S3.

---

# 15. LOC budget and cleverness-only reduction program

## 15.1 Counting method

Count nonblank, non-comment Grandiose lines separately for:

- complete bootstrap standard library;
- private compiler toolkit;
- each mirrored stage0 module;
- production total;
- test-only probes/snapshots;
- generated schema data, if any.

Also record physical lines and bytes. Generated or table-derived code is not “free”; count the checked-in canonical source or data that maintains it.

## 15.2 Revised budget model

The repository's 9–12K target is retained as a stretch budget for the **semantic compiler core**. Full stage0 equivalence adds operational/query/cache/service and in-language VM backend behavior that the earlier target did not necessarily count.

| Component | Stretch normalized LOC | Review range | Notes |
|---|---:|---:|---|
| Shared compiler toolkit, excluding general stdlib | 1,500–2,500 | 3,000 | Arena/control/query/schema/wire/flow substrate |
| Request/identity/diagnostic/operation/output | 1,200–1,900 | 2,300 | Full behavior, no Rust synchronization transliteration |
| Source/scanner/header/interface/module/fixity/resolution | 3,000–4,500 | 5,200 | Complete grammar, caches, modules/imports |
| Types/signature/coherence/trait/pattern/body/Core | 5,000–7,500 | 8,500 | Full current static and Core semantics |
| Place/use/escape/storage/instance/MIR | 4,000–6,000 | 7,000 | Complete implemented MIR/editor/optimizer |
| Runtime manifest + complete VM backend | 3,500–5,500 | 6,500 | Emit/decode/verify/execute, schema-driven |
| Bootstrap/dependency/revision/query/artifact cache/service/lib/main | 2,800–4,500 | 5,200 | Full operational compiler system |
| **Production compiler total** | **17,000–23,000** | **24,000 architecture review** | No feature cuts to meet number |
| Bootstrap standard library | **7,000–11,000** | **12,000 review** | Expanded for query/cache/VM toolkit |

An outcome below 17K is welcome but not a reason to weaken readability or proofs. An outcome above 24K triggers a formal architecture review. A hard escalation at 28K requires identifying why the implementation is larger than the incomplete historical 21.4K prototype despite stronger shared substrate. Neither threshold permits deleting a baseline feature.

## 15.3 Allowed reduction sources

### Shared transaction semantics

One affine guard/journal implementation replaces bespoke rollback across parsers, inference, scopes, caches, query publication, package sessions, and outputs.

### Generic query family

One typed engine replaces repeated frame/memo/dependency/cancellation/budget/reuse/retention code. Module-specific query adapters define keys, evaluator, fingerprint, dependencies, and reuse validation.

### Ownership instead of synchronization scaffolding

The VM executes a compiler request with single-owner mutable state. Replace `Arc`, `Weak`, `Mutex`, and atomics where they are implementation details, while retaining all lifecycle observations. Concurrent hosts isolate or serialize compiler instances.

### One mixed-kind term toolkit

Common folds, substitution, canonical encoding, kind validation, and inference eliminate repeated trees across headers, signatures, solver, instances, Core, MIR metadata, runtime manifests, and VM records.

### One definition and namespace substrate

Definition identity, namespaces, visibility, module ownership, imports, fixities, runtime leaves, occurrences, and references share tables and search/ambiguity logic.

### One flow graph

PlaceFlow, UseFlow, EscapeFlow, MIR import, cleanup, and storage erasure consume one place/control/provenance substrate.

### One VM schema

Section, type, opcode, feature, primitive, operand, encoder, decoder, verifier, and interpreter metadata comes from one checked schema rather than parallel match forests.

### Source-defined control

Labels, loop effects, effect-polymorphic walkers, checkpoints, worklists, and propagation helpers remove manual recursion and nested result plumbing. Control-plan tests require hot abstractions to fuse.

### Manifest-bound primitives

BLAKE3, bulk bytes/words, bitset operations, and other admitted leaves replace low-level loops while preserving high-level compiler semantics in source.

### Lazy diagnostic/explanation materialization

Store compact facts and construct strings or deep explanation trees only when published/inspected.

### Module facades over shared engines

A mirrored module may be a thin typed facade rather than a duplicate implementation. The facade's presence preserves traceability and API parity.

### Test protocol outside production

Snapshots, numeric compatibility tags, and phase probes remain test-only. This is code separation, not feature removal.

## 15.4 Forbidden “reductions”

The following do not count as size wins:

- removing a stage0 module;
- compiling only the self-host source subset;
- dropping a request mode or CLI command;
- moving a query/cache/revision decision to Rust;
- using Rust stage0 as a semantic callback;
- omitting VM decode/verify/execute behavior;
- weakening diagnostics, cleanup, ownership, effects, or verifier checks;
- marking a test “covered” through a nearby case;
- leaving a feature behind a post-bootstrap TODO;
- hiding large semantic logic inside an unreviewed primitive.

## 15.5 Per-module review questions

For every completed module ask:

1. Which stage0 behavior is represented?
2. Which shared engines replace repeated Rust machinery?
3. Are all exported errors and resource cases present?
4. Did any Rust implementation detail accidentally become public Grandiose complexity?
5. Could a generic fold/schema/transaction remove another local traversal?
6. Do effects/labels eliminate control plumbing without widening authority?
7. Do hot control helpers fuse?
8. Does a new primitive pass the permanent-contract review?
9. Is every LOC reduction behavior-preserving?
10. Did downstream module snapshots remain green?

## 15.6 Size is subordinate to completeness

The project should prefer a 22K complete, clean, convergent compiler over a 12K compiler with missing query, cache, VM, or language behavior. The budget exists to force architectural intelligence, not to redefine the product.

# 16. Performance and memory plan

## 16.1 Release target

The repository's release gate is:

- cold stage-2 compiler;
- compile compiler source and bootstrap standard library;
- O2;
- less than 120 seconds;
- less than 4096 MiB.

Treat this as a hard architecture target from the beginning.

## 16.2 Required statistics

`--stats` should emit deterministic counters:

```text
source bytes
tokens
definitions
interned names
canonical terms by kind
trait goals/steps/cache hits
query executions/memo hits/reuse/recompute/cycles
dependency nodes/edges/green/red/cycle/incomplete
revisions retained/retired/pinned and snapshot pins
interface/artifact cache hits/misses/rejected/stores
request/package sessions and staged products
candidate tests
Core nodes peak/current
flow points/events/iterations
move paths/loans/regions
instances total/per definition
MIR blocks/locals/operations before/after each pass group
control fusions attempted/succeeded
residual dynamic handlers/callables in hot helpers
output strings/types/constants/functions/bytes
VM decode words/records, verifier states/steps, interpreter frames/steps
bootstrap manifests encoded/validated and lineage comparisons
peak arena entries by lifetime tier
phase timings
process peak memory (host-provided when available)
```

Stats are not part of bootstrap artifact identity unless explicitly included in a nonsemantic report.

## 16.3 Memory controls

- one-body AST/Core scratch reset;
- frozen generic Core only when reachable;
- per-body solver tables;
- flat range storage;
- bitsets for dense universes;
- sparse sorted vectors for sparse facts;
- reusable buffers/work queues;
- render diagnostics after error cap;
- release MIR scratch after function emission when whole-program passes do not require it;
- avoid cloning interfaces into solver objects;
- avoid per-node strings;
- avoid unnecessary duplicated decoded VM records; retain only the complete stage0-visible candidate/verified views and compact verifier/runtime state required by `vm_backend`.

## 16.4 Time controls

- O(1) delimiter jumps;
- hash-based name/index lookup;
- direct scope map with restoration journal;
- tabled trait solving;
- indexed compiler-generated evidence fast paths;
- demand-driven instance worklist;
- feature bits to skip MIR pass families;
- bounded optimization rounds;
- canonical sorting only at output boundaries;
- mutable byte writer;
- digest/bitset primitives only when measured.

## 16.5 Benchmark ladder

Run increasingly complete cold benchmarks:

1. lexer/scanner corpus;
2. interface-heavy generic/trait corpus;
3. effect/control corpus;
4. ownership-heavy corpus;
5. backend emission corpus;
6. revision/query/dependency/cache sequence corpus;
7. VM decode/verify/execute hostile and normal corpus;
8. bootstrap toolkit;
9. compiler frontend source;
10. full compiler source at O0;
11. full compiler source at O2;
12. cold/warm incremental service sequence;
13. S1→S2;
14. S2→S3.

Record baseline and delta per merged phase.

## 16.6 Performance stop conditions

Stop feature work and investigate architecture when:

- peak memory grows with total body AST size;
- solver steps depend strongly on declaration traversal order;
- one helper creates large residual handler/callable allocation counts;
- an optimization pass needs more than three fixed-point rounds;
- output canonicalization dominates compile time;
- repeated standard-library specialization dominates;
- stage1 self-compile cannot fit an interim 2× final resource envelope;
- a new primitive is proposed without a profile.

# 17. Risk register

| Risk | Likelihood | Impact | Early warning | Mitigation | Release condition |
|---|---|---|---|---|---|
| Module mirror becomes line-by-line transliteration | High | High | Grandiose structs/functions mirror Rust synchronization and helper layout | facade parity plus shared-engine review; per-module LOC/control report | same behavior with demonstrably fewer mechanisms |
| Feature omission disguised as architecture | High | Critical | module marked “host-owned,” “later,” or “not needed” despite stage0 export/test | mandatory 36-module/API/test ledgers | zero missing/partial rows |
| Hybrid Rust fallback becomes production | Medium | Critical | Grandiose phase calls host for semantic product | capability audit and no-fallback tests | no semantic fallback capability or callback |
| Query/revision semantics silently simplified | Medium/High | High | only one-shot compilation tests exist | scripted multi-revision/cold-warm/cancel/retire sequences | operational parity suite green |
| Complete VM backend is too large | High | High | duplicated type/opcode/codec/verifier/interpreter match forests | single VmSchema, checked views, transfer-rule engine | full VM parity inside agreed module budget |
| Grandiose and Rust verifiers disagree | Medium | Critical | one accepts bytes the other rejects | dual differential hostile corpus on every change | identical acceptance/error categories for baseline corpus |
| Old prototype size repeated without parity | Medium | High | approaches historical LOC while module ledger incomplete | per-module completion and size dashboard | complete feature set within revised review ceiling |
| Bootstrap stdlib incompleteness | High | High | compiler modules add private collections/query/binary helpers | finish layer gates first; prohibit local duplicates | all modules use approved stdlib/toolkit |
| Name-based primitive authority | Medium | Critical | selector chosen by spelling/order | exact identity/signature schema and malicious shadow tests | no name/position fallback |
| Primitive creep hides compiler semantics | Medium | High | parser/solver/verifier policy proposed as primitive | permanent primitive admission process | every primitive low-level, finite, specified, measured |
| Quantity multiplication outruns seed integer support | Medium | High | source quantity port requires checked `u64` multiplication/division but stage0 has no corresponding MIR/VM lowering | add and differentially test checked `u64` arithmetic end-to-end in stage0 before binding a quantity primitive | M02 multiplication is translated with exact overflow and zero-times-infinite behavior, never a repeated-addition fallback |
| Source-defined control fails to fuse | High | High | handlers/closures/recursion remain in hot loops | ControlSummary, control-plan, lints and benchmark gates | approved direct control shapes |
| Effects become ambient mutable state | Medium | High | broad effect rows on every helper | explicit contexts; narrow scoped effects | effect catalog remains auditable |
| Transactions diverge between subsystems | Medium | High | parser/cache/query rollback bugs differ | one transaction kernel and failure-injection corpus | all publication/rollback cases pass |
| Flow facades reconstruct facts separately | High | Critical | three walkers/maps drift | shared FlowGraph and cross-view assertions | one place/control/provenance substrate |
| MIR port stops at O0 | Medium | High | module called complete without editor/optimizer/validation parity | M26 gate includes all exports/tests | complete MIR ledger green |
| Diagnostic adapters become incomplete | Medium | High | new Rust variant lacks Grandiose mapping | exhaustive manifest/test generated from baseline | zero unmapped variants/codes |
| Cache hit trusted without verification | Low/Medium | Critical | warm build bypasses decode/verifier | cache module gate and hostile entries | every hit fully validated |
| Retention leak | Medium | High | retired revisions remain pinned/cache-owned | retention counters and stress sequences | bounded collection after pin release |
| Nondeterministic query/cache ordering | Medium | High | cold/warm or hash perturbation changes outputs | explicit canonicalization and perturbation tests | deterministic observations/artifacts |
| Generic instance explosion | High | High | self-compile specialization count spikes | limits, summaries, source discipline, profiling | self-compile within resource gate |
| Ownership semantics weakened for size | Medium | Critical | missing partial move/cancel/drop cases | full flow/MIR/VM parity corpus | all baseline ownership cases green |
| CLI logic duplicated in Rust launcher | Medium | Medium/High | launcher parses commands or runtime selectors | argv pass-through architecture | Grandiose M36 owns command behavior |
| Stage1 compiles itself but not users | Medium | Critical | narrow self-source masks missing features | full external compile-domain gate before S1 | representative and complete corpus green |
| Stage2/3 converge on wrong source world | Low/Medium | Critical | manifests omit module/cache/runtime inputs | dual bootstrap validation | exact source/codegen/producer commitments |
| Cross-host byte drift | Medium | High | host order/path/width affects output | fixed widths, canonical pools, cross-host tests | identical supported-host bytes |
| LOC pressure causes hidden omissions | Medium | Critical | TODOs or host adapters added near threshold | completeness outranks budget; formal review | no feature cut accepted |

## 17.1 Highest-priority mitigations

Implement these first:

1. machine-checked module/API/test ledgers;
2. semantic-fallback capability audit;
3. exact runtime-manifest authority tests;
4. generic transaction/query/schema toolkit prototypes;
5. dual Rust/Grandiose VM verifier harness;
6. normalized LOC and control-plan dashboard.

These make false progress difficult before the expensive modules begin.

# 18. Recommended pull-request sequence

The sequence is intentionally module-granular. A very large module may use several internal PRs, but only the final PR flips its module row to complete. PRs may be developed concurrently after dependencies stabilize; merge order remains the order below unless the ledger records a safe reordering.

## 18.1 Foundation PRs

| PR | Scope | Gate |
|---:|---|---|
| 1 | Freeze baseline, reconcile docs, generate module/API/test/CLI/schema inventories | clean-checkout inventory reproducible |
| 2 | Restore exact historical corpora into test-only harness | truthfulness test green |
| 3 | Add LOC/resource/control-plan/fallback dashboards | CI publishes metrics |
| 4 | Bootstrap stdlib collections/text/formatting completeness | stdlib foundational corpus green |
| 5 | Arena/range/cursor/transaction/control/worklist toolkit | proof programs green |
| 6 | Canonical/wire/schema/query/flow toolkit | toy query/revision/cache/VM proofs green |

## 18.2 One completion PR per stage0 module

| PR | Module | Required result |
|---:|---|---|
| 7 | M01 `diagnostic.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 8 | M02 `quantity.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 9 | M03 `identity.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 10 | M04 `operation.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 11 | M05 `request.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 12 | M06 `output.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 13 | M07 `source.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 14 | M08 `scanner.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 15 | M09 `header.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 16 | M10 `interface.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 17 | M11 `module_graph.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 18 | M12 `fixity.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 19 | M13 `resolution.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 20 | M14 `types.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 21 | M15 `signature.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 22 | M16 `coherence.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 23 | M17 `trait_solver.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 24 | M18 `pattern.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 25 | M19 `body.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 26 | M20 `core.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 27 | M21 `placeflow.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 28 | M22 `useflow.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 29 | M23 `escape.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 30 | M24 `mir_storage.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 31 | M25 `instance.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 32 | M26 `mir.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 33 | M27 `runtime_manifest.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 34 | M28 `vm_backend.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 35 | M29 `bootstrap.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 36 | M30 `dependency.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 37 | M31 `revision.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 38 | M32 `query.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 39 | M33 `artifact_cache.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 40 | M34 `service.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 41 | M35 `lib.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |
| 42 | M36 `main.rs` | Module-complete gate; exact mapped tests; no fallback; LOC/control report |

Large-module rule: `core.rs`, `mir.rs`, and `vm_backend.rs` may use preparatory PRs for private submodules, but their public module rows remain incomplete until the corresponding completion PR. No preparatory PR may advertise feature parity.

## 18.3 Full-system and bootstrap PRs

| PR | Scope | Gate |
|---:|---|---|
| 43 | Full stage0-equivalence run and zero-gap parity report | 36/36 modules, all exports/CLI/tests complete |
| 44 | Rust stage0 builds complete stage 1 | S1 dual-verifies and passes external corpus |
| 45 | Stage 1 builds complete stage 2 | S2 dual-verifies; all modes operational |
| 46 | Stage 2 builds complete stage 3 | S2/S3 exact bytes |
| 47 | Resource, hostile-input, cache/revision, cross-host hardening | release gates green |
| 48 | Default launcher cutover | generic launcher uses verified complete compiler; rollback documented |

## 18.4 Merge rules

A module completion PR must include:

- baseline contract excerpt;
- export mapping changes;
- exact test-ledger changes;
- positive/negative/resource/cancellation evidence;
- differential snapshot results;
- no-fallback audit;
- normalized LOC delta;
- control-plan output for new hot helpers;
- primitive authority evidence if applicable;
- list of shared-toolkit consumers;
- downstream regression results.

No PR may reduce the baseline by deleting a test, changing a row to “not applicable,” moving logic into the Rust launcher, or weakening a verifier/cache/query rule to get green.

# 19. Immediate next actions

1. Rename the existing plan as superseded and check in this revised full-port plan.
2. Record baseline rolls in `docs/self-host-stage0/baseline.toml`; the active behavioral baseline is `cfeab4b58d60754a70c819fdda25a1f1024907af`.
3. Generate the 36-module inventory and `lib.rs` public export inventory.
4. Inventory all `main.rs` commands/options and all schema/generation constants.
5. Assign every `grandiose-stage0` test to module owners; import historical exact parity cases.
6. Add a CI truthfulness rule: no complete row may reference ignored or non-executing coverage.
7. Define the mirrored `self-host-stage0/src` tree and module facade convention.
8. Prototype the transaction kernel on parser rollback, budget lease, and query publication.
9. Prototype the generic query family and revision store on a small semantic toy query.
10. Prototype `VmSchema` by expressing a small subset of type/opcode encode/decode/verify/execute rules once.
11. Decide and specify the BLAKE3 primitive boundary so identity parity is available before M03.
12. Complete the expanded bootstrap standard-library ledger before source module translation begins.
13. Start M01 `diagnostic.rs`; do not begin with `core.rs` or `vm_backend.rs` before the shared substrate proves itself.
14. Establish a monthly architecture review comparing module completion, LOC, control fusion, query/cache behavior, verifier parity, and resource trends.

The first near-term milestone should read:

> The complete M01–M06 foundation modules execute in Grandiose, match Rust stage0 on all mapped normal/error/cancellation/resource cases, use the real transaction and host-effect substrate, and introduce no semantic fallback.

# 20. Appendices

## Appendix A — Proposed compiler-internal effect catalog

| Effect | Operations | Where handled | Hot-path expectation |
|---|---|---|---|
| `Report` | `emit(Diagnostic)` | phase/session boundary | inline append; no dynamic lookup |
| `CompileTrace` | `event(TraceEvent)` | compile entry | erased/no-op when disabled |
| `Budget` | coarse `charge`, terminal exhaustion | session/body/optimizer boundary | local counters in inner loops |
| `AbortPhase<E>` | terminal `stop(E)` | only when label threading is worse | direct transfer after specialization |
| Host `ProcessArgs` | argument access | outer application | host import |
| Host `FileRead` | read logical input file | outer application | host import |
| Host `FileWrite` | write verified output | outer application | host import |
| Host `Diagnostic` | render structured diagnostic | outer application | host import |

Rejected ambient effects:

- source map lookup;
- arena allocation;
- scope mutation;
- inference assignment;
- map access;
- MIR editing;
- byte-buffer mutation.

## Appendix B — Proposed control helper catalog

| Helper | Primary compiler uses | Required fused shape |
|---|---|---|
| `fold_until` | scanning, search, validation | loop + direct exit |
| `loop_state` | generic state loops | CFG loop |
| `while_state` | lexer/parser/MIR | CFG loop |
| `drain_worklist` | imports, solver, flow, instances | queue loop |
| `repeat_until_stable` | fixed points, optimizer | bounded loop |
| `walk` | terms, patterns, Core, MIR | explicit stack loop |
| `attempt` | parser/candidate speculation | branch + rollback cleanup |
| `choice` | grammar alternatives | direct branch chain |
| `recover_until` | parser recovery | scan loop |
| `with_range` | arena ranges | start/end arithmetic |
| `with_section` | bytecode writer | direct writes/patch |
| `ensure` | validation | conditional direct leave |
| `some_or_leave` | option propagation | pattern branch + leave |
| `find_unique` | resolution/candidates | loop + ambiguity branch |

## Appendix C — Primitive proposal scorecard

Score each candidate 0–3:

| Criterion | 0 | 1 | 2 | 3 |
|---|---|---|---|---|
| Compile-time impact | none | <1% | 1–2% | >2% |
| Source LOC removed | <25 | 25–75 | 75–200 | >200 |
| Bootstrap necessity | no | convenience | difficult source fallback | no safe/practical fallback |
| Trusted complexity | large | medium | small | tiny |
| Verifier clarity | complex state | moderate | simple | trivial |
| Cross-host determinism | uncertain | constrained | specified | obvious |
| Reuse | one site | one subsystem | multiple compiler subsystems | stdlib-wide |

Require a high total and no zero in determinism/verifier clarity.

## Appendix D — Example canonical source world

```text
Package compiler
    self-host-stage0/src/main.glorious
    self-host-stage0/src/lib/lib.glorious
    self-host-stage0/src/request/request.glorious
    self-host-stage0/src/source/source.glorious
    ... all mirrored stage0 modules in canonical logical-path order
Package std
    std/core/...
    std/collections/...
    std/compiler/...
Runtime manifest
Semantic options
Codegen options
Entry: compiler::main
```

The manifest records logical paths and content digests. The physical repository location does not participate.

## Appendix E — Definition of architectural regression

Any of the following triggers an architecture review:

- fourth persistent semantic IR;
- whole-program body AST retention;
- duplicate semantic/backend type tree;
- separate callable hierarchy for handlers/resumptions;
- separate brand arenas by feature;
- separate linear/affine/resumption quantity checkers;
- separate ownership ledgers for environments;
- separate Core walkers for place/use/escape with their own CFGs;
- a second query/revision/cache lifecycle implementation outside the mirrored modules or generic query substrate;
- production phase CLIs/snapshot encoders;
- primitive authority by source name or declaration position;
- compiler-recognized standard-library control names;
- runtime label objects or dynamic label search;
- normalized production compiler LOC above the revised 24K review threshold without an approved full-parity architecture review.

## Appendix F — Review checklist for each phase

### Semantics

- [ ] Exact stage0 behavior identified.
- [ ] No excluded semantic case silently dropped.
- [ ] Poison/recovery cannot reach executable artifact.
- [ ] Resource limits are structured.
- [ ] Ownership/effect/cleanup invariants documented.

### Representation

- [ ] Fact has one semantic owner.
- [ ] No parallel numeric tag beside enum.
- [ ] Typed IDs stay in owning arena.
- [ ] Variable ranges are flat.
- [ ] Body-local data is released.
- [ ] Output ordering is explicit.

### Language-specific leverage

- [ ] Effects are narrow capabilities.
- [ ] Labels replace repetitive terminal propagation where useful.
- [ ] Cleanup guards replace manual rollback.
- [ ] Control helper has fused plan.
- [ ] Quantity kernel is reused.
- [ ] Callable/brand kernels are reused.
- [ ] New primitive, if any, passes admission process.

### Testing

- [ ] Exact corpus cases added.
- [ ] Strongest boundary compared.
- [ ] Negative/resource cases included.
- [ ] Independent VM verifies output.
- [ ] O0/O2 compared where relevant.
- [ ] Parity ledger updated truthfully.

### Size/performance

- [ ] Normalized LOC delta recorded.
- [ ] Phase time and peak entries recorded.
- [ ] No production probe code.
- [ ] No unmeasured primitive.
- [ ] No unexpected retained allocation/control effect.

## Appendix G — Source references

Current pinned stage0 module sources:

- [`artifact_cache.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/artifact_cache.rs)
- [`body.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/body.rs)
- [`bootstrap.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/bootstrap.rs)
- [`coherence.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/coherence.rs)
- [`core.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/core.rs)
- [`dependency.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/dependency.rs)
- [`diagnostic.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/diagnostic.rs)
- [`escape.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/escape.rs)
- [`fixity.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/fixity.rs)
- [`header.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/header.rs)
- [`identity.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/identity.rs)
- [`instance.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/instance.rs)
- [`interface.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/interface.rs)
- [`lib.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/lib.rs)
- [`main.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/main.rs)
- [`mir.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/mir.rs)
- [`mir_storage.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/mir_storage.rs)
- [`module_graph.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/module_graph.rs)
- [`operation.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/operation.rs)
- [`output.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/output.rs)
- [`pattern.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/pattern.rs)
- [`placeflow.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/placeflow.rs)
- [`quantity.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/quantity.rs)
- [`query.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/query.rs)
- [`request.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/request.rs)
- [`resolution.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/resolution.rs)
- [`revision.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/revision.rs)
- [`runtime_manifest.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/runtime_manifest.rs)
- [`scanner.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/scanner.rs)
- [`service.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/service.rs)
- [`signature.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/signature.rs)
- [`source.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/source.rs)
- [`trait_solver.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/trait_solver.rs)
- [`types.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/types.rs)
- [`useflow.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/useflow.rs)
- [`vm_backend.rs`](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/crates/grandiose-stage0/src/vm_backend.rs)

Normative design:

- [Language core](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/glorious-branded-environment-core-spec.md)
- [Compiler architecture](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/docs/architecture.md)
- [Size/speed review](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/docs/size-speed-review.md)
- [Control kernel](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/docs/control-kernel.md)
- [MIR design](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/docs/mir-design.md)
- [G1 bytecode](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/docs/bytecode.md)
- [Bootstrap standard library](https://github.com/MalekiRe/glorious/blob/02ced7ed1894acfd54b0766e2d718b699fc31a8c/docs/std-lib.md)

Historical postmortem:

- [Retired self-host architecture](https://github.com/MalekiRe/glorious/blob/a62a08316f5b0c81f74c2a975fe7bd9826157a90/self-host/ARCHITECTURE.md)
- [Retired line counter](https://github.com/MalekiRe/glorious/blob/a62a08316f5b0c81f74c2a975fe7bd9826157a90/self-host/count-lines.sh)
- [Retired parity audit](https://github.com/MalekiRe/glorious/blob/a62a08316f5b0c81f74c2a975fe7bd9826157a90/docs/selfhost-parity-audit.md)

---

## Appendix H — Module parity ledger template

```text
module: MNN name.rs
baseline commit:
Grandiose facade:
public exports:
upstream module dependencies:
downstream consumers:
semantic products:
stable identities/fingerprints:
diagnostics/errors:
resource/cancellation cases:
normal tests:
negative tests:
incremental/sequence tests:
snapshot encoder:
Rust oracle entry:
Grandiose entry:
no-fallback evidence:
control-plan evidence:
primitive authority evidence:
normalized LOC:
status: missing | scaffolded | structural-parity | behavioral-parity | complete
reviewers:
```

## Appendix I — Cleverness review checklist

A proposed LOC reduction is acceptable only when all answers are yes:

- Does the Grandiose module still expose the complete stage0 behavior?
- Is the reduction replacing duplicated machinery rather than a semantic case?
- Is the shared abstraction used by at least two real modules or required by parity?
- Are stable identities, diagnostics, limits, and failure categories preserved?
- Does the differential corpus still exercise the exact original cases?
- Does any effect remain scoped and capability-auditable?
- Does any control helper fuse or have an accepted cost model?
- Is any primitive finite, low-level, manifest-bound, verifier-specified, and non-forgeable?
- Is the Rust host still only a capability/trust adapter?
- Does the module remain independently testable through its mirrored facade?


---

## Final recommendation

Translate the frozen Rust stage0 **one module at a time and in full**. Preserve each module's public responsibility, diagnostics, identities, resource behavior, tests, and operational contracts through a mirrored Grandiose facade. Do not call any intermediate subset a self-hosted compiler, and do not use Rust semantic fallbacks to close gaps.

Make the result smaller by being structurally better:

- one Callable/Brand/Quantity/PlaceFlow semantic substrate;
- one transaction/publication model;
- one generic query engine and revision store;
- one mixed-kind term/substitution engine;
- one definition/namespace/index substrate;
- one VM schema feeding encode, decode, verify, execute, runtime manifest, and CLI help;
- effects and labels for diagnostics, cancellation, rollback, worklists, and early exit;
- manifest-bound primitives only for finite low-level operations;
- explicit single-owner state instead of transliterated Rust synchronization;
- test-only snapshots and probes kept out of production.

Success means all 36 module rows, every `lib.rs` export, every CLI command/option, and every mapped test are complete before stage 1; stage 1 is already stage0-equivalent; Grandiose and Rust verification agree; no semantic fallback exists; stage 2 and stage 3 are byte-identical; the full compile-domain and operational corpora pass; and the complete system meets the revised LOC and resource review gates without deleting any baseline feature.
