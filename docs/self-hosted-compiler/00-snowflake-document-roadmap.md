# Self-Hosted Glorious Compiler — 32-Document Snowflake Roadmap

I would split the design into **32 implementation documents**, organized as **eight volumes of four documents each**.

That is enough separation to avoid enormous “god documents,” while keeping closely related mechanisms together. Fewer than roughly 25 documents would force unrelated concerns—such as caching, invalidation, query execution, and identity—into oversized chapters. Much more than 35 would fragment the design so heavily that its central invariants would become difficult to follow.

The existing snowflake-stage-one document remains the **root synopsis**. These 32 documents become its next expansion layer.

# Volume I — The Compiler’s System Spine

### 01. Architecture and Trust Boundaries

Defines the responsibilities of `grand`, `grc`, the compiler database, the standard library, the bytecode verifier, `grvm`, the supervisor, editor tooling, and external package infrastructure.

It should settle:

- which components may access the filesystem, process environment, or network;
- which components are trusted;
- which inputs must be hermetic;
- which representations cross component boundaries;
- which part owns package orchestration versus language semantics;
- how compiler-as-library differs from compiler-as-command.

### 02. Compilation Inputs, Revisions, and Session Ownership

Defines the complete compilation request and the lifetime of compiler state.

It should describe:

- source snapshots and revisions;
- package and workspace inputs;
- dependency interface inputs;
- target and capability manifests;
- `CompilerDatabase`, `CompilerSession`, `BodyContext`, `LoweringContext`, and `EmissionContext`;
- snapshot isolation;
- how editor revisions coexist;
- what may survive between requests.

### 03. The Typed Query Engine

Defines the compiler’s core computation model.

It should specify:

- typed query keys and result types;
- memoization;
- automatic dependency recording;
- nested query execution;
- query cycles;
- fixed-point queries;
- provisional IDE results;
- cancellation;
- poisoning and recovery;
- query statistics;
- `why_recompiled`;
- query tracing and inspection.

This will likely become the most foundational implementation document.

### 04. Stable Identity, Interning, and Typed Arenas

Defines all compiler identity systems.

It should distinguish:

- persistent `PackageKey`, `ModuleKey`, `DefKey`, `BodyKey`, and `InstanceKey`;
- body-local `ExprId`, `LocalId`, `PlaceId`, `LoanId`, and `BlockId`;
- stable syntax anchors;
- identity across edits;
- string, type, effect-row, const, and goal interning;
- typed arena storage;
- canonicalization at persistence boundaries;
- prevention of accidental raw-integer identity mixing.

# Volume II — Incrementality and Operational Safety

### 05. Dependency Tracking and Invalidation

Defines how the compiler decides which facts remain valid after a change.

It should cover:

- source dependencies;
- interface versus implementation dependencies;
- body dependencies;
- trait-selection dependencies;
- fixity dependencies;
- generic-instance dependencies;
- capability dependencies;
- change fingerprints;
- red-green validation or the chosen alternative;
- invalidation traces;
- unexpectedly broad rebuild detection.

### 06. Caching, Persistence, Eviction, and Schema Evolution

Defines the complete cache architecture.

It should separate:

- in-memory query memoization;
- persistent semantic caches;
- emitted-function caches;
- final artifact caches;
- content-addressed storage;
- cache manifests;
- checksums;
- schema versions;
- compiler-version identities;
- cache validation;
- eviction under memory pressure;
- warm-versus-cold equivalence;
- corrupted-entry handling.

Cached data must always be treated as an untrusted optimization hint.

### 07. Determinism and Reproducibility

Defines everything necessary for byte-identical output.

It should settle:

- deterministic diagnostic ordering;
- canonical pool freezing;
- stable interface serialization;
- deterministic generic-instance discovery;
- map and set iteration rules;
- optimizer worklist ordering;
- artifact record ordering;
- warm-versus-cold build equivalence;
- parallel execution without nondeterminism;
- stage-two/stage-three comparison.

### 08. Cancellation, Resource Limits, Corruption Handling, and Security

Defines how the compiler behaves under obsolete, hostile, or pathological work.

It should cover:

- cancellation propagation;
- transactional query commits;
- token and syntax limits;
- type and trait-solver limits;
- monomorphization limits;
- MIR and optimizer budgets;
- diagnostic-volume limits;
- memory ceilings;
- malformed cache inputs;
- malformed dependency interfaces;
- internal invariant failures;
- fail-closed behavior.

# Volume III — Source and Frontend

### 09. Source Model, Spans, Lossless Lexing, and Delimiter Pairing

Defines the immutable source substrate.

It should describe:

- source files and bundles;
- byte offsets and line mappings;
- source segments;
- lossless tokens and trivia;
- lexical diagnostics;
- nested comments;
- malformed token recovery;
- delimiter-pair construction;
- incremental lexing boundaries;
- formatter and refactoring requirements;
- stable syntax anchors.

### 10. Packages, Modules, Structural Scanning, Interfaces, and Fixity

Defines everything that can be known without parsing complete bodies.

It should specify:

- package roots;
- module discovery;
- inline and external modules;
- declaration shells;
- visibility;
- top-level token ranges;
- traits, implementations, effects, aliases, and fixities;
- exported package interfaces;
- dependency interface consumption;
- interface fingerprints;
- generic bodies that must cross package boundaries.

### 11. Body Parsing, Contextual Blocks, Operator Grouping, and Recovery

Defines the body parser.

It should cover:

- body-local syntax arenas;
- token cursors;
- expected delimiters;
- contextual block interpretation;
- closures and anonymous callables;
- flat operator streams;
- source-defined fixity grouping;
- patterns and handlers;
- labels;
- error recovery;
- parser transactions and rollback;
- incomplete editor syntax;
- termination guarantees for malformed input.

### 12. Name Resolution, Scopes, Visibility, and Reference Indexing

Defines semantic identity binding.

It should describe:

- namespace separation;
- lexical scope stacks;
- local bindings;
- pattern bindings;
- generic parameter bindings;
- module paths;
- imports and aliases;
- privacy and visibility;
- ambiguity;
- method and associated-item lookup prerequisites;
- definition-at-position;
- references-to-definition;
- rename safety;
- resolution recovery for editor requests.

# Volume IV — Static Semantics

### 13. Semantic Types, Normalization, and Inference

Defines the compiler’s type representation and inference machinery.

It should cover:

- nominal types;
- references;
- callable types;
- never and unit;
- inference variables;
- expected-type elaboration;
- unification;
- coercion policy, where any exists;
- normalization;
- zonking;
- occurs checks;
- recursive types;
- type fingerprints;
- type presentation for diagnostics and tooling.

### 14. Generics, Traits, Associated Items, GATs, HRTBs, and Consts

Defines the generic and trait-solving engine.

It should specify:

- generic parameter kinds;
- trait goals;
- canonical goals;
- implementation coherence;
- orphan rules;
- associated types and effect rows;
- GATs;
- higher-ranked lifetime placeholders;
- const generics;
- const normalization;
- structural constants;
- solver tables;
- cycles and coinduction;
- solver dependencies and cacheability;
- proof explanations.

### 15. Effects, Effect Rows, Handlers, Resumptions, and Cancellation

Defines the complete static control-effect system.

It should describe:

- nominal effects;
- effect instances;
- open and closed rows;
- outward effects;
- operation lookup;
- deep handlers;
- partial handlers;
- terminal operations;
- continuation result types;
- one-shot and finite multi-shot resumptions;
- cancellation;
- nested suspension;
- payload references;
- effectful callables;
- handler reinstatement;
- static restrictions required for soundness.

### 16. Quantitative Use and Ownership Obligations

Defines Glorious’s central quantitative engine.

It should specify:

- principal use intervals;
- requested and actual quantities;
- sequencing;
- exclusive branch hulls;
- repetition and widening;
- nested-execution multiplication;
- exact-positive obligations;
- affine and unrestricted values;
- zero-use destruction;
- transfer propagation;
- partial moves;
- continuation replay;
- cancellation;
- opaque representations;
- private-field consumption authority;
- diagnostics that explain the computed interval.

# Volume V — Semantic Core and Ownership

### 17. Regions, Lifetimes, Borrowing, and Reborrowing

Defines region inference and borrow checking.

It should cover:

- shared and unique references;
- place origins;
- region variables;
- outlives constraints;
- nonlexical lifetime inference;
- reborrowing;
- variance;
- higher-ranked leak checking;
- drop checking;
- references through aggregates;
- references in effect payloads;
- suspension boundaries;
- continuation captures;
- rejection of illegal escape.

### 18. Callables, Captures, Brands, Environments, and Refinements

Defines the shared callable and nominal-environment kernel.

It should describe:

- named and anonymous callables;
- closures;
- handler clauses;
- resumptions as callables;
- receiver modes;
- capture inference;
- capture layout;
- `Fn` and `RunsIn` evidence;
- environment brands;
- label brands;
- continuation identities;
- binder keys;
- open and sealed environments;
- `is` refinements;
- environment post-states.

### 19. Typed Core

Defines the smallest trusted semantic calculus.

It should enumerate every Core form and its invariants:

- values;
- constructions;
- projections;
- calls;
- tail calls;
- labels and transfers;
- effects;
- handlers;
- resumptions;
- cancellation;
- borrows;
- destruction;
- machine primitives;
- host imports.

It should also state explicitly what Typed Core may never contain, including compiler-known `if`, `match`, `loop`, or `return` nodes.

### 20. PlaceFlow

Defines the compiler’s single source of ownership facts.

It should cover:

- places and projections;
- initialization;
- move paths;
- final-use selection;
- copies;
- loans;
- captures;
- partial moves;
- continuation snapshots;
- cleanup obligations;
- destruction eligibility;
- must-move obligations;
- control-flow joins;
- loops and fixed points;
- fact-table representation;
- queries over PlaceFlow;
- validation of imported facts.

# Volume VI — MIR and Optimization

### 21. Ownership-and-Control MIR, Lowering, Cleanup, and Validation

Defines the operational IR and the complete Core-to-MIR translation.

It should specify:

- blocks and block parameters;
- locals and places;
- statements;
- terminators;
- calls and tail calls;
- switches;
- labels and `LEAVE`;
- effects and handlers;
- resume and cancel;
- cleanup edges;
- failed initialization;
- destruction order;
- source mappings;
- MIR construction;
- structural validation;
- semantic validation against PlaceFlow.

### 22. Generic Instances, Monomorphization, and Interprocedural Summaries

Defines demand-driven instance construction.

It should cover:

- canonical instance keys;
- type, const, effect, lifetime, and quantity substitutions;
- reachability;
- recursion;
- instance discovery;
- body reuse;
- cross-package generic bodies;
- call summaries;
- effect summaries;
- capture summaries;
- ownership summaries;
- invalidation of specialized instances;
- instance explosion limits.

### 23. Optimizer Framework, Analyses, Budgets, and Invalidations

Defines the optimizer as an infrastructure rather than a list of ad hoc rewrites.

It should specify:

- analysis bundles;
- checked MIR editing;
- analysis invalidation masks;
- bounded fixed points;
- pass ordering;
- optimization levels;
- work budgets;
- transformation profitability;
- semantic barriers;
- differential checking;
- pass reports;
- deterministic behavior;
- optimization-cache boundaries.

### 24. Source-Defined Control Specialization

Defines the most Glorious-specific optimization family.

It should describe:

- control summaries;
- contextual callable blocks;
- branded labels;
- source-defined conditionals;
- source-defined loops;
- propagation helpers;
- pattern selection;
- static handler fusion;
- one-shot continuation elimination;
- direct branch and loop formation;
- `LEAVE` formation;
- residual runtime machinery;
- `control_plan`;
- failure explanations;
- development lints.

# Volume VII — Emission and Runtime

### 25. Register Allocation, Instruction Selection, and Function Emission

Defines MIR-to-bytecode lowering.

It should cover:

- physical register representation;
- empty-register states;
- typed register reuse;
- addressable places;
- block layout;
- parallel edge transfers;
- cycle breaking;
- instruction selection;
- cleanup maps;
- continuation capture plans;
- constant and operand pools;
- per-function emission;
- emitted-function caching;
- source-to-PC maps.

### 26. Interface Artifacts, Executable Artifacts, Linking, and Serialization

Defines all persistent compiler outputs.

It should specify:

- dependency interface format;
- executable `.grbc` format;
- section schemas;
- feature flags;
- critical and noncritical sections;
- canonical serialization;
- stable fingerprints;
- function tables;
- type and signature tables;
- source maps;
- capability declarations;
- artifact linking;
- compatibility policy;
- schema migration.

### 27. Bytecode Decoder and Verifier

Defines the independent artifact trust boundary.

It should cover:

- defensive decoding;
- section validation;
- type and signature checking;
- register-state dataflow;
- move and copy legality;
- place and reference legality;
- cleanup validation;
- label and handler validation;
- resumption identities;
- continuation captures;
- host imports;
- resource amplification defenses;
- verifier products supplied to the VM;
- hostile-artifact testing.

### 28. VM, Supervisor, Host Capabilities, and Runtime Limits

Defines execution after verification.

It should describe:

- frozen execution images;
- register frames;
- arena handles;
- values and aggregates;
- references;
- callables;
- handlers;
- continuations;
- destruction;
- cycle reclamation, if retained;
- host calls;
- exact capability grants;
- worker isolation;
- memory and time limits;
- runtime diagnostics;
- deterministic execution boundaries.

# Volume VIII — User Experience, Validation, and Self-Hosting

### 29. Diagnostics, Explanations, and Machine-Applicable Fixes

Defines diagnostics as structured semantic products.

It should cover:

- stable diagnostic codes;
- source and semantic identity spaces;
- primary and related locations;
- expected and observed facts;
- explanation chains;
- quantity derivations;
- trait proofs;
- effect escape explanations;
- borrow explanations;
- control-fusion explanations;
- warnings and lint levels;
- fixes;
- deterministic rendering;
- JSON output.

### 30. Compiler Service APIs and Tooling

Defines how every tool consumes the same semantic engine.

It should cover:

- command-line API;
- package-tool integration;
- language-server requests;
- hover;
- completion;
- definitions;
- references;
- rename;
- semantic highlighting;
- formatting;
- documentation;
- refactoring;
- compile-fail testing;
- inspection commands;
- long-lived compiler processes;
- editor recovery behavior.

### 31. Testing, Differential Oracles, Fuzzing, and Performance

Defines how correctness and performance are demonstrated.

It should describe:

- unit tests;
- compile-pass and compile-fail tests;
- golden diagnostics;
- Rust-bootstrap versus self-hosted differential tests;
- VM versus native comparisons;
- O0 versus optimized semantics;
- optimizer trace equivalence;
- hostile artifact corpora;
- parser and verifier fuzzing;
- deterministic-build tests;
- incremental invalidation tests;
- cache-correctness tests;
- benchmarks;
- memory measurements;
- performance regression gates.

### 32. Self-Hosting, Bootstrap Convergence, Migration, and Release

Defines how the envisioned compiler becomes real.

It should specify:

- the stage-zero Rust compiler;
- the self-hosted source tree;
- compatibility probes;
- migration by subsystem;
- parity ledgers;
- stage-one, stage-two, and stage-three builds;
- byte-identity requirements;
- canonical seed production;
- release manifests;
- checksums;
- reproducible release commands;
- compatibility promises;
- deprecation of bootstrap-only mechanisms.

# How I would apply the snowflake method

I would **not** immediately write document 01 in exhaustive detail and then move sequentially through document 32. That risks discovering contradictions after hundreds of pages have already been written.

The next expansion should proceed breadth-first:

1. Keep the existing document as the root synopsis.
2. Write a **two-to-four-page synopsis for each of these 32 documents**.
3. Reconcile vocabulary, identities, phase boundaries, and dependencies across all 32.
4. Lock the shared architecture.
5. Expand each synopsis into its full implementation specification, probably **8–25 pages per document**.
6. Derive implementation epics, milestones, and tests from the completed specifications.

Every detailed document should use the same internal template:

1. Purpose and scope  
2. Goals and non-goals  
3. Public queries and interfaces  
4. Data structures and ownership  
5. Algorithms and phase order  
6. Semantic invariants  
7. Cycles and fixed points  
8. Incremental dependencies and invalidation  
9. Caching and persistence  
10. Diagnostics and explanation  
11. Cancellation and resource limits  
12. Determinism requirements  
13. Testing strategy  
14. Migration from the current implementation  
15. Open questions and rejected alternatives  

The existing document would therefore become **document 00**, followed by these **32 implementation snowflakes**. An index and a shared glossary should accompany them, but I would not count those as substantive design documents.
