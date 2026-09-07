# Specification conformance groundwork

This is the test plan for the current [language specification](../glorious-language-specification.md)
and [standard-library specification](../glorious-standard-library-specification.md).
It is **not a claim that Stage0 or the library conforms**, and does not preserve
obsolete source/API/ABI behavior. The specifications are the authority; this
plan must change when their intended contracts change.

Finite tests supply strong acceptance and regression evidence, not a mathematical
proof of soundness for every program. Independent validators, property/model
tests, unsafe-invariant review and explicit coverage gaps remain necessary.

## Start here

- [cases.tsv](cases.tsv): all L01–L48 and S01–S96 acceptance families, plus LX/SX
  families covering requirements outside those checklists. Every row defines
  positive, negative/counterexample and boundary scenarios, an oracle, source
  sections, a harness and required expansion matrices. **All are planned.**
- [matrices.json](matrices.json): mandatory finite families and cross-cutting
  expansions, including all **588 scalar conversion policy/pair cells**,
  ownership classes, actual library bodies, profiles, effects, target widths,
  callbacks, cleanup paths, fault injection and mixed execution.
- [spec-lock.json](spec-lock.json): reviewed source hashes and routing units for
  every substantive numbered section through language §20 and library §32.
  Prose, lists, tables and code blocks are included, not just sentences saying
  MUST. Rationale is not a separate rule. A whole code block is a review unit,
  **not one atomic API requirement or one test**.
- [regression-candidates.tsv](regression-candidates.tsv): a small, checked index
  of existing tests worth adapting. Existence is not a passing result, a full
  semantic match, or evidence for a missing native backend. The older
  [48-row inventory](../docs/self-hosted-compiler/stage0-semantic-inventory.tsv)
  is another candidate pool, not a competing authority.
- [verification.md](verification.md): commands and actual results for this
  groundwork, including the still-red executable regression suite.

Rows use `L2.2` for language §2.2 and `S18.3` for library §18.3. `LX` and `SX`
are supplemental test-plan IDs, not new specification clauses. The
`positive`, `negative` and `boundary` columns describe families of fixtures;
split their individual assertions into independently diagnosable tests during
implementation. Their stable scenario prefixes are `L01.positive`, etc.
For an API with no invalid safe input, a negative case is an adversarial
implementation/oracle mutation, **not an invented source rejection rule**.

## Commands and what a green result means

Run from the repository root, using the repository's test time limit:

```sh
tooling/test-with-budget.sh python3 tooling/conformance_check.py --check
tooling/test-with-budget.sh python3 -m unittest discover -s tooling/tests -p 'test_conformance_check.py'
python3 tooling/conformance_check.py --list-scenarios
python3 tooling/conformance_check.py --list-units
python3 tooling/conformance_check.py --conversion-cells
python3 tooling/conformance_check.py --require-complete
```

`--check` is an executable **plan-integrity** gate. It verifies exact checklist
coverage, unique cases, routing of all substantive sections, detailed scenarios,
valid matrix references, complete scalar-pair expansion, unchanged reviewed
specifications and real nonignored Rust candidate anchors. CI runs it separately
from compiler semantics. Its mutation tests demonstrate that omissions, drift,
fake evidence and broken anchors are rejected.

`--require-complete` intentionally exits **1** today. There is no executable
per-scenario/per-profile evidence schema yet, and no plan row can be marked
passed. Do not add it as a green CI prerequisite or change it to silently skip
missing features. Later implementation work must add a real execution/evidence
schema before this readiness condition can be satisfied.

`--list-units` prints actual current clause text and its routed case families,
so reviewers can inspect obligations inside a large API block or control table.
Routing a section is not proof that its scenarios cover every sentence: each
fixture author must review the complete routed units. The snapshot catches
subsequent additions or changes that would otherwise escape that review.

For a specification change, review the source diff, update scenarios and
matrices, and only then use `--print-lock` to obtain a proposed snapshot for
an explicit reviewed file edit. It writes nothing and grants no approval.
Do not regenerate a hash simply to make an unexplained failing gate green.

## The real standard library is a compiler acceptance suite

Implementing the whole source library is a major test of the compiler's actual
expressiveness. **SX01/SX02 are foundational gates, not optional examples.**
They require more than compiling a `main` that imports an otherwise unused
library. Demand-driven specialization can leave almost every generic method
unvisited in that situation.

The library gate must produce a declaration/body/instantiation ledger:

| Layer | Required evidence |
| --- | --- |
| Public source surface | Every specified function, associated member, type, constructor, constant, effect operation, trait and family expansion exists in its canonical module with the exact public contract. |
| Real implementation | Every selected library module and body is parsed/elaborated. No bodyless placeholder, `()` stub or host implementation of whole collections, UTF-8, formatting or control substitutes for source code. Genuine manifest-bound leaves remain allowed. |
| Generic materialization | Downstream source roots instantiate every public generic callable and required trait instance through the full production lowering/emission/verification path. An interface check alone does not cover a generic body. |
| Client behavior | Execute calls using those actual library implementations and compare independent value, ownership, effect and failure oracles. Do not replace them with miniature test-only versions for the library gate. |
| Dependency closure | Build core, core+alloc, std and optional compiler modules with exactly their dependencies. Include no-std/explicit-prelude clients and negative missing-dependency/grant tests. |
| Completion | Every owning public type records its principal use rule, selected Drop if applicable, and lawful consuming completion operations for each reachable state. |

Each declaration's ledger entry must link its specification review unit,
qualified declaration identity, source implementation, concrete instantiation
roots, executed scenarios and selected profile. A missing entry fails the
surface gate. A root that is never reached/lowered fails the materialization
gate. A failed or unrun body cannot be counted as covered merely because its
public name resolves.

The signature gate checks owner/member generics separately, argument tuples,
mutability and lifetimes, `unsafe`, visibility, exact result/error type, outward
rows, selected Fn/RunsIn evidence and guarded control contracts. For each
applicable bound, include a client missing that bound and a paired valid client.
Do not weaken signatures merely to make the current solver accept the library.

Required expansions include:

- all twelve integer namespaces, signed-only additions, both float namespaces,
  char APIs and the 14 × 14 × 3 As/TryAs/ExactAs family;
- all four Result/BranchResult And/Or carrier pairs, every reachable structural
  tag path, hidden argument tuples and context merge/projection cases;
- each library §31.1 type-by-trait cell with its exact conditions, all advertised
  tuple arities and array lengths 0/1/multiple, plus §31.2 adapter instances;
- every prose-defined NonZero and predicate/fallible-predicate family, not only
  declarations containing a literal `fn` in a fenced block;
- all Result/Option and collection methods across relevant success/error/empty/
  nonempty cases, independently varying both payload classes where applicable;
- every directly declared host/task operation with provider results, ownership
  and resumption counts. Minimal source test providers are sufficient; a full
  production executor is not a prerequisite for testing the protocol.

A table dash is **not required**, not a required negative implementation.
Opaque `struct Type;` in an interface does not authorize a constructible empty
implementation. The schemas in the specifications need their actual enclosing
modules, imports and family expansion; compiling Markdown blocks verbatim is
not this gate.

## Executable fixture contract

When a planned scenario is implemented, record at least:

1. Stable scenario ID and exact specification unit(s); full source fixture or
   deterministic generator with pinned seed and minimized regression inputs.
2. Required profile, target descriptor, engine, optimization flags, runtime
   manifest/provider and compiler/library revision identities.
3. Expected phase and outcome: accept, source reject, admission reject, typed
   error, terminal category, exact trace, mathematical property or logical
   resource bound. State prerequisites explicitly.
4. An independent oracle and concrete assertions; expected results cannot be
   copied from the implementation under test. Record ownership/effect/output
   facts in addition to a return integer where they matter.
5. A paired valid control for every source-rejection fixture. A syntax error,
   absent library declaration, unresolved import, internal invariant error,
   timeout or exhausted proof budget is **not** the expected ownership/lifetime
   rejection. Check source spans and the violated semantic obligation, not
   exact English messages or frozen diagnostic numbers.
6. Actual execution outcome, command, supported-capability decisions and
   failure artifact. Merely pointing at a function named `test_*` is not
   execution evidence. Keep source, model and execution hashes together.

These are future evidence requirements, not fabricated records in this commit.
No `#[ignore]`, unconditional successful stub or expected compiler failure is
allowed to stand in for a completed positive scenario. An enabled red test is
useful but still reports a gap. Update stale tests to the intended semantics;
do not preserve old acceptance as a compatibility constraint.

## Independent oracles and observation

The `harness` column selects the primary style, not an implementation already
present for every row:

| Harness | Required observation |
| --- | --- |
| lexer / compile / compile-run | Tokens/spans or exact source acceptance; full execution where specified. |
| trace | Ordered capture, call, perform, resume, transfer, Drop and release events with independent logical resident IDs. |
| model | Small sequence/map/iterator/mark/budget/provider state model, checked after each operation. |
| golden / differential | Pinned independently sourced bytes or exact integer/rational/rounding model; VM/native agreement alone can share a bug. |
| metamorphic | Equivalent renamed/reordered source retains specified semantics; no stronger byte identity after a real declaration-identity change. |
| fault-injection | Fail each allocation, callback or provider step in turn and validate the exact promised failure state. |
| resource | Logical work and high-water live-control/storage counters; wall time only supervises the harness. |
| admission | Corrupt one safety-relevant field of a valid interface/artifact/binding and reject before side effects. |
| instrumented / ffi / mixed | Isolated unsafe probes, actual C ABI calls, or actual shared-object VM/native execution, respectively. |
| library | The real implementation plus explicit public-client and generic materialization ledger described above. |

Use at least these reusable test instruments:

- `Ticket`: exact-linear logical owner, including a zero-sized version; lawful
  consuming terminal operation/deconstruction for cleanup of the test itself.
- `DropSpy` and `CloneSpy`: affine and explicitly cloneable probes with separate
  identity/order counters. Do not pretend an exact-linear type can implement Drop.
- Side-effecting callee/argument/capture expressions and callbacks with distinct
  rows and distinguishable result tags. Record formation separately from invocation.
- Fail-after-N allocator with domain/layout/initialized-resident accounting;
  initialize sentinels only in storage that is valid to inspect.
- Scripted I/O/clock/entropy/task providers with operation and resumption ledgers;
  no uncontrolled real files, processes, network or timing races in unit models.
- Small configurable index/generation/budget limits to test exhaustion without
  enormous allocations. These are instrumentation knobs, not changed public laws.
- Explicit high-water frame, delimiter and retained-continuation counters for
  long tail cycles; a known growing control must fail the same bound.

Do not read uninitialized padding to test that semantic hashing avoids padding.
Use instrumentation/defined initialized representations and compare semantic
streams. Different logical zero-sized residents can share an address. Hash
collisions are permitted. A sort may choose its comparison order, maps/sets may
choose iteration order, and an inconsistent safe comparator need only preserve
memory safety and a valid permutation, not sortedness.

Invalid unsafe contracts run only in supported instrumentation and isolated
processes. Record missing instrumentation as a gap. The compiler is not required
to statically decide all unsafe violations, and an unsafe-enabled process is not
a sandbox. Separate safe-wrapper invariants from hostile-bytecode admission and
from trusting an external C caller to uphold its declared obligations.

## Backend/profile and readiness rules

Static checks precede both engines. Every applicable executable scenario runs
through production source compilation, verified VM execution and the native
backend at O0 and shipped optimized levels. Include decoded artifacts, and use
separate internal-IR mutation tests to challenge validators; do not substitute
hand-built IR for the source path or one validator's own metadata for an
independent oracle.

The mixed ABI gate requires actual calls in both directions, same backing
allocation, visible mutation, borrowed/owned results, bytecode-only generic
callbacks, correct source-selected Drop/domain identity and zero marshalling.
Pointer-substrate tests alone do not certify the eventual LLVM backend.

C-FFI is conditional on an advertised C-FFI target capability; optional codecs
and compiler-library modules are conditional on their selected profile. Other
unimplemented language/backend requirements remain **open**, not quietly
not-applicable. A selected unsupported capability must fail explicitly.
Record target widths/endianness/layout facts; no historical G1 decoder, fixed
wire assignment or fixed-64-bit usize preservation is required.

Keep distinct results for plan integrity, executable test coverage, actual
passes/failures, unsupported capabilities and full readiness. Neither a green
inventory nor a green compilation of the library establishes all runtime,
negative, ownership, resource or cross-engine obligations.

## Implementation order

1. Keep this audit green and the older regression harness buildable. Review
   each existing candidate against the new contract before promoting coverage.
2. Implement canonical syntax/import/privacy/argument-pack and generic/effect
   contracts needed to compile the actual core library. Add minimal paired
   source fixtures before or alongside each compiler change.
3. Compile real core/control implementations and their client instantiations;
   validate guarded environments, binding contexts, generative loops and tail
   proof/space bounds before adding dependent library breadth.
4. Implement alloc/collection/text/numeric APIs with the reusable ownership,
   exact-value and allocation-failure instruments. Drive the whole public API
   and trait matrix, not just the methods the compiler currently calls.
5. Add compiler-toolkit and hosted/protocol provider matrices, then full native,
   C-capability and mixed-execution evidence as those backends become available.
   Admission and resource failure tests accompany every stage.
6. Add a machine-readable execution ledger and a strict readiness gate only
   when it can distinguish all implemented/unrun/failed/not-applicable cells.
   No percentages based on source line counts or number of test names.

Policy choices delegated by the specs (for example a documented SeededRng
algorithm version, lossy UTF-8 subsequence policy, target scalar alignment and
logical graph-work charges) need pinned distribution contracts before approving
their exact oracles. Do not invent those answers in test snapshots. Networking,
a production executor, cross-thread memory-model APIs, macros, general
serialization and other explicitly excluded extensions are outside this plan.
