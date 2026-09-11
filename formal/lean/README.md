# Executable Lean semantics — in progress

**Current working draft:** a mandatory, request-indexed whole-compiler proof
attempt is wired into the implementation and driver. The general compiler-phase
proofs still fail, and parts of the proposed specifications remain incomplete. See
[`DRAFT.md`](DRAFT.md). The implemented/proved boundary below describes the
earlier verified checkpoint, not the unverified whole-compiler draft. Draft code
does not establish any additional conformance or end-to-end acceptance yet.

Within that draft, the shared substitution producer is now kernel-checked:
successful substitution follows the declarative structural rules and preserves
the outer kind. All existing Lean semantic consumers use it. The focused
substitution and receiving-register repair gates are recorded in `DRAFT.md`;
neither makes the whole compiler a verified executable.

This is the beginning of the executable formal reference requested for
Glorious. It is **not full language conformance, a completed compiler, or a
proof that Stage0 is correct**. The two repository specifications remain the
normative authorities. Existing Rust development is preserved separately.

The intended pipeline is supplied source closure → elaboration → checked
semantic core → checked lowering → the existing VM artifact. Ownership,
control, lifetimes and lowering must consume the same semantic transitions.
The work here starts at that shared boundary; a second source walker or a
separate unconsumed facts database is not the intended integration.

## Build and trust

Run `lake build` in this directory using the pinned Lean 4.33.1 toolchain.
Only Lean's shipped `Std` is required. Warnings are errors, including Lean's
warning for admitted proofs. There are no project axioms, `sorry` proofs,
`native_decide` proofs, unsafe definitions or external semantic oracles.

Proof checking is the primary verification mechanism. `ProofChecks.lean`
contains a small set of kernel-reduced composition examples, not a replacement
for general proofs. This does not verify Lean's code generator, its runtime,
the existing VM, source-spec interpretation, or future foreign hooks.

## Implemented boundary

| Module | Executable definitions | Established properties |
| --- | --- | --- |
| `Quantity` | Principal permission checks, structural intersection, sequential sum, alternative hull | Intersection exactly describes resident permissions; sums/hulls contain their corresponding executions; an exact-once request does not imply exact principal ownership |
| `Control` | Guarded alternatives and strict sequential composition | Associativity, identity, distribution over alternatives, no suffix execution after nonnormal control, returned values preserve post-state, unknown is not an empty alternative |
| `Cleanup` | Bounded proof-producing resident/scope/exit compilation; consumer of guarded control outcomes | Every returned plan derives from the independent destruction rules; exact owners and open loan holes have no destruction rule; custom hook before reverse fields before release; explicit exhaustion and missing-evidence failures |
| `Effects` | Extensional row operations, exact-instance first-match/deep-handler routing, checked surface resumption policies | Row-union laws; routing reconstructs the original continuation stack; inner delimiters were skipped; the chosen clause has the exact operation/instance identity; exact-two does not admit once-only tail resume |

The cleanup compiler returns proof-carrying plans; the routing algorithm
returns proof-carrying dispatches. The proofs are erased for execution. The
declarative relations are defined independently of those algorithms, so an
algorithm cannot grant itself permission merely by returning success.

The resident forest is an **input contract**, not inferred evidence. It must
come from checked types, actual residual initialization, transferred-payload
protection and loan facts. Stored reference handles, backing storage, logical
owners, loan identities, invocation inputs and generative brands are distinct.
Each resident's logical release is not necessarily an allocator free. Hook
events name the selected Drop declaration; validating and executing those
bodies is a later boundary. A divergent hook prevents subsequent events from
executing; the plan itself does not assert hook termination.

Similarly, effect arguments must already have equality-preserving
normalization, and operation predicates must come from checked pattern
elaboration. Complete-handler row subtraction requires proved coverage, not
just one successful dispatch. These are unimplemented upstream obligations,
not assumptions that imported metadata or source code may assert unchecked.

## Remaining integration and conformance

This checkpoint covers parts of language §§7–8 and 10, with cleanup consumers
for the exits in §§11–12. It does not establish an entire L01–L48 acceptance
family. In particular the following remain required:

- Source decoding, lexer/parser, modules/privacy, declaration selection,
  aliases, structural constants, patterns and exhaustiveness.
- Type/generic/trait/row normalization and inference, coherence, higher-rank
  scopes and leak checks, intrinsic manifest admission.
- The authoritative initialized-storage/loan transition system, actual
  capture formation and invocation, availability sealing, deconstruction,
  moves/copies, borrow checking and reference-return provenance.
- Complete operational calls, label fusion, handler continuation capture,
  alias-accounted resumption/replay, and proper-tail storage proofs. Routing
  and allowed-quantity definitions alone do not establish these properties.
- Typed Core preservation/progress and verified receiving IR/lowering,
  concrete target/scalar/layout semantics, ABI and unsafe/FFI admission.
- A `.glorious` frontend, executable reference compiler, actual VM artifact
  emission, VM/native boundary checks, and the companion's library behavior.
- Migration of production compiler consumers. No existing Rust semantic path
  has yet been replaced or proved by these Lean modules.

These requirements are not satisfied by adding constructors or trusting a
caller-provided contract. Subsequent work must produce and check the evidence,
connect the executable consumers and remove superseded paths. Standard-library
completion and the new self-hosted compiler remain separate final gates.
