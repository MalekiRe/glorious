# Grandiose

Grandiose is being rebuilt as a compact, self-hosting compiler and portable
bytecode VM. The target system is:

- `grvm`, a safe Rust bytecode decoder, verifier, VM, host-capability adapter,
  and supervisor;
- `grc`, a Grandiose compiler distributed as verified `.grbc` bytecode;
- `std-lib.glorious`, the source-defined control and compiler-building library
  prepended to every generation-1 compilation.

The normative design starts with [the architecture](docs/architecture.md), the
[bytecode contract](docs/bytecode.md), the
[standard-library contract](docs/std-lib.md), and the
[language core](glorious-branded-environment-core-spec.md). The live,
completed-work-pruned backlog is [docs/remaining-work.md](docs/remaining-work.md).

## Repository status

This repository is pre-alpha. The Rust implementation is the authoritative
generation-1 compiler and VM under construction. The old compiler under
`compiler/` is retained only as historical/bootstrap material and is excluded
from implementation progress, porting plans, and self-hosting estimates.

`crates/grandiose-vm` implements the canonical G1 container and codec, hostile
input verification, typed register VM, deterministic cleanup and custom drop,
references and loans, labels and `leave`, deep handlers, finite multi-shot
resumptions, host capabilities, supervision, and deterministic reclamation of
cyclic runtime environments.

`crates/grandiose` implements the source frontend, recovery interpreter, trait
and generic solver, typed Core, ownership-aware MIR, optimizer, bytecode
emission, and artifact verification pipeline. Accepted programs compile through
the same verified Core/MIR/bytecode path at O0 through O3.

### Completed ownership checkpoint

The supported G1 ownership surface is implemented and independently validated
by PlaceFlow:

- exact `Use<[lower, upper]>` obligations, must-move values, transfers,
  structural deconstruction, and zero-use destruction;
- arbitrary supported CFG joins, loops, handlers, cancellation, tail transfer,
  and unreachable predecessors;
- nested partial moves, reconstruction, enum variant replacement, conditional
  initialization, reverse cleanup, and exact residual-shell accounting;
- shared and unique loans, NLL, nested projections, temporary projected
  reborrows, reference-origin transport, and escape/alias rejection;
- reference-bearing struct/tuple deconstruction and reference-to-enum payload
  projection under a dominating variant proof;
- partial residual aggregates across direct and indirect suspension, optional
  cancellation, and exact finite multi-shot replay;
- transitive validation of pure custom `Drop` bodies; and
- canonical exported join, indirect-effect, capture, cancellation, and cleanup
  facts that MIR import recomputes and rejects when hostile or inconsistent.

Memoized globals with restricted `Use` intervals are a deliberate G1 exclusion:
their reads are not source-bounded ownership events. Restricted global results
therefore receive a structured compile-time diagnostic.

### Effects checkpoint

The compiler and VM already support closed effect rows, generic effect
instances, terminal and resumptive handlers, deep resume, explicit
cancellation, outward effect propagation, exact finite resumption quantities,
nested suspension, handler environments, reference payloads/results, and
mixed one-shot/multi-shot environments. Remaining effect work is tracked only
in the live backlog and is currently concentrated in fully compositional
handler-result inference/nesting, recursive reference-origin summaries, and
late recursive or broader quantity-bearing resumption environments.

### Verification gates

The repository uses deterministic unit, hostile-artifact, source-to-VM, and
O0-O3 acceptance tests. The ownership checkpoint currently includes 263 library
tests, 200 compiler integration tests, 21 path-sensitive suspension cases, 20
generic reference-transport cases, 31 typed-callable cases, 19 deconstruction
cases, and strict workspace formatting and Clippy gates.

These counts are checkpoints, not a promise of source or artifact stability.
The compiler CLI, standard-library breadth, tooling, release hardening, and the
eventual wholesale source port/self-hosting convergence remain separate work.
