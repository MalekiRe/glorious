# Formal language specification

This independent Lean project specifies the language described by
`glorious-language-specification.md`. It does not implement a compiler,
import the earlier `formal/lean` compiler draft, or specify/verify library
algorithms. Source-owned libraries are arbitrary programs using the same
language rules as application code. Machine and foreign boundaries are
explicit contracts.

Status: initial whole-specification draft, in its semantic repair pass.
The latest complete `lake build` passes (38 build jobs), including source
elaboration, origins, the aggregate and `Checks`, with warnings as errors
and implicit identifier creation disabled. This is not a full-language
conformance result. See `DRAFT.md` for checked gates and remaining defects.
Work now follows the hardest-first order in `PROOF-PLAN.md`, beginning with
nonvacuous semantic soundness rather than remaining local feature coverage.
The earlier compiler work remains reference material, not the foundation
or a dependency of this project.

## Organization

- `Foundation`, `Terms`: quantities, identities, typed terms, substitution,
  unbounded executions and two-way observational refinement.
- `Syntax`, `SourceRules`, `Elaboration`, `Origins`: UTF-8, AST-indexed concrete
  grammar, contextual elaboration, declarations and source authentication.
- `Declarations`, `Static`, `Instantiation`, `Typing`: one declaration
  inventory, resolution, kinds, traits, capabilities, concrete instances and
  structural typing.
- `Storage`, `Kernel`, `Machine`, `Atoms`: one storage world, explicit
  sequencing, invocation, transfers, borrowing and executable cleanup.
- `Effects`, `Relocation`, `Control`, `Contracts`: handlers, continuation
  quantities, snapshots, labels, guarded environments and body-checked
  invocation contracts.
- `Target`, `Memory`, `Primitives`, `Foreign`, `ABI`: scalar mathematics,
  layouts, provenance, machine leaves, explicit host models and target
  admission requirements.
- `Specification`, `Checks`: aggregate language/implementation obligations
  and foundational positive/negative regression propositions.

`Execution.Step` is the shared executable meaning. It is consumed by control
contracts, semantic admission and source observations. The grammar produces
the AST consumed by elaboration; source origins authenticate the declaration
inventory rather than accepting a separately supplied unrelated AST.

## Checking

Run `lake build` in this directory using the pinned toolchain. The default
target includes `Checks`. No `sorry`, new axiom, evaluator fuel bound, or
always-rejecting implementation counts as a completed specification/proof.

Checking that definitions and sample propositions elaborate is different
from proving determinism, type soundness, adequacy of every source rule,
or compiler correctness. See `COVERAGE.md` for the audit boundaries.
