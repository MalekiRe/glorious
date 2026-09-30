# Language semantics proof plan

## Authority and current status

This is the single active proof plan for the new development in
`formal/semantics/`. The requirements in [AGENTS.md](../../AGENTS.md) govern it.
The [compiler architecture contract](../../docs/compiler-architecture.md)
governs semantic authority; the
[language specification](../../glorious-language-specification.md) and relevant
normative library contracts determine language meaning.

The user authorized this new folder after reviewing the previous development's
assumed realization bridges and incompatible invariants. Existing work in
`formal/spec/`, `formal/grounded-spec/`, and `formal/lean/` is preserved as
reference, not developed in parallel. No old theorem is automatically a theorem
of this development. No temporary code, assumed bridge, or placeholder Lean
project is introduced by this reset. Subagent use remains paused.

## Recovered, verified baseline

At commit `2958fffc`, `Grounded.lean` was restored byte-for-byte from commit
`d182ea2a` ("Derive ordered pattern dispatch from structural coverage"), the
1,081-line early second-revision milestone. This historical baseline established
the independent Lean 4.33.1 project described below. Subsequent changes are
recorded separately; the active files are no longer a byte-identical restoration.
The package remains `languageSemantics`, with module/namespace `Grounded`.

Covered: target-bounded integer and Unicode scalar literals; immutable lexical
binding and sequencing; tuples, fixed arrays and projections; decoded aliases
and structural constants; finite-layout duplicable nominal data with visibility
checks; direct noncapturing calls with finite body-typing derivations; and
immediate ordered pattern application with structural coverage and usefulness.

The public theorem is `Grounded.correctness`:

```lean
HasType program home context expression type →
EnvironmentTyped program environment context →
∃ value, Evaluates program environment expression value ∧
  ValueHasType program value type ∧
  ∀ other, Evaluates program environment expression other → other = value
```

`Grounded.closed_correctness` discharges the entry environment using the empty
environment constructor. The general induction constructs binding and parameter
environments and invokes the same evaluation relation for constants, calls,
and selected pattern bodies. No executable-realization, future evaluation,
successful cleanup, or run-level progress premise is supplied.

Premise-producer map:

| Premise | Meaning and producer | Actual consumer |
| --- | --- | --- |
| `HasType` | Ordinary rules check decoded syntax, declarations, visibility, bounds and permitted duplicable operations. Calls include a finite derivation for their declared body. | `correctness` inducts on these rules and their list/arm derivations. |
| `EnvironmentTyped` | Legitimate current values agree with lexical types. Empty entry constructs it; binding, parameter zipping and pattern binding preserve it. | Lookup and recursive body correctness. |
| `Covers` | Structural constructor-space coverage, not an evaluation-success certificate. | `Covers.selectArm` constructs selection after argument evaluation. |
| `PatternType` | Static constructor/field typing, access and legal duplicable disposal. | `PatternType.bindings` derives the selected body's typed environment. |
| `Useful` | A typed datum distinguishes a clause from preceding clauses; it does not assert evaluation of the subject. | `ArmsType.clause` admits only useful clauses. |

This is a logical terminating AST-to-value theorem, not whole-language
soundness, a source parser/typechecker implementation, or machine progress.
Inductive body typing does not admit general recursive calls. Immutable values
model no mutable storage, loans, captures, physical allocation, exhaustion,
nonlocal control or custom destructors. No later reference/admission machinery
was restored. The old pending/view defects below are constraints on future
extensions, not defects asserted to exist in this recovered fragment.

Verification performed in `formal/semantics`:

- `cmp Grounded.lean <(git show d182ea2a:formal/grounded-spec/Grounded.lean)`
  passed: exact historical source, not a reconstructed approximation.
- `lake build` passed with `autoImplicit=false` and `warningAsError=true`
  configured in `lakefile.toml`.
- A strict Lean defining-module audit checked all 1,135 declarations, including
  28 private declarations and generated declarations. The only transitive
  axioms were `propext` and `Quot.sound`. The public correctness, closed
  correctness, coverage-selection and pattern-binding results were also
  inspected individually. No concrete examples or unit tests were added.

The recovered proof is the first semantic checkpoint here. It supplies a
connected base to extend, not permission to replay the later development's
assumed bridges or to treat its finite terminating subset as the full language.

## Structural constant-pattern boundary

The authoritative entry remains `Grounded.lean`. It now imports two modules:
`Grounded/Core.lean` owns decoded typing, coverage, evaluation and general
correctness; `Grounded/SourcePatterns.lean` owns source-pattern normalization
and its application consumer. There is no second evaluator or copied admission
framework. The public `Grounded.correctness` signature is unchanged.

Normative scope: §4.3 structural constant patterns, composed with §6.3 ordered
pattern application. Normalized constants retain their resolved declared type
and compare complete structural values without invoking user-defined Eq.
Nominal identity, constructor tags, scalar kinds and aggregate shape participate
in equality. The existing coverage-selection and binding theorems now handle
literal patterns, and the general correctness induction consumes them.

The new public theorem is `SourceArmsChecked.correctness`:

- Inputs: source patterns with ordinary closed constant typing; typed arguments;
  a nonempty source arm list; ordinary coverage, usefulness, pattern and body
  checking of the **computed normalized list**; a typed current environment.
- Conclusions: normalization of that source list; uniqueness of the entire
  normalized list, including declared type tags; actual evaluation of its
  application; result typing; uniqueness of the evaluation result.
- No successful evaluation or normalization is supplied. Static checking of the
  normalized patterns remains explicit: normalization alone does not establish
  exhaustiveness, usefulness, visibility, or body typing.

| Fact | Producer | Consumer |
| --- | --- | --- |
| Constant value | Existing `closed_correctness`, from ordinary constant typing | `SourcePattern.Checked.normalize` and `normalizes` |
| Unique constant type and value | `ResolvesType.unique` and existing evaluation uniqueness | `NormalizesPattern.unique`, then `NormalizesArms.unique` |
| Ordered normalized patterns and unchanged bodies | `SourceArmsChecked.normalize` and `normalizes` | Ordinary `Covers` / `ArmsType`, then `SourceArmsChecked.correctness` |
| Actual selected-body execution | `Covers.selectArm`, `PatternType.bindings`, general correctness | The source application theorem |

Normalization uses standard `Classical.choice` to extract a value whose
existence is already proved; its uniqueness is proved independently of choice.
This is a semantic definition, not an implemented normalization algorithm.
Source patterns are elaborated for an application whose arguments and bodies
remain decoded core. No parser or complete recursive source elaborator is
claimed. Stateful and whole-language obligations remain open.

Verification: `lake build` passed with strict configured options. A strict
Lean audit inspected every declaration defined by both modules, including
private/generated declarations (1,428 total, 64 private). Only `propext`,
`Quot.sound` and standard `Classical.choice` occur transitively. Core
correctness, coverage selection, pattern binding and normalization uniqueness
still require only `propext` and `Quot.sound`; the chosen normalization
product and its public consumer additionally use `Classical.choice`.
No `sorry`, custom axiom, unit test or concrete-example evidence was introduced.


## Destination contract

The full-language goal remains a faithful semantic specification and a proved
language/compiler correctness contract before compiler implementation. The
following are design obligations, not asserted Lean propositions or axioms:

- Start from ordinary source checking and explicit, legitimate current-state
  and external-interface evidence. Construct the execution correspondence;
  do not require a separately supplied executable realization.
- Prove preservation through actual transitions and progress at the appropriate
  machine boundary. Do not assume progress over all runs as source admission.
- Preserve the chosen elaboration/checking products and evaluation order. Keep
  the checking of alternatives distinct from runtime execution of the selected
  alternative; use the actual matcher, including preceding failures.
- Preserve resource ownership, provenance, lifetime, initialization, and
  control obligations across the outcomes where they apply. Distinguish normal
  return, nonlocal transfer, cancellation/cleanup, resource exhaustion, fatal
  abort, and divergence. A terminating big-step theorem is not a substitute
  for a correctness contract covering recursion and divergence.
- State the obligations of compiler transformations and foreign/runtime
  interfaces explicitly. Do not label an abstract language theorem as physical
  allocation, ABI, or compiler correctness.

Before extending the recovered fragment, refine the destination into precise
public theorem signatures and a premise-producer map for the next coherent
boundary. Record unsupported constructs explicitly; partial coverage is not
approval to reduce the full-language goal.

## Required design boundary before stateful extensions

Resolve these interacting questions together before extending the baseline with
mutable storage, resource-bearing references, or their execution contracts:

1. **Pending resources and initialization holes.** Separate resource
   correspondence and ownership from current readiness. Determine exactly when
   use, passing, transfer, and cleanup require restoration under language
   sections 5.2, 5.3, and 7.5. The old global `StateTyped.heldReady` requirement
   may reject a legal temporarily suspended pending ancestor; that path is a
   suspected defect, not a proved counterexample. Establish the actual producer
   path and the normative obligation before choosing the invariant. Neither
   blanket overlap rejection nor weakened restoration guarantees is a repair.
2. **Canonical target resolution and dormant declarations.** Use authoritative
   loan/storage resolution. Raw target lookup or a missing cached cell is not
   proof that a reference is dormant. Settle how unexecuted declared reference
   inputs are checked without inventing runtime storage or unjustified
   separation between potentially aliased references. Audit any proposal to
   introduce fresh symbolic roots against that aliasing requirement.
3. **Selected branch products.** Construct concrete source products for the
   actually selected branch while retaining the original checked alternatives,
   coverage, and priority. Do not demand incompatible concrete constructor
   evidence for every alternative, or silently select a different checking
   derivation to make realization possible.
4. **Entry and produced values.** Canonical entry must derive the current-state
   correspondence it promises from actual backing storage and resources.
   Untouched opaque pending carriers must not acquire an unjustified nominal
   typing requirement. Produced results and invocation arguments need their
   actual typed interpretation and freshness evidence from their producers.

For each decision record: normative requirement, exact contract, premise
producer, preservation consumers, and what discharges it at public entry.
Existing `Context.Resolves`, custody proofs, operation producers, and import
proofs are reference candidates, not predetermined interfaces to preserve.

## Implementation and composition discipline

Implement the settled boundary as a connected vertical slice:

1. Define the authoritative semantic relation and its legitimate entry facts.
2. Prove each real operation constructs its outcome, preserving the appropriate
   structural invariants and establishing the readiness required by consumers.
3. Compose sequencing, arguments/captures, selected branches, and ordered
   cleanup through those contracts. Transport freshness and interpretation
   through the complete sequence, not merely each local step.
4. Close the general preservation/progress or correctness result for the stated
   boundary and connect its public entry consumers.

Extend the recovered connected source through modules with actual semantic
responsibilities, rather than growing another monolith or creating a generic
framework in advance. Source organization changes must preserve the existing
public result. Reused proofs need audited hypotheses and real consumers; no
extra evaluator, resource walker, compatibility layer, or callback may stand in
for a missing proof.

The older `checked_correctness.realized` premise, run-level `ResourceAdmissionAt`,
eager executable arm evidence, and raw-target opaque-view discriminator must not
be copied into the new development as convenient admission assumptions.

## Checkpoint and continuation record

At each meaningful checkpoint update this document with:

- The exact covered semantic boundary and public theorem symbols.
- Each remaining premise, its producer, and its actual discharge site.
- Assumptions removed and guarantees established by connected consumers.
- Strict Lean command/results and transitive axiom inspection for the affected
  public results; no implication that successful checking validates the model.
- Suspected defects distinguished from proved obstructions, conditional
  theorems distinguished from discharged guarantees, and unsupported features.
- The exact next obligation on the same dependency chain.

Current next obligation: specify mutable lexical storage and assignment
(§5.2) as an extension of the existing checking-to-evaluation theorem. Settle
the current-state, successor-state and framing contracts before adding rules;
derive actual successor storage from checking, not a supplied realization.
Keep the four stateful contract questions above explicit, and preserve the
proved immutable and constant-pattern consumers.

Whole-language completion additionally requires an explicit normative coverage
and consumer audit. Features absent from this new folder remain unproved,
including recursion/divergence, general callables/captures, effects and handlers,
nonlocal control, replay/cancellation, generics/traits, full lifetime and custom
Drop checking, physical allocation/exhaustion, unsafe operations, and
foreign/ABI/compiler composition. This list is not an exhaustive coverage audit.
