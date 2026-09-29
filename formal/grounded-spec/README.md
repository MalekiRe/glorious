# Grounded language specification

This directory starts a new Lean specification of the language semantics and
future compiler correctness contract. It is not a compiler implementation.
The goal is a smaller, inspectable development built entirely from ground truth,
with one connected body of definitions and proofs—not a collection of proof
islands awaiting integration.

## Governing discipline

**Build from established meaning upward. Do not work backward from a desired
soundness theorem by introducing assumptions that promise its prerequisites.**

The normative [language specification](../../glorious-language-specification.md)
is the source of intended language meaning. Relevant normative library and
machine-interface contracts govern their respective boundaries. Follow the
[compiler architecture contract](../../docs/compiler-architecture.md) without
mistaking implementation organization for language semantics.

Existing Lean code is reference material, not ground truth. A checked proof
establishes its stated proposition under its premises; it does not establish
that its definitions faithfully describe the language, that its premises are
inhabited, or that source programs produce them.

### One connected body, no speculative prerequisites

1. Start with the smallest faithful semantic foundation needed for the current
   construction. Each definition must have a present semantic purpose grounded
   in a normative rule or an explicit execution mechanism.
2. Extend that foundation using only established definitions and checked results.
   Connect each extension to the existing body and prove its applicable
   guarantees before building further on it.
3. Do not introduce temporary prerequisite lemmas, speculative interfaces, unused
   fact tables, or standalone theorems for anticipated future integration.
   Intermediate reasoning belongs inside the proof that needs it. Extract a
   shared lemma only when actual consumers require it, and migrate those
   consumers in the same change.
4. Do not create a second semantic path to avoid repairing the first. Each fact
   has one authoritative producer; consumers use that producer's evidence.
5. A checkpoint must strengthen the connected semantic result. New files, helper
   counts, successful builds, and promises of later composition are not progress
   criteria by themselves.

The foundation is necessary semantic definition, not permission to accumulate a
framework for future proofs. Keep it minimal and extend it through real use.

### Grounded premises, not assumed conclusions

Every premise must have an explicit source: a normative language requirement,
an established invariant produced by the current development, or a genuinely
external machine/foreign assumption whose meaning and scope are documented.

- Derive execution readiness from source admission and established state facts.
  Do not define admission to assume progress, preservation, successful execution,
  valid future states, or eventual resource completion.
- A property may be defined as a proof target. It must not then be supplied as
  admission evidence in place of proving that target.
- Moving an unresolved obligation into a structure, certificate, callback, or
  host contract does not discharge it.
- External assumptions must describe the actual external boundary, not conceal
  obligations belonging to the language semantics.
- Missing evidence is unknown, not absence, permission, or allocation exhaustion.
- No `sorry`, `admit`, or new axioms used to bypass semantic obligations. Identify
  logical axiom dependencies and audit the connected theorem's premises.

### Preserve meaning while simplifying

Optimize for fewer independent concepts, fewer separately supplied premises,
and fewer reconstructions of the same fact—not merely fewer lines.

Preserve distinctions required by the language: source equality versus physical
storage identity; ownership versus borrowed permission; permission versus
custody; captures versus their common invocation coordinates; normal return,
transfer, cancellation, divergence, and failure. Preserve evaluation order,
guards, provenance, and lifetimes through actual transitions.

Allocation must not be assumed successful. Exhaustion must concern the actual
admitted request and preserve any already executed preparation prefix. Logical
type conversion must not be silently treated as physical tag identity.

### Simpler semantics first: complete subsets end to end

Start with the simplest faithful subset and complete its semantic proof end to
end before extending it. This supersedes the older hardest-first construction
order for this directory. The full language remains the goal.

State the supported syntax, admission rules, execution relation, and both ends
of the correctness theorem precisely. Exclude unsupported constructs explicitly;
never give them placeholder behavior. Prove admission is nonvacuous and prove
all applicable typing, progress, result, resource and lifetime guarantees for
every admitted program. Progress alone does not imply termination.

Grow the same definitions and general result. Each extension must preserve the
meaning and guarantees of previously supported programs, with agreement proved
when representations change. Do not build disposable toy languages or parallel
fragments for later unification. Completed subset soundness is a legitimate
milestone, not whole-language completion or compiler correctness.

An AST-to-value theorem does not prove parsing, physical allocation behavior,
or implementation correctness. Those boundaries must later be established,
not silently inferred from a logical evaluation theorem.

## Reusing existing work

[`../spec/`](../spec/) contains prior semantics, proofs, audit findings, and
counterexamples to attempted designs. [`../lean/`](../lean/) is the older
compiler draft, not this development's foundation.

Read and reuse what is justified; do not copy either tree wholesale. Before
bringing code into this directory:

- identify the normative meaning and immediate consumer;
- inspect all premises and transitive dependencies;
- adapt the smallest coherent piece and check it in the new connected chain;
- record provenance in a concise source comment when code is adapted;
- retain discovered semantic constraints even when replacing their old encoding.

Do not import the old proof graph merely to hide dependencies or make a check
pass. Any direct dependency must be deliberate, audited, and necessary for the
current construction. Preserve old trees as reference material; do not delete
unrelated or unfinished work. Within the new development, remove superseded
paths as consumers migrate rather than retaining compatibility layers.

## Acceptance and verification

For each change, answer:

1. Which normative rule or explicit mechanism gives this construction meaning?
2. Which already established facts does it use?
3. Which part of the connected result now becomes stronger?
4. Where are its conclusions consumed now—not in a promised future stage?
5. Which premises, duplicated reasoning, or obsolete paths does it eliminate?
6. What remains outside the proved boundary?

Check the actual Lean definitions and general proofs, including affected
consumers. Audit assumptions and nonvacuity; compilation alone is insufficient.
Do not routinely add or run concrete examples or unit tests. Use an example only
to isolate a suspected modeling error when a general argument is insufficient.
Commit and push meaningful verified changes, preserving unrelated repository
work. Development proceeds serially unless the user changes that direction.

Maintain a concise current account here of the established boundary and its next
grounded extension. Do not turn this README into a checkpoint diary or duplicate
status across competing ledgers. Whole-language completion requires all intended
cases, general preservation/progress and resource/lifetime guarantees, and an
explicit semantic-fidelity and proof-assumption audit.

## Current boundary

**Completed subset: unit, explicitly typed fixed-width nonnegative integer and
decoded character literals, grouping, lexical reads, sequencing, immutable
bindings, arbitrary-arity tuples, and numeric tuple projection over duplicable
values.** The boundary is decoded expression AST to logical value; names use
nearest-binder lookup. Normative basis: §§2.3, 3.2–3.4, 4.1–4.2, 5.1, 5.3 and
7.2–7.3. No previous proof modules are imported. The objective is the full
specification, not a percentage of features.

`Grounded.correctness` proves finite evaluation, result typing and uniqueness
for every admitted expression in a typed environment. Initializers execute in
the old environment; their proved result typing constructs the extended body
environment. Sequencing and binding scope do not leak local names. Copy/discard
sites require explicit duplicability evidence. `closed_correctness` constructs
the empty environment rather than assuming it. Admission has no execution
premise. Exact scalar admission theorems and `unit_agreement` remain connected
to this general result. No intermediate machine-state theorem is claimed.

Tuple arity is preserved: unit is the empty tuple; grouping and a singleton
tuple are distinct. Constituent evaluation and positional value typing are
proved inside the connected theorem, not left as separate prerequisites.
Projection derives its actual resident and typing from the evaluated tuple;
an in-range runtime selection is not separately assumed. Out-of-range tuple
projections cannot be admitted. Physical evaluation traces remain outside this
pure big-step boundary.

Integer types include signed and unsigned 8/16/32/64/128-bit families. Range
checking uses mathematical integers with no wrapping. Characters exclude
surrogates and values above U+10FFFF. Parsing, type inference, prefix negation,
target-size integers, floating conversion, static strings, nominal aggregates,
arrays, calls, mutation, moves, loans, effects and remaining constructs are open.
There is no physical-storage, allocation-failure, package-admission or compiler-
realization claim. Big-step total evaluation is not a small-step machine theorem.

Verification: strict `lake build` passed. The connected correctness and unit
agreement proofs use only Lean's `propext`; scalar admission proofs use no axioms.
Reproduce from this directory:

```sh
lake build
lake env lean -DwarningAsError=true -DautoImplicit=false --stdin <<'LEAN'
import Grounded
#print axioms Grounded.correctness
#print axioms Grounded.closed_correctness
#print axioms Grounded.integer_admission
#print axioms Grounded.character_admission
#print axioms Grounded.unit_agreement
LEAN
```

Next: connect source admission constructively to the existing execution theorem,
then grow callable and nominal-value semantics without primitive booleans:
§4.1 excludes them; truth and branching use ordinary library declarations.
No standalone prerequisite programme is authorized.
