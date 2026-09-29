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

**Completed subset: the closed unit expression, from source AST to logical
value.** `Grounded.lean` defines just expression/type/value syntax, admission,
value typing, and big-step evaluation. Its normative basis is language
specification §§3.4 and 4.1. No previous proof modules are imported.

`Grounded.correctness` proves, for every supported expression, admission and,
for every admitted typing, existence of a finite evaluation to the unit value,
result typing, and uniqueness of the evaluation result. Admission is produced
by the theorem, not assumed inhabited; its rule contains no execution premise.
There are no intermediate machine states in this big-step model. This result
establishes total logical evaluation, not small-step machine preservation.

The only supported AST form is `()`. Grouping, other literals, sequencing,
bindings, calls, resources, effects and all other constructs are outside this
subset. Parsing/source authentication, package admission, physical storage,
allocation failure and compiler realization are not proved. No claim about
physical allocation follows from this logical unit-value rule.

Verification: `lake build` with warnings as errors and implicit variables
disabled passed. `#print axioms Grounded.correctness` reports no axioms.
Reproduce from this directory with:

```sh
lake build
lake env lean -DwarningAsError=true -DautoImplicit=false --stdin <<'LEAN'
import Grounded
#print axioms Grounded.correctness
LEAN
```

Next: extend this same chain with a simple normative scalar literal family,
including its validity bounds. Do not introduce primitive booleans: §4.1
explicitly excludes them; truth and branching use ordinary library declarations.
Then grow composition through sequencing and immutable bindings, closing each
extension before advancing. No standalone prerequisite programme is authorized.
