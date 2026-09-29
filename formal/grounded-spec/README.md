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

**Completed subset: unit, selected fixed/target-width nonnegative integer and
decoded character literals, grouping, place reads, sequencing, immutable and
mutable initialized bindings, whole-local and nested tuple/structure moves, restoration and assignment,
optional type annotations, tuples/projection, fixed-array construction, non-generic transparent aliases, structural constants,
non-generic finite-inline nominal data over duplicable fields, direct
nonrecursive first-order calls, and immediate structural pattern-callable
application.** Records, tuple structs and enum variants retain declaration
identity; projection and deconstruction check field visibility. The boundary
is decoded declarations/expressions to logical values and lexical post-states. Normative basis:
§§2.2–2.3, 3.2–3.4, 4.1–4.4, 5.1–5.3, 6.1–6.3, 7.2–7.3 and 13.1. No
previous proof modules are imported. The objective is the full
specification, not a feature percentage.

`Grounded.correctness` proves finite evaluation, result typing, lexical-state
preservation and uniqueness of both result and final environment. Every
constituent consumes its predecessor’s actual post-state. Initializers execute
before their binding is introduced; their result and post-state construct the
body environment. Scope exit removes its own binding prefix and retains
changes to surrounding locals. Copy/discard
sites require explicit duplicability evidence. `closed_correctness` constructs
the empty environment rather than assuming it. Admission supplies no successful
execution or normalization witness. Exact scalar admission theorems and `unit_agreement` remain connected
to this general result. This is lexical-state preservation, not physical-machine preservation.

Tuple arity is preserved: unit is the empty tuple; grouping and a singleton
tuple are distinct. Constituent evaluation and positional value typing are
proved inside the connected theorem, not left as separate prerequisites.
Projection derives its actual resident and typing from the evaluated tuple;
an in-range runtime selection is not separately assumed. Out-of-range tuple
projections cannot be admitted. Physical evaluation traces remain outside this
logical big-step boundary.

`Place` selects the nearest lexical root and a field path. `ProjectionType`
supplies tuple bounds, nominal-field visibility, and the source-resolved child
index to both reads and writes. `PathType` composes those indices along the
field path. `ProjectionType.access` proves that runtime selection uses that
exact index; it no longer merely produces some runtime index after the fact.
Expression projection, place reads, assignment, and their connected proofs
consume this strengthened contract. No second resolution pass or index table
is introduced. The old separate tuple-expression projection rule is removed. Assignment
evaluates the RHS first, then updates the selected place in that actual
post-state. It requires a mutable root. A live destination requires a legally
discardable old resident (currently duplicable, without hooks); restoring a
vacant selected subtree does not discard an old value. Nested writes require
present ancestors, not complete siblings or an initialized destination.
`PathType.write` and `EnvironmentTyped.writePlace` preserve the computed partial
state and prove readback of an initialized replacement; clearing makes the
selected path unreadable. Expression correctness consumes these operations.

Typing now produces the final initialization context, rather than requiring
every expression to preserve its input context. Runtime slots contain either
a resident or a vacancy; a vacant nearest binding still shadows outer bindings.
Whole-root and nested `move` extract the actual selected resident and clear
that path, even for a duplicable value. `EnvironmentTyped.takePlace` constructs
the transition and proves the selected path unreadable afterward. Reads and
moves require the selected subtree to be complete; later arguments and bodies
consume the preceding initialization context. Assignment restores a vacant
subtree of a mutable root after evaluating its RHS. Function
parameters and pattern binders start initialized; scope exit removes only its
own prefix and preserves changes to outer slots. Vacancies now reside directly
in the resident tree; the separate optional-root wrapper and pattern-binding
conversion are removed. `ValueHasType.initialized` proves that every typed owned
result contains no vacancy at any depth. Reads check the selected subtree, and
extraction uses the same path write as restoration, replacing the selected
resident with a vacancy rather than retaining its payload elsewhere.
`Evaluates.move_invalidates` proves that every actual move makes a subsequent
read of that exact path fail, including nested paths in already partial trees.
Its proof needs neither source admission nor an assumed post-state invariant.
The shared operational readback theorem also supplies typed write preservation;
the superseded typed-only child-readback proof is removed.
`Evaluates.move_restore` proves the exact operational round trip: immediately
writing the extracted resident back to its path recovers the entire original
environment, including siblings, pre-existing holes and shadowed bindings.
This is not merely equality of the selected field or preservation of its type.
It does not grant source-level write permission to an immutable place.
Whole-root and nested writes now share one path-update implementation.
The static initialization context now stores finite field overrides rather than
a whole-root Boolean. `ResidentTyped` is the authoritative storage typing
relation; owned-value typing is its fully initialized specialization, not a
second value-typing relation. `ResidentTyped.complete` recovers owned typing
and proves physical absence of vacancies from complete initialization evidence.
Reads, moves and writes share `Initialization.Access` along the exact coordinates
produced by `PathType`. The former read-only `Initialization.Ready` relation is
removed. Source moves and assignments compute the next mask with the same
`Initialization.write`; `ProjectionType.access` and `PathType.write` prove that
the actual resident replacement has that state. `correctness` consumes those
proofs and preserves partial initialization through arguments, bodies and scope
exit, without assuming any runtime post-state.
`Initialization.Access.write_frame` preserves the selected state at every
disjoint coordinate path, including siblings below a shared prefix. Complete
retained subtrees therefore remain readable.
`HasType.no_whole_read_after_clear` rejects a whole-root source read after any
accessible nested clear. `Initialization.setChild_complete_iff` characterizes
restoration: the replacement and every other child must be complete.
`Initialization.Access.restore_complete` proves that writing a complete value
back to an extracted path recovers whole-root completeness when the root was
complete before extraction. These laws accompany the existing exact physical
move/restore round trip.
Strict Lean checking and the connected correctness, nested take/write, sibling
framing, restoration and whole-read rejection axiom audits passed with only
`propext` and `Quot.sound`. Conditional ownership joins, destruction of surviving
fields, exact-linear disposition, and reference-mediated mutation remain at
their ownership and borrowing boundaries; this is not whole-language soundness.
Array indexing, enum payload writes and writes through references are not
silently treated as ordinary field projection.

The explicit target supplies its positive pointer width. Signed and unsigned
fixed widths remain 8/16/32/64/128; `usize/isize` use the target width throughout
admission, execution and result typing. Integer checking never wraps. Characters
exclude surrogates and values above U+10FFFF. Array construction reuses the
existing constituent relations; admission enforces homogeneous residents,
exact arity and target-representable length. Known-empty arrays are resident-free.

Alias bodies resolve finitely to existing types, including nested tuple/array
types; binding annotations consume that resolution. No alias identity is added
to runtime values. Constant references select declared structural initializers,
check their declared types, and evaluate them in an empty local environment.
Their bodies are admitted in the declaring module, not the caller’s module;
the caller must have access to the constant itself.
The existing evaluation relation and correctness induction perform the work;
there is no separate constant evaluator or assumed evaluated-value table.
Declaration lookup is supplied as decoded maps; whole-package validation,
duplicate-name rejection, generic schemes and source name resolution remain open.

Nominal construction consumes the existing ordered constituent relation and
produces tagged nominal values, never structural tuples masquerading as owners.
One declaration supplies constructor schemas, projection indices and field
types. Private access includes descendants; package/parent/public visibility
is explicit. Aliases cannot change a nominal field’s access rule. Numeric
tuple-struct access and named record access remain distinct; enum payloads
cannot be projected without matching. Copyability checks every variant and
respects manual principal restrictions. Inline type expansion checks every
field and rejects direct recursive layouts and duplicate record field names.
Empty arrays remain resident-free but must have valid element types. This also
repairs the previously unchecked malformed element type of an empty array.

Direct calls select a resolved function identity, check visibility, exact
argument arity/types and distinct parameter names, and admit the actual body
in its declaring module. Arguments evaluate in order. Their proved value
typing constructs the isolated parameter environment; caller locals cannot
leak into the body. Body admission is a recursive static derivation, not a
promise of execution: correctness carries both argument and body induction
hypotheses through actual invocation. Recursive call cycles have no finite
admission derivation in this subset. Structural constants still exclude calls.
Computed callees, first-class function values, captures, effects, recursion and
named-label exits are not included in this direct-call boundary.

Immediate pattern-callable application supports binders, wildcards, nested
scalar/tuple/array/nominal constructor patterns and named structural constants. It retains the callable’s
argument list: one tuple argument is not two arguments. Source-ordered selection
executes just the first matching body; bindings remain clause-local. Each body
receives the caller environment after argument evaluation and the declared
result type. The selected body’s outer-local updates survive clause exit.
`Covers` is an inductive constructor-space specialization, not a future-match
assumption. Its proof constructs actual successful dispatch for every typed
subject. Pattern binding preservation then constructs the body’s typed
environment; both results are consumed by `correctness`. Duplicate binders
are rejected. Every clause needs a static typed datum distinguishing it from
previous clauses, excluding unreachable clauses without assuming a result
for the subject expression. There is no primitive Boolean or library-name
dispatch rule.

Named constants are retained in `PatternSource`. Their initializers are checked
by ordinary source typing; `correctness` constructs unique normalization using
the same `Evaluates` relation, not a second evaluator or a supplied value table.
Coverage and body typing are checked over those constant normal forms; their
existence is proved before either check is consumed, so missing normalization
cannot make admission vacuous. A normalized literal retains its declared type,
including the element type of an empty array. Structural equality is total and
proved lawful; it calls no user `Eq` and does not ownership-deconstruct a
constant’s private representation. Comparison-only nodes created during
coverage specialization cannot be admitted as typed source patterns.

This pattern boundary is decoded immediate application, not stored callables
or a proof of library `match`. Source record/remainder expansion, borrowed
patterns, first-class callable identity and captured-storage semantics remain
open at their respective source/borrowing/callable boundaries. In particular,
this does not prove source capture formation or compatibility between a
materialized callee’s captured loans and argument evaluation.

Nominal scope excludes generic instances, indirections, hooks, nonduplicable
owners and non-exhaustive-enum deconstruction. Constructor arguments are
already ordered decoded expressions; source record-initializer elaboration
and name resolution are not proved. Parsing, inference, prefix negation,
floating conversion, static strings, partially initialized aggregates, loans and
effects remain open. There is no physical-storage, allocation-failure, package-admission
or compiler-realization claim. Big-step evaluation is not a small-step theorem.

Verification: strict `lake build` passed. The connected theorem reports Lean’s
standard `propext` and `Quot.sound` (the recursive matcher and its equations
introduce the latter dependency). No bypass axioms or admitted proofs. Reproduce:

```sh
lake build
lake env lean -DwarningAsError=true -DautoImplicit=false --stdin <<'LEAN'
import Grounded
#print axioms Grounded.correctness
#print axioms Grounded.closed_correctness
#print axioms Grounded.integer_admission
#print axioms Grounded.character_admission
#print axioms Grounded.unit_agreement
#print axioms Grounded.ValuesHaveTypes.select
#print axioms Grounded.Covers.selectArm
#print axioms Grounded.PatternType.bindings
#print axioms Grounded.PathType.write
#print axioms Grounded.EnvironmentTyped.writePlace
LEAN
```

## Construction order and size reviews

Proceed serially, closing each extension through the same end-to-end theorem:

1. Ordinary values, non-generic constants and aliases: connected as described above.
2. Nominal data, constructors, visibility and projection: connected for the subset above.
3. Direct calls and immediate structural-pattern application: connected; remaining pattern/callable boundaries above.
4. Mutable places, initialization, assignment and explicit moves: whole-root and
   nested tuple/structure moves, partial restoration, sibling access and
   incomplete-aggregate rejection are connected through the general theorem.
5. Affine/exact-linear ownership, destruction and scope cleanup.
6. Borrowing, provenance, lifetimes and returned references, including required
   Rust-style implicit reborrowing of existing references (§5.3). Expected
   reference types select unique/shared derived loans, not ownership transfer;
   unconstrained generic owned inputs do not automatically reborrow. Preserve
   storage identity, parent permissions, initialization restrictions and actual
   child-loan lifetimes, including loans retained by returned references.
   Explicit moves remain transfers. Source elaboration must select these same
   loan operations, not introduce a separate implicit-borrow permission model.
7. Callables, captures and invocation quantities.
8. Recursion and finite/infinite execution guarantees.
9. Labels, nonlocal transfer and proper tail invocation.
10. Effects, handlers, replay, cancellation and cleanup.
11. Generics, traits, constraints, inference and static evidence.
12. Physical representation, allocation/exhaustion and unsafe operations.
13. Floating-point contracts and authenticated static literal storage.
14. Source authentication, packages, resolution and elaboration.
15. Foreign/runtime/ABI and compiler-correctness composition; full normative audit.

This is dependency order, not disconnected workstreams. Move a requirement
earlier when its current consumer needs it. Do not add a standalone admission
checker without a present semantic obligation requiring one. No primitive
booleans: truth and branching use ordinary library declarations.

At verified checkpoints, review size, duplicated reasoning and unused concepts.
Simplify where meaning and guarantees are preserved; do not introduce a generic
framework merely to shorten local proof plumbing. Pattern coverage and binding
preservation are connected immediately to the same expression theorem. Runtime
typing supplies one constructor decomposition to both proofs. Place and
expression projections share field selection; tuple and nominal updates share
positional typing. Arrays and constructors share constituent evaluation;
constants reuse ordinary evaluation. The local proof simplification reduced
the module from 1,846 to 1,829 Lean lines, including comments and blanks, without
changing existing theorem statements or semantic definitions. It removes a
redundant path split, combines impossible constructor cases, shares move
decomposition, and reuses the generic binding lookup result. Strict proof
checking and the connected correctness/invalidation/restoration axiom audits
passed unchanged. The development remains one Lean module; no standalone
admission checker or speculative proof module is added.
