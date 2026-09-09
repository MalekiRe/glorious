# Compiler architecture contract

The language and standard-library specifications define correctness. This
document defines how we organize the implementation; it does not alter those
specifications or waive any conformance requirement.

## Goal

Represent semantic meaning as shared, typed facts, then derive and validate the
properties required by the next intermediate representation. Avoid teaching
separate passes their own versions of control flow, capture propagation, or
reference provenance. Phase separation is valuable only when the boundaries
preserve meaning and the consumers actually use the shared products.

## Responsibilities

1. Elaboration resolves source syntax and produces validated Typed Core with
   explicit identities and contracts. Later phases must not recover semantic
   authority from source spelling or incidental tree shape.
2. Analysis derives control, storage/provenance, and resource relations from
   that input. Analyses may depend on one another through explicit products;
   recursive dependencies require a defined fixed point or a conservative
   unknown result, not source-order guessing.
3. Validation checks language obligations against those facts. Failure rejects
   the program; a transformation must not repair an invalid source program by
   silently changing its behavior, ownership, or lifetime.
4. Lowering transforms validated representations under explicit preconditions.
   Preserve semantic identities and evidence, and independently validate the
   receiving representation. Do not recompute earlier semantic decisions.
5. Runtime machinery implements the chosen representation and ABI: allocation,
   leases, frame lifetimes, foreign calls, and execution environments remain
   concrete mechanisms with explicit lifecycle and safety contracts.

## Required distinctions

- A storage owner's identity is distinct from a reference handle's local slot
  and from the referent reached through that handle.
- A closure's capture is an implicit invocation input. Its provenance and
  possible stores must compose with explicit inputs and higher-order calls.
- Normal return, local-label rejoin, outer transfer, cancellation, divergence,
  and unresolved behavior are distinct control outcomes. Preserve evaluation
  order and branch/return guards when joining resource states.
- Missing observations and analysis limits mean unknown, not an empty set of
  effects, borrows, exits, or ownership obligations. A known empty result needs
  positive evidence of complete coverage.
- Source Copy, byte relocation, borrowed access, and ownership transfer are
  different operations even when they use similar physical instructions.

## Rule and product design

Use small typed rules with explicit premises and conclusions. Their
implementation can be ordinary Rust or Glorious functions; declarative syntax
is not a substitute for correct domains, composition, or invariants. Local
rewrites and global dataflow analyses are different mechanisms and should not
be forced through one abstraction.

Prefer immutable published products with identities/dependencies that allow
consumers to reject stale or mismatched evidence. Keep mutation inside the
producer or solver. Unknowns, resource limits, cancellation, and diagnostics
must remain explicit parts of the contract.

For each change, identify the authoritative fact producer and its consumers.
Extend that producer instead of adding a consumer-side special case. If a
boundary cannot express the needed fact, change the boundary and migrate its
consumers rather than recovering the fact independently downstream.

## Incremental migration and acceptance

The initial consolidation target is the Typed Core control/ownership boundary:
shared continuation facts and guarded invocation outcomes consumed by ownership,
escape, and quantity checking. Storage/capture provenance follows the same
producer/consumer discipline. Existing callable-control summaries are useful
building blocks, but their presence alone does not establish integration.

For each migrated slice:

1. Preserve a regression demonstrating the old failure or disagreement.
2. State the shared product's invariants and unknown behavior.
3. Migrate the actual consumers and remove the displaced inference path.
4. Test aliases, aggregates, captures, higher-order composition, branches,
   abnormal exits, and invalid/stale inputs where applicable.
5. Run relevant fresh/decoded and VM/native execution gates when the change
   reaches those boundaries. Report known failures rather than masking them.
6. Commit and push the verified checkpoint, documenting what remains open.

Do not count a renamed visitor, an unused fact table, or a broad rewrite without
consumer-level evidence as completion. Full compiler/library conformance and
self-hosting remain separate end-to-end acceptance requirements.

## First migrated boundary: local continuation facts

`crates/grandiose-stage0/src/core_continuations.rs` projects Typed Core into
source-ordered operand, choice, transfer and label-rejoin rules. It solves their
dependencies once and publishes a shared immutable product. PlaceFlow owns that
product, lifted closures reuse it, and escape and quantity checking validate
the same control-input projection before querying it. The previous recursive
continuation query embedded in PlaceFlow has been removed.

Possible normal return and possible nonlocal exits are independent facts. A
prefix may either return or leave to another label; a later definite transfer
must not erase that alternative. Unknown invocation exits remain unknown, and
an enclosing label can consume only positively known matching targets or
conservatively retain a possible rejoin. This product proves strict-suffix
unreachability, not complete absence of effects or cancellation.

The rule tests cover sequence/choice composition laws, conditional and definite
transfer payloads, exact label identity, stale/missing inputs, and a deeply
shared graph without recursive expansion. Source regressions check that both
branches preserve the correct owner state after rejoining, including rejection
of a double use. See `conformance/implementation-progress.md` for gate results.

This is the first migrated slice, not the end of the architectural work.
Interprocedural guarded resource states, complete operation-handler control,
and shared storage/capture provenance still require consumer-level migration.

## Capture formation boundary

`crates/grandiose-stage0/src/capture_formation.rs` projects each frozen capture
into ordered formation actions: retain contents, then borrow, copy, or move the
source. It also defines the resident type and the path to its captured contents.
Core callable contracts, PlaceFlow capture snapshots and formation, EscapeFlow
dependencies, and UseFlow source-state classification consume that projection.
Core, ownership and escape checking share the sealed environment shape check.

A borrowed reference capture retains two distinct dependencies: the source
slot holding the handle and any backing places reached through the handle.
Copying or moving retains the latter without borrowing the former. Nested
callables carry their existing dependencies through owned aggregate wrappers.
Formation mode does not establish shared or unique invocation authority.

This consolidates formation rules, not the entire provenance analysis. The
invocation migration below shares store rules, while storage identities and
fully guarded outcomes still need a common published product across analyses.

## Captured and explicit invocation inputs

`crates/grandiose-stage0/src/resident_invocations.rs` derives typed may-store
edges from explicit and captured inputs through one invocation relation.
PlaceFlow and EscapeFlow supply read-only projections of their resident
snapshots and apply the resulting edges to their own storage graphs. Their
previous separate logical/captured call-store inference paths are removed.
Nested captured callables use the same worklist rules as argument callbacks;
identical invocation inputs share expansion. Unknown capture coverage is
reported separately from positively represented empty environments.

Callback authority comes from the declared callable parameters and `Fn`
bounds, including implementation bounds, not merely from substituting an
actual closure for an unconstrained type parameter. Declared independently
elided lifetimes remain distinct from substituted resident lifetimes.
`callable_declarations.rs` supplies declaration identities and selected
implementation substitutions to analysis and materialization; both consumers
share the checked binding algorithm. Factory forwarding retains typed capture
inputs without inventing physical environment fields or brands. Containing a
captured owner does not make the callable resident alias that owner.

Consumers apply these relations only after strict operands complete according
to the shared continuation product. This is not a complete interprocedural
execution/control relation: it models possible stores, not exact invocation
order, branch guards, transfer or cancellation states. Storage identities and
environments remain per-consumer, and unresolved inputs retain their observed
footprints rather than proving complete coverage. The source regressions cover
direct, borrowed, higher-order, nested and trait-selected invocation, ordinary
non-invoking generic forwarding, and abrupt argument evaluation. They do not
establish full guarded provenance or captured native/mixed execution.
