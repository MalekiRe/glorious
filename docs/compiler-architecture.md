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

## Body-derived invocation outcomes and label payloads

The staged analysis boundary now derives callable-control summaries from the
complete frozen body batch before ownership checking. Binding validates full
body, declaration-contract and interface dependency seals. The resulting
per-body invocation product is consumed by shared continuation facts,
PlaceFlow and EscapeFlow; quantity checking reuses those continuations.
Selected implementation bodies and call sites share declaration substitution
with materialization. Summary work is charged to the request's body budgets,
and cancellation returns no partial published product.

Invocation facts distinguish normal return, exact local-label rejoin, outer
transfer, terminal operation, cancellation, divergence and unknown behavior.
They are may-outcomes conditional on reaching a call after strict operands,
not exact guard-correlated storage states. An unobserved call after an unknown
prefix may compose an independently checked static callee contract; only an
explicitly represented label operand supplies a local target. Unknown or
aliased targets do not acquire a destination from a bottom return type.

Label payloads are typed projections from the same control alternatives onto
evaluated explicit or captured inputs. Both ownership and escape instantiate
these relations through the existing read-only invocation input adapters.
Missing projections require independent frame-independence proof, not an empty
reference footprint. Label exits retain payload snapshots and backing loans
until rejoin; actual invocation consumes its input snapshots before temporary
receiver and argument owners are released. Closure formation does not execute
the enclosing body's label transfers.

This slice fixes helper-driven label ownership and reference transfer, not
complete guarded resource analysis. Operation/cancellation ownership states
still use their conservative existing path. Generic unknown callbacks,
nominal payloads without input provenance, unified storage identities and
structural fusion of closures capturing outer labels remain open. The latter
has an active failing source regression; this checkpoint does not relax its
label-lifetime check or claim captured native/mixed execution.

## Lexical label dependency rules

`core/label_dependencies.rs` produces the lexical free-label dependencies of
Core subgraphs. Direct transfers and first-class label values reference the
same generative identities. Union combines dependencies; a `Label` discharges
its own brand only in its body. A declaration in a sibling subgraph cannot
discharge another reference. Closure bodies participate because this is code
dependence, not evidence that formation executes those bodies.

Elaboration uses these rules for result contextualization and unfused closure
rejection. Independent Core validation checks closure dependence again without
trusting source diagnostics. Mandatory-tail validation consumes that same
derived product, and escape checking queries the immutable product retained by
shared continuations. The old transfer/value scans and separate tail/escape
dependency walk are removed. Graph inputs are checked, and missing, cyclic or
unqueried input cannot establish independence; consumer binding validates the
retained projection, including label-value brands.

This product covers lexical references, not arbitrary value-alias propagation,
higher-order control contracts or a fusion proof. It prevents first-class
label literals from bypassing the existing source/Core boundary while the
full label-bearing callable representation and structural fusion remain open.

## Label-bearing snapshots and normal invocation results

The existing escape value/storage domain now retains label brands through
aliases, aggregates, invocation stores and capture formation. Owning a captured
label does not make its destination frame-independent. A label boundary checks
its outgoing result and pre-existing storage identities, including pending
outer exits against their own snapshots rather than a sibling's current state.
The lexical dependency product remains the authority for literal label brands;
this adds no separate Core alias walker.

The shared body-derived invocation relation projects ordinary return payloads
as well as label-transfer payloads. Both ownership and escape instantiate
explicit and captured input projections through the same input adapters used
by stores. Known ordinary-result projections augment the existing declared
reference/callable result contract; unknown fields neither erase that contract
nor prove an empty footprint. Ownership preserves the declared result before
installing extra roots and before releasing invocation temporaries.
Normal payload origins also reuse the checked call-result partition relation:
separate unique-reference leaves remain distinct even when their frozen input
provenance is represented by an array wildcard. Transfer payloads do not acquire
normal-result partitions from a bottom-typed call.

These are may-dependencies, not a complete guarded storage product or permission
to materialize outer-label closures independently. Structural fusion, nominal
label-bearing callable authority and opaque-result coverage remain open.

## Positive observations under incomplete coverage

Invocation evidence retains guarded observed executions independently of its
unconditional coverage gap. The public coverage view remains unknown when a
prefix, handler, resource limit or unresolved invocation leaves missing paths;
specializing an observed guard cannot discard that gap. The bound invocation
product may nevertheless retain payload dependencies from observed paths.
An independent static callee contract can settle invocation coverage without
erasing more precise observed result dependencies.

Escape and ownership add these positive ordinary-result dependencies to their
existing snapshots even when invocation coverage is partial. Ownership retains
its conservative normal/abrupt state and cannot infer disposal permission from
the observations. This is the distinction between retaining a known possible
dependency and proving that no other outcomes or dependencies exist. It does
not supply missing higher-order result projections or complete guarded storage
states, and adds no independent Core reconstruction.

## Nominal label authority and callable views

`types/label.rs` constructs compiler-owned nominal label types using the
existing nominal type algebra. An opaque invariant identity represents the
lexical brand; the payload remains an ordinary mapped type argument. Generic
substitution and canonical identity therefore retain the brand without adding
an ABI refinement that could be joined onto an unrelated function value.
Only this nominal subject supplies intrinsic `Label<T>` evidence. Ordinary
bottom-returning functions do not, and distinct brands cannot unify merely
because their payloads agree. The old terminal-function argument heuristic
for inferring label-only generic payloads has been removed.

The shared intrinsic `Fn` view shifts the payload under the callable binder.
Call checking and concrete invocation validators consume that directional
view, but the actual value and inferred generic arguments keep their nominal
type. Core and the succeeding label-construction validators check the retained
brand; runtime construction also checks the destination payload. Label use
queries return the duplicable interval, while payload types do not imply
resident ownership or destruction. Replay consumes the ordinary owner quantity
product, not a replay-specific exception for labels.

Direct borrowing rejects nominal labels during elaboration. When a generic
loan's referent is not concrete until specialization, demand discovery checks
its frozen ownership-loan obligation using the specialization type mapping and
reports a source error. Independent Core, Control and concrete loan validation
reject malformed products as well. This uses the existing loan and place
products, not another source/Core borrow walker.

This is a nominal authority migration, not complete label conformance. The VM
still uses its existing label control carrier and a physical callable view at
emission; that representation is not a source function pointer or proof of
correctness-required structural fusion. Full proof-carrier erasure, active
destination resolution across opaque/structural callable boundaries, captured
outer-label fusion and native/mixed execution remain separate open obligations.

## Resolved invocation targets and label address obligations

The shared callable-control execution relation now records borrow observations
with their actual input value and invocation context. A structural `Fn`
parameter does not erase an incoming label's identity in that relation.
Binding the sealed batch exposes positive label-address obligations to source
validation, including observations after an unresolved prefix and through
captured inputs. These observations do not prove the absence of other borrows;
the concrete frozen-loan check at specialization remains required.

Invocation evidence separately classifies the callee value itself. An exact
local generative label is distinct from a named helper that eventually exits
through that label. A direct-transfer lowering proof requires complete coverage
and one local label callee, with no other callee alternatives. Symbolic, outer,
mixed and incomplete targets do not acquire this proof from a bottom result or
the helper's transfer outcomes.

Evaluation lowering binds that same immutable product already owned by
PlaceFlow. It emits strict callee and payload evaluation, then replaces only
the proved invocation with the existing direct-transfer operation. Control,
ownership, cleanup and runtime lowering consume the ordinary label-exit path.
The callee-producing helper is retained; skipping its body would erase effects
or obligations before the transfer. Stale Core input is rejected at binding.

This resolves local invocation edges, not full helper/closure fusion or
proof-carrier erasure. In particular, tuple-pattern lowering still attempts to
materialize a label as a callable resident. The source execution regression is
active rather than weakening the non-addressability rule or widening native
storage to make labels addressable.
