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
proof-carrier erasure. The invocation migration exposed tuple-pattern lowering
trying to materialize a label as a callable resident. The following erasure
boundary addresses that failure without widening native callable storage.

## Checked runtime proof-value erasure

`runtime_mir/proof_erasure.rs` derives an immutable representation plan from
the validated closed executable batch. It does not discover label targets or
replace helper bodies. A label carrier whose consumers are already resolved
control edges can become unit; tuples, arrays, internal projection references,
local layouts and matching direct-call signatures use the same physical map.
The direct leaves retain their generative destination and cleanup. Ordinary
resident fields and captured data remain present.

Proof-bearing call and abandonment-cleanup edges connect callers and callees
into ABI components; environment and host-resident cleanup signatures also
participate in retention.
An unresolved indirect consumer, incompatible structural callable boundary,
foreign/effect payload or unsupported identity-bearing layout retains its
whole component. Missing transformation evidence cannot authorize a unit value
at a still-callable boundary. Nominal generic identities, effect-family
arguments and specialization keys are not recursively rewritten into unit.
This is a value representation map, not type equality or new source coercion.

Applying the plan checks its exact input batch. Original executable validation
runs before erasure, so malformed label construction cannot be laundered into
a valid unit constant. Executable control tables are re-frozen after removed
materializations, and frame/transfer layouts are derived again. The receiving
runtime program independently validates local instructions, cleanup and every
cross-function ABI before emission. Source/Core addressability checks remain
in force; the native callable-storage rule has not been widened.

This migration repairs stored resolved label products, including generic
forwarding at O0. It does not finish proof erasure: components with residual
label invocations, label-bearing nominal/callable layouts, or operation payloads
still retain the prior carrier. Correctness-required helper/outer-label fusion,
and native resident captured-callable execution, remain open obligations.

## Staged lexical closure fusion

Ordinary function elaboration can publish pending lexical closure obligations
inside the staged body batch. The lexical-dependency product admits them only
under their enclosing destination binders. Standalone Core validation remains
strict: pending code is not an independently executable closure. Constants and
value initializers do not gain this staged permission. A control-dependent
constructor must retain its own nominal environment or an explicitly erased
callable view; unit or another constructor's environment is not that view.

`core/control_fusion.rs` accepts only the dependency-bound callable-control
batch. Source bodies, static declaration selections and closure constructor
authority come from that sealed product. The transform carries each value's
checked semantic contract together with its physical representation; explicit
and captured inputs use the same binding form. Aliases and projections do not
require a second analysis that reconstructs callable identity from the arena.

Control environments are closed tagged products. Original capture formation
creates their resident fields at the original evaluation point; invocation
aliases those same fields, including through shared/unique receiver loans.
Labels remain explicit proof fields until source escape checking and checked
runtime erasure. A mutable erased callable dispatches on its current constructor
tag, not an earlier observation. Compatible branch results share one checked
layout join; incompatible layouts reject rather than reinterpret residents.
Selected bodies are structurally expanded under fresh lexical identities, with
strict receiver/argument order and source unsafe scopes preserved. Transfers
use the ordinary Core label path, so ownership and cleanup are derived after
fusion instead of modifying an existing ownership ledger.

Before installing transformed Core, the service validates the original source
resource and escape obligations using the same resource-checking entry point
as ordinary bodies. The receiving Core is independently validated and receives
fresh bound control and resource analysis. Fusion cannot make an invalid generic
discard, double use or escaping label legal by removing the offending code.

PlaceFlow now publishes the per-callable loan/resource products for the frozen
arena once. Escape checking selects the closure's own loan journal while
examining its body, then restores the enclosing journal at formation. Ownership
and MIR lowering consume the same products; their separate closure-analysis
loops have been removed. This fixes the former mismatch where borrowing an
owned capture was checked against the enclosing function's loan events.

The shared invocation values distinguish a value's origin from the storage of
its current place. Binding, argument transfer, owned capture formation and
pattern binding create new slots; projections retain structural subplaces and
moving a reference handle preserves its referent. The payload relation can
therefore express a reborrow of an explicit or captured input loan without
equating a copied value with the storage it came from. Both ownership and escape
instantiate this relation through their existing frozen input adapters. Missing
storage identity remains unknown. Isolated closure inspection retains its
captured destination inputs but does not publish hypothetical exits as effects
of formation. The real invocation supplies the destination and payload snapshots.

This is an integrated but incomplete fusion slice. The entry condition covers
outer-label closures and captured label aliases, not every label-bearing helper
family. Mandatory-tail activation fusion lacks the required contracts and
explicitly rejects in transformed code. Heterogeneous
environment layouts, projected ordinary nested captures and some nominal/result
representations remain unsupported. Recursive expansion rejects without a
finite proof. Output is bounded and charged to the request, but expansion still
needs finer-grained request cancellation/work accounting. Full helper fusion,
complete proof erasure and ordinary native captured-callable storage remain
open; tagged lexical fusion is not an implementation of the latter ABI.

## Handler binders through structural fusion

Handler-clause and continuation brands identify their actual enclosing Core
handler as well as the body owner and clause index. Explicit resumption binders
retain their generative resumption identity; a literal resumption reference must
match that binder's identity, spelling and complete callable contract. Nested
handlers no longer collide merely because both contain a first clause.
Fingerprinting encodes the handler edge structurally, not by arena offset.

Core validates those lexical declarations and references independently. The
existing Evaluation MIR region validator checks the receiving binder/contract
relation, and Control MIR resolves resumption instructions only by their exact
identity. The previous name-based fallback is removed. Aliases and selected
capture inputs are ordinary local values, not fresh generative resumption
references. Capture selection normalizes the latter representation at the
producer; it does not infer new alias authority in a lowering consumer.
Owned-only callable values infer copy-or-move capture formation, rather than a
shared loan that cannot supply their declared invocation authority.

Fusion reserves each new handler binder before expanding its computation and
clauses, rebrands continuation contracts, and substitutes payload and result
types through the same invocation frame as other values. Resumption calls remain
ordinary checked calls; they do not inline a protected computation or bypass
deep-handler reinstatement. A physical handler result change incompatible with
the already-bound resumption ABI rejects explicitly. Ordinary closure bodies
cannot resolve an ambient resumption instruction: captures must supply values.

This extends lexical fusion, not general native handler support. Resumption
capture admission now uses the shared lifetime boundary described below.
Native owned-handler installation is still explicitly unsupported.
Full helper-family fusion and mandatory-tail handler activation transfer remain
open; VM handler composition does not establish those separate contracts.

## Source control lifetimes and resumption capture admission

EscapeFlow's existing resident-value domain carries both label and resumption
brands. Capture formation retains these dependencies through the same ordered
formation actions, aliases, structural fields and storage graph as references.
An explicit handler arm introduces its actual resumption identity; its outgoing
result, pre-existing storage and pending outer-label exits must not retain that
identity when the arm ends. Exit payloads resolve against their own storage
snapshot. Owning a control-bearing closure does not make it frame-independent.
The old independent source resumption-capture alias walker and restricted
immediate-closure rewrite are removed.

The source resource-checking boundary publishes body-sealed capture obligations
from that lifetime analysis before fusion. Structural fusion binds the exact
source body before consulting its environment obligations, including helper
expansion frames. Captured resumptions use the same tagged environment products,
strict formation order and checked invocation substitution as captured labels.
An unchanged body batch reuses its original resource products; a transformed
batch receives independent validation and fresh bound analyses. Missing, invalid
or stale lifetime input does not authorize a transformation.

For an invocation under incomplete enclosing execution coverage, a compiler-owned
nominal label type can supply its invariant destination by matching the shared
lexical binder product. The shared invocation producer emits the strict argument
payload relation and exact target; escape and lowering consume that relation.
An ordinary bottom-returning function has no such nominal authority. This proves
the call conditional on reaching it, not the preceding computation's coverage.

Explicit resumption quantity is checked by UseFlow against shared continuation
facts. The former elaboration-time syntactic call counter and its Core contract
field are removed: summing branch call sites or overlooking aggregate aliases
cannot validate an execution interval. Tail/cancellation declaration admission
remains explicit. Residual replay-safety admission follows an explicit binder's
declared multi-shot capability rather than that deleted counter.

Composing an aggregate capture also requires cleanup to relocate partially
consumed storage. The VM layout checker now distinguishes ordinary value
validation from storage-layout validation through one recursive layout relation.
Owned projection extraction and tag-only destruction dispatch preserve typed
holes at every structural depth. The selected storage root must still exist;
moving it clears that root, and selecting a hole as a value remains invalid.
This preserves initialization state, not a source Copy or invocation permission.

This is not complete higher-order lifetime analysis. The factory-result
migration below supplies checked constructor/capture relations, not arbitrary
opaque callback behavior. Guard-correlated storage outcomes, full helper-family
fusion, borrowed/cross-frame resumption transfer and native handlers remain open.

## Factory results and owned label payloads

The shared invocation payload relation retains returned closure constructors,
sealed defining-body identities and typed capture projections. Ownership records
these as capture provenance, not ordinary result-reference partitions or aliases
of the callable's physical resident. Escape checking retains the same captured
control brands and loans. Computed captures require an independent owned-type
proof when no incoming projection represents them; unknown reference or callable
contents cannot establish independence.

All source ownership products are staged before quantity checking can inspect
another body. UseFlow binds the checked defining body and its own closure loan
product, and runs its existing quantity solver with the caller's capability
identities. A factory's eager execution and returned capability are one transfer;
blanket outgoing-argument accounting would double-count that capability. Arena
caches are frame-local, while capability keys survive calls. Result alternatives
join instead of adding branch counts. Missing/stale bodies and unbounded recursive
expansion reject; may-outcomes do not become an independent quantity counter.

Fusion consumes the returned-constructor obligations before helper expansion.
Its existing value/input representation now carries closed constructor choices
through captures, tuples, projections, references and result joins. An erased
callable type cannot recover code identity. Compatible choices dispatch on their
actual tags; incompatible or unrepresented joins reject. Local storage updates
retain a conservative union of represented tags across branches and rejoins.
Control-value replacement through captured/borrowed storage remains unsupported.

Runtime label edges, like ordinary block-parameter edges, transfer ownership.
The verifier and VM snapshot all payloads before retiring predecessor carriers
and installing successors, preserving parallel swaps and identity edges. Reusing
or duplicating a consumed carrier rejects. Value provenance moves separately
from storage lifetime, and exact local-label facts retain the existing private
storage requirement. Expired resumption contents remain tainted, not empty.
Native emission transports initialization masks with the bytes, clears sources,
and does not revive moved-out fields. This also prevents source cleanup from
destroying a callable environment still owned by the label result.

This completes the tested finite, checked-body factory composition slice. It
does not supply native captured-callable/handler ABIs, mandatory-tail activation
fusion, arbitrary recursive factories or complete guarded storage analysis.

## Executable resumption value provenance

The bytecode verifier's scalar snapshot-brand vector and separate aggregate
resumption taint are replaced by one structural resident-value domain.
`vm_backend/resumption_values.rs` distinguishes no capability, possible unknown
contents, an exact handler token, and structural product fields. Constructors,
storage moves, constant field projections, owned extraction, record replacement,
effect payload transfer and saved continuations carry this same value record.
Both invocation authentication and frame-escape restrictions consume it.

Joins retain an exact field identity only when all incoming values agree. A
removed field no longer contributes authority to its former owner. Expiring a
handler invalidates its tokens recursively without erasing their possible
control contents; revisiting an installation cannot revive an old token.
Runtime layout matching recognizes a resumption's retained callable signature,
including inside structural values. This type match is distinct from the
live-handler check performed by resumption dispatch.

Product nodes are shared immutable values. Structural growth is bounded; losing
coverage yields unknown, never an empty capability footprint. Opaque memory
access and dynamic-index extraction do not acquire an exact snapshot identity.
Borrowing exposes mutable storage and discards its exact snapshot proof while
retaining possible control contents. General resumption transfer through borrowed
storage or ordinary call frames remains unsupported, as does the native handler
ABI. This repairs resident product composition, not those separate boundaries.

## Generated ordinary callable environments

The native emitter publishes and retains its checked frame layouts and logical
initialization paths with the immutable code/ABI witness. Generated callable
operations and the existing mixed bridge consume those exact plans; the mixed
bridge no longer independently reconstructs its parameter/result layouts or
initialization paths. Register and result layouts must support their complete
resident shape before the native plan is published.

Generated construction uses the existing execution-domain callable registry:
bytes contain a verified definition identity and an authenticated environment
token with an address lease, not a process function pointer or a zero placeholder.
Captured inputs inhabit the same NativeHome/RuntimeCaptureEnvironment storage
used by the VM. Invocation lends those homes and their initialization sidecars
to the selected generated body, then restores the updated residents. Borrowed
receivers retain that same environment; source Copy duplicates owned captures.
Environment destruction dispatches to the checked generated destructor, including
cleanup of partially consumed products. These callbacks implement storage and
dispatch; they do not interpret the source body or invoke the bytecode engine.

Byte transport carries address leases through arguments, results, aggregates,
label edges, tail packets and raw memory. Partial overwrites revoke authority
even when the replacement bits match. Native body/dispatcher scopes retire
compiler-owned stack leases on ordinary, tail and error exits without treating
lease release as source destruction. Scalar reads respect initialization flags;
a moved callable receiver or incomplete source Copy cannot read uninitialized
storage. Capture homes and the trampoline's bounded activation/sidecar storage
share the existing memory and instruction budgets.

Generated VM/native bindings now retain an explicit slot contract from those same
published layouts. The implicit capture prefix is lent storage; explicit inputs
are transferred arguments. Public native registration cannot install this private
contract. Generated callable parameters/results use authenticated resident slots,
not the external callback trampoline ABI. The interpreter retires transferred
inputs at the binding boundary and returns captured slots to their environment.
VM frame planning obtains these resident demands from the linked private binding.
It must not allocate callable/capture homes merely because an external public
callback has a Callable type; scalar-only public callbacks retain their existing
zero-native-byte contract. Generated machine entry requires its bound allocation
and resident runtime before executing even a scalar body.

VM re-entry borrows the actual capture homes from the existing execution-domain
owner registry. It must not introduce a second owned external view: retiring that
view would revoke callable leases still owned by the enclosing environment. Both
engines write initialization changes back through the checked input sidecars.
Zero-byte inputs keep their logical identity through the capture position and
sidecar, not an invented unique address. Missing nonzero owners reject.

The generated adapter binds the original verified source invocation contracts,
environment producers and capture-access proofs as well as tail summaries.
Adapter instructions still receive ordinary graph/ABI validation; their host-call
transport is not treated as the source body's capture consumption. This private
semantic witness is neither exposed nor serialized as portable verified bytecode.
Callback failures retain their original runtime error through native dispatch.
Public external callback/result authority is unchanged.

This supplies tested ordinary captured-callable execution in all-native and mixed
closed graphs. The reference-storage migration below now supplies the ordinary
frame-backed referent contract; environment-lifetime returned borrows remain open.
Native owned handlers, borrowed/cross-frame resumption transfer, full helper-family
fusion and mandatory-tail activation fusion remain separate open obligations.

## Complete normal-result reference coverage

The existing body-sealed invocation product now resolves normal-result payloads
and their reference coverage together. Complete control coverage, at least one
represented normal result, and an authenticated projection for every non-static
reference leaf of every return alternative are required to settle a declaration's
opaque reference obligation. Captured and explicit inputs use the same relation.
Missing shapes, captures, paths, input provenance or alternatives cannot establish
coverage; positive dependencies remain available independently of that decision.

Invocation events retain the evaluated receiver, including its borrow wrappers.
The shared invocation view selects callable code without changing that input's
coordinates. Payload projection records the receiver dereferences; code selection,
direct-label classification and fusion query the same view. Previously, unwrapping
the receiver before publishing the event silently made capture paths relative to
the referent while consumers supplied the original reference handle.

PlaceFlow authenticates the projected leaves against its existing loan/region
snapshot and installs the resolved result aliases before releasing invocation
temporaries. EscapeFlow consumes the same resolution rule over its existing
storage values and retains the returned reference's actual backing owner. Neither
consumer reconstructs closure code or turns an opaque declaration into an external
reference. Ordinary declared parameter-region contracts remain conservative input
unions; body-derived observations cannot erase them.

Core's reference fields remain declaration evidence, not a forged captured-field
ABI. Core validation still checks that evidence; the bound source resource phase
settles its remaining invocation obligations. Lowering consumes the resulting
ordinary loan products, and decoded/executable verification retains its independent
reference and frame-provenance checks. No parallel source walker or new runtime
reference representation is introduced.

This admits the represented factory-produced callable returning a captured loan.
It does not establish arbitrary opaque callbacks, complete nominal/array payload
projection, guarded storage identities, or returns borrowing an owned capture's
storage. Native reference storage is addressed separately below.

## Pattern inspection and resident initialization

The executable pattern product declares its read requirement. A wildcard reads
no payload. Tuple/nominal shells require their root; literal and fixed-array
inspection require a complete value. Explicit nominal fields additionally require
their complete declared value, even when their nested pattern is a wildcard.
The materialized and resident VM matchers consume those same rules. Runtime value
validation now requires complete resident initialization, while storage-layout
validation preserves holes without turning them into readable values.

Generated direct and captured resident patterns use the frame's published logical
paths, including ancestor initialization. Control flow checks the required flags
before any payload load. Masking a result after an uninitialized LLVM load would
not be safe. Enum tag-only cleanup continues to inspect partially consumed shells;
it does not demand unselected payloads. Borrowed pattern auto-dereference now
uses the reference-storage contract below; handle flags never stand in for
referent initialization.

## Native reference identity and backing initialization

`vm_backend/native_residents.rs` extends the existing resident byte-transport
domain to reference handles. Callable leases and reference origins share copy,
relocation, partial-overwrite invalidation and scope retirement. The former
`NativeHome` reference cache and its special leaf reader are removed. Home
stores, native layout reads/writes, raw transport, generated instructions and
mixed invocations consume the same handle-address metadata. A reference still
occupies one genuine machine pointer; its logical projection is not inferred
from numeric pointer equality. Distinct zero-byte fields retain distinct paths.

Reference origins retain either the existing home weakly or a native reference's
shared logical initialization view. A generated view names the exact published
frame layout, logical paths and writable flag storage, guarded by its frame's
live lease. It reads and updates those actual flags, not a persistent shadow
mask. VM dereferences of a generated reference and generated dereferences of a
VM home use that same backing owner. Borrow formation does not read a complete
value: unique handles can retain restoration authority, and shared handles need
the resident shell. Dereference and pattern operations check their own required
initialization before generated payload loads. Moves preserve the destination's
holes, clear the referent and retain the checked unique restoration handle;
stores restore the source mask. Payload transfers remain LLVM instructions,
not interpretation or reconstruction of a VM aggregate by a runtime callback.

Borrowed pattern layouts and logical paths are published with the native frame
plan. A bounded per-pattern scratch mask observes the authenticated referent
immediately before inspection, with separate space for nested dereferences.
Ordinary pattern control flow then applies the shared no-read/root/value rules.
No user code or storage mutation intervenes between that observation and its
reads. This is not a reference handle's initialization mask.

Generated resident reads require an existing origin even when unsafe execution
is enabled. Only explicit unsafe raw/native adoption may establish an external
pointer promise; public callback/result admission and private generated slots
select that contract explicitly. Raw borrow construction uses the same native
origin producer in both engines. Compiler-owned machine and mixed-bridge scalar
slots share scope retirement. Expiring a frame invalidates its backing views
before any subsequent reference access; copying a handle does not extend that
lifetime or run source destruction.

This completes the tested local-frame/captured-handle move, restoration and
borrowed-inspection slice, not all captured-storage lifetime contracts. The
capture-storage boundary below extends it to returned loans of owned captures.
Native owned handlers, resumption transfer and full fusion remain separate
outstanding boundaries.

## Returned loans of callable-owned storage

The shared invocation payload relation distinguishes returning a captured value
from borrowing its resident storage. Its capture-storage projection retains the
receiver path, sealed callable type, resident type and logical fields. Ownership
keeps the real receiver owner for overlap and lifetime obligations, while escape
keeps that owner's existing storage identity. Nested capture paths are logical
invocation coordinates, not invented physical Core environment fields.

Both consumers apply the new projection through their ordinary invocation input
adapters. Dereference reads and writes follow the same stored capture path.
Assignment snapshots the RHS before replacing destination provenance. Exact
ordinary destinations permit strong updates; ambiguous aliases and type-grouped
capture destinations retain a union of possible contents. Loan liveness closes
over the existing loan graph, so a live alias also retains references subsequently
stored in its referent. Lexical scope exit then checks those same live loans.
Escape joins omit an absent declaration alternative only when the shared product
positively covers every result reference; an unknown value remains unknown.

Callable-control summaries retain the symbolic explicit and captured residents
actually used to derive them. Abstract and observed return contracts use the
same payload projection rules. A complete compiler-branded constructor type in
the same sealed body's generic namespace can select an independent contract
after an unobserved prefix. Matching only an environment brand, an erased type,
another specialization or a stale body cannot select it. This settles the call
conditional on reaching it; mutation coverage and its guards remain unknown.
Cross-owner generic instantiation still requires an independently checked mapping.

Field assignment now uses the ordinary field-selection/type/privacy producer
and its explicit dereferences before checking write permission. Unique referent
authority is distinct from permission to reassign the handle's binding. The
separate assignment field walker is removed.

Generated capture-slot borrows resolve the existing environment home through the
exact lent initialization sidecar. Equal payload addresses cannot identify
zero-byte owners. During a machine invocation, the home's initialization state
is the generated code's actual writable flag view; nested entries lend and return
that same ownership. Returning or failing a loan detaches its flag pointers
before their stack storage expires. Ordinary local borrows retain their existing
frame lifetime. The former copy-in/copy-out initialization reconstruction is gone.

Generated import adapters derive their transitive ABI layouts from the checked
program-wide nominal table, also used by VM native storage. The adapter validator
requires every added descriptor to occur unchanged in that exact source graph.
The common native ABI closure producer supplies both import validation and
generated resident obligations; its duplicate generated-layout walker is removed.
Function-local Copy descriptor demands need not grow through reference handles.

This is not complete guarded storage analysis. Capture destinations grouped by
resident type cannot prove exact slot replacement. Explicit environment-destruction
retirement for every runtime home/borrowed-slot formation path still needs a
lifecycle audit; returned handles must not be treated as source ownership.
Native handlers, general resumption transfer, full fusion and complete library
and self-hosted-compiler acceptance remain open.
