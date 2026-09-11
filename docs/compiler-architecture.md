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

## Effect declaration prerequisites and selected operation applications

Effect headers retain family and operation `where` clauses. A family publishes
the same predicate-domain product used by nominal declarations. Each operation
publishes an ordinary complete declaration signature, with family binders before
operation binders and inherited prerequisites included. Alias normalization,
kind-preserving instantiation, projection-domain checking and invocation checking
consume those products. The former payload/result-only operation substitution
and empty-scope effect signature validator are removed.

The shared trait solver retains effect declarations in its immutable snapshot.
Effect-family applications, including phantom arguments and unused outward rows,
use the same bounded domain-proof rule as nominal applications. Intrinsic callable
associated items have compiler-owned declaration identities even without source
trait headers; lexical equalities use ordinary associated-owner lookup. Predicate
conjunctions register their existing branded callable inputs before checking
environment prerequisites, independently of source order. Unresolved body-region
cells defer outlives checking until sealing; successful partial zonking is not
evidence that a region is already rigid.

Performances and monomorphic handler applications retain their operation's own
mixed-kind arguments in Typed Core. Generic transformation, sealing, canonicality,
scope validation and body fingerprints include those arguments. Independent Core
validation selects the declaration again, proves its prerequisites in the caller's
lexical environment, and checks payload/result compatibility using the shared
region and type relations. A payload-free operation cannot erase a phantom bound.
Operation arguments never become part of the nominal effect-family identity.

This repairs declaration and selected-application checking, not polymorphic
handler compilation or task-provider execution. Handler applications currently
require monomorphic evidence; unresolved binders do not introduce universal
assumptions. Executable lowering still transports the established payload and
resumption ABI, and the VM requires all senders/handlers for an exact family and
operation to agree. General operation specialization and retained task-registration
contracts remain open, as do native handlers. Parsing and validating the standard
task declarations does not establish a complete task provider or library.

## Lexical, kinded projection normalization

`TraitSolver` owns projection selection and recursive normalization for value
types, effect rows and structural constants. Its inputs are the immutable rule
snapshot and the current lexical trait, associated-equality, outlives and
quantified assumptions. A known structural head may contain rigid declaration
parameters: reducing `Wrapper<T>::Item` requires proving the selected
implementation's predicates in that exact environment. Ordinary functions and
implementation bodies use the same rule. A bare abstract subject or missing
generic evidence remains a symbolic obligation, never evidence or permission.

Implementation-head inference and associated-item substitution are distinct.
Unknown head arguments cannot select an implementation. A well-kinded GAT or
method argument can retain an inference cell in the substituted result because
it does not choose the implementation; it still cannot prove an item-domain
requirement. Kind checks and substitutions must preserve const cells as const
cells, rather than retaining a declaration binder or converting them to types.

The normalizer traverses every kinded carrier, including callable prerequisites,
parameters, results, effects and static-data element types. Nested callable and
quantified binders retain their actual region scopes. Type/row/const expansion
uses one active-key stack and the existing depth budget across kind boundaries;
cycles, ambiguity, refutation and exhausted limits are not successful symbolic
normal forms. Nested failures preserve their cause for source diagnostics.

Core supplies a partial substitution from its existing inference cells before
requesting normalization. This read-only substitution resolves solved type,
lifetime, const and row cells throughout the same structural terms without
defaulting unknowns. In particular, a generic argument learned from an earlier
call operand must be visible when reducing a later dependent parameter. Complete
zonking remains mandatory at persistence boundaries.

Signature comparison, signature/frozen projection validation, Core call/effect
checking and executable materialization consume this authority. The former
implementation-only permission flag, Core projection walkers and cycle guard,
signature-local selection walkers and materialization const-chain loop are
removed. Exact lexical identity retains its no-snapshot validation fast path;
structural and supertrait entailment use the solver. Failed normalization is
either reported or retained for an independently checked obligation, never
reinterpreted as an empty row or successful contract.

This is a repaired semantic boundary, not a complete compiler or library. The
full-library root still fails, and no GSC-2 bootstrap or native-handler readiness
follows from these normalization checks.

## Normal result snapshots and executed operation payloads

EscapeFlow joins normal values and their storage environments through one exit
snapshot representation, also used by exact local-label transfers. The bound
shared continuation product decides whether an evaluated expression can supply
a normal exit. A terminal arm still executes its argument, store and transfer
checks, but its placeholder value cannot contaminate a sibling's result shape.
Unknown continuation coverage retains a possible normal exit. Completion arms
do not execute after a definitely terminal strict subject.

PlaceFlow preserves a handler computation's normal result in the handler's
existing result-loan owner before capturing that edge's ownership snapshot.
Returning clauses use the same transfer mechanism. Merely retaining the
computation's storage state did not preserve its outgoing reference aliases.

Direct operation evaluation distinguishes an exited argument prefix from an
invoked operation, and retains an invoked terminal operation's payload separately
from its absent normal result. Handler payload binding consumes that evaluation
once; a non-returning operation no longer triggers a second evaluation fallback.
Terminal payloads retain the existing suspension/escape obligations, while an
operation whose argument exits never publishes an unexecuted payload.

This repairs those source resource boundaries, not complete guard-correlated
handler execution. General handler payload discovery, the remaining independent
minimum-handler completion logic, opaque nominal-result reference coverage and
native handlers remain open. No new continuation walker or runtime representation
was introduced, and normal-result exclusion does not erase outer-transfer debt.

## Partial invocation reference coverage

The interface-aware reference-path producer retains known caller dependencies
separately from unresolved coverage. `CallReferenceOrigin::Partial` travels in
the existing call/operation contract; its paths keep loans live but its result
shape remains potentially reference-bearing and incomplete. It is neither an
empty result nor external-reference permission. Declaration and realized call
types use the same producer; the duplicate realized-region matching algorithm
is removed. Refinement preserves every dependency frozen before region opening.

The shared layout traversal continues through unknown tuple/record components,
restoring each projection prefix. Enum alternatives merge only compatible known
paths: an unresolved prefix or conflicting region cannot certify a path beneath
that prefix, while an independent sibling remains usable. Logical residents,
raw-storage obligations, recursive-layout termination and unresolved array
extents retain their existing conservative treatment. Missing evidence is not
complete coverage.

Core validates partial shape, nonempty/nonrepeated paths, argument arity and
preservation of frozen dependencies; it does not independently reopen nominal
layouts without the interface. PlaceFlow uses those same known paths for result
aliases, projections, unique-output partitions and operation payload transfers.
EscapeFlow preserves their values and still rejects an incomplete concrete
reference result unless the existing bound invocation relation proves complete
returned-reference coverage. Generic coverage remains deferred, not certified.
Input collection cannot settle an unknown physical component merely by finding
another known leaf. The shared return proof can authenticate a known input
projection independently of its siblings, but still requires complete output
shape and checked reference evidence. The initial migration still failed to
authenticate a generic getter whose physical borrow was joined with unresolved
logical-region debt; the following boundary addresses that remaining distinction.
MIR transports the existing contract product and its fingerprint; runtime
provenance and wire-verifier representations are unchanged.

This repairs the generic erased-view result boundary exposed by sorting and
graph, not complete nominal/handler provenance or library execution. General
handler payload discovery, guarded storage, native label materialization and
the full-library acceptance gate remain open.

## Reference validity and retained invocation debt

The bound invocation product's `ReferenceCoverage` now publishes authenticated
normal-result paths as well as whole-result completeness. A path requires a
known invocation, at least one normal return and an authenticated input projection
on every returning alternative. An unrelated open result field does not erase
that path; unknown invocation coverage, a missing input or an unrepresented
alternative cannot certify it. The same shared layout and input-adapter rules
derive the paths and the complete-result decision. There is no second Core
provenance walk or independently populated result table.

EscapeFlow carries this reference validity in its existing value snapshot,
separately from the reference's conservative dependency union. The declaration's
possible input loans, logical residents and body-derived payload debts remain
present. Authentication does not turn an unresolved dependency into a valid
reference, remove it, or claim that the entire aggregate is known. It records
that this particular result leaf is a reference independently of those debts.
This repairs the generic getter described in the preceding checkpoint.

Projection and reborrowing transport that value evidence; replacing the handle
replaces its proof. A later unknown branch still prevents complete authentication.
Array elements keep their homogeneous/sparse provenance representation. Lifetime,
tail, external-store and control-escape queries inspect all retained dependencies,
and dereference still needs the existing backing-storage projection. Validity
does not create a referent identity or permission to ignore a live loan.

PlaceFlow consumes the same coverage product for opaque-result admission and
continues to retain the full loan union in its ordinary result aliases. Source
resource products, Core contracts and runtime/verifier provenance remain separate
boundaries. This is not complete guarded storage, generic operation-result
authentication, native label/handler lowering or self-hosted acceptance.

## Reference targets, retained loans and physical invocation stores

PlaceFlow's existing reference-origin snapshot now carries retained loans and
complete possible referent targets as separate relations. EscapeFlow transports
the same distinction in its existing reference value, independently of reference
authentication. Declared lifetime paths retain dependencies; they cannot claim
that an input carrier is the returned reference's actual destination. The bound
normal-return product can refine an authenticated leaf only when every return
alternative supplies represented targets. An unknown incoming target or absent
alternative prevents complete target coverage without erasing any observed loan.

Aliases, aggregates, captures, patterns, result snapshots and continuation joins
transport this product. Actual storage lookup, callable-owner projection and
reference assignment consume the target relation; liveness, scope escape and
carrier suspension consume the retained dependencies. Reborrowing a field
projects the possible referents, not the storage of every retained carrier.
Assignment snapshots its RHS before retiring old residents. Complete singleton
local destinations permit strong replacement; multiple/captured destinations
require weak joins. Unresolved local reference-containing accesses reject rather
than treating a lifetime dependency as an address or silently dropping a store.
Reference-free loads/writes use the existing owned-type proof for their absence
of stored-reference obligations, not a scalar-specific exception.

The shared invocation relation also publishes physical reference-handle may-stores
through unique input access, alongside its existing logical-resident stores.
PlaceFlow and EscapeFlow apply the same edges to their resident snapshots, retain
the possible new backing loans and invalidate exact local targets. Shared handle
copies retain backing storage without borrowing the old handle slot. Selected
declarations keep independent named and omitted regions rigid before deriving
store permission; actual captured inputs retain their established region
relations. The existing directional outlives entailment, including declaration
and parameter-implied bounds, is the authority for those edges.

Symbolic input references in callable-control values retain a distinct referent
identity. Their checked input projections can therefore supply a getter's
conditional return contract after an unknown mutation prefix without inventing
a physical caller address or certifying the preceding execution. Symbolic
storage payloads remain boxed to keep recursive evaluator values compact.
External reference targets denote only storage outside the current frame, never
an exact local address. Generic logical-parameter seeding augments rather than
erases that physical provenance.

Control MIR assignment and Ownership MIR replacement use the established value
representation compatibility relation already used for forwarding/call edges.
Source/Core still establish directional lifetime legality; mutability, pointee
shape, writable-place and ownership obligations remain independently checked.
No new source coercion, runtime reference ABI or wire representation is added.

This repairs the carrier/referent destination boundary and physical invocation
may-stores, not complete guard-correlated storage. Unknown local access, arbitrary
captured writes, operation-result coverage, native labels/handlers and full
compiler/library/self-hosted acceptance remain separate open obligations.

## Present references, absent variant payloads and evaluated initializers

The existing normal-return payload product distinguishes evaluated enum
constructors from ordinary aggregate products. Reference coverage classifies
each declared result path as authenticated wherever present, positively absent
on every returning alternative, or unresolved. A choice must cover every
alternative; an unknown value, missing ordinary tuple field or missing logical
argument cannot become an inactive variant payload. Whole-result coverage still
requires a known invocation and complete declared result shape. Positive
observations under incomplete execution coverage retain debt without proving
absence.

PlaceFlow's existing origin snapshot carries positive reference absence
independently of its loan union and target relation. An empty target query at
an external aggregate root does not establish absence in its fields. EscapeFlow
distinguishes a reference-free resident from both unknown provenance and generic
frame-independent storage. Aliases, constructors, aggregate projections, calls
and joins transport these facts through the existing products. Present or
unknown alternatives revoke complete absence. Replacing a nested resident
invalidates reference-free ancestor snapshots; the existing physical may-store
consumers also revoke absence while retaining possible incoming backing loans.
Absence cannot erase declared lifetime or control dependencies.

Evaluated top-level value initializers now participate in the same body-sealed
control batch as callable bodies, using their frozen pure zero-input declaration
contract and checked kinded substitution. Their source values do not acquire a
function type or callable authority. Existing constant invocation observations
and conditional declaration selection supply their return payloads. Ownership
and escape consume that bound result through the ordinary invocation pipeline,
and the interface-aware reference contract producer supplies static versus
unresolved result coverage. Neither consumer reconstructs the initializer body.
The old constant omission and duplicated escape call-result assembly are removed.

This repairs inactive enum payload and initializer-result provenance, including
the standard library's generic `None` value. It is not a complete invocation
mutation contract. A helper that constructs a static view and replaces an empty
variant still fails closed: the current source-to-destination may-store relation
does not supply a replacement variant's resident shape. The active regression
must be addressed through shared storage outcomes, not by treating an absent
source as new reference authority or dropping an unresolved write. General
guard-correlated stores, native labels/handlers and full compiler/library/
self-hosted acceptance remain open.

## Writable reference slots and proved read-only invocations

The shared resident-invocation relation distinguishes a writable physical
reference slot from the incoming loans it might receive. The declaration's
checked path and unique access authorize the slot; directional outlives rules
select possible input dependencies. A slot can receive a newly constructed
reference backed outside the current frame even when no incoming loan supplies
it. Logical residents and whole callable stores remain separate products: a
callable value is not a reference handle. Explicit, captured and higher-order
inputs share this producer and its projection rules. Missing projections and
opaque invoked environments retain their whole footprints and unresolved flags.

Both resource consumers snapshot physical write inputs before applying them.
They retain old and possible incoming loans, admit the coarse outside-frame
alternative, revoke reference absence and invalidate exact local targets. The
escape value snapshot supports declaration-authorized replacement of variant
payloads separately from strict source assignment. Opaque aggregates retain
projected updates with an untouched-field fallback, not a fabricated array or
closed field count. All loan, region, control and escape queries traverse that
same value. Source-proved arities and array extents permit precise subsequent
replacement; unknown fallback provenance cannot become absence or validity.

Only the existing sealed callable-control execution product can prove an
invocation storage-read-only. It requires complete coverage, classifies every
event, and includes possible implicit cleanup. The destruction authority supplies
positive trivial-cleanup evidence using its existing custom-Drop selection and
owned layout rules. Open or unavailable layouts, executable cleanup and unknown
control prevent the proof. An independently checked declaration contract may
prove a getter read-only after an unknown caller prefix without certifying that
prefix. Both store consumers use this proof; empty loan sets never imply no write.

This repairs the helper-created static-view replacement left open above,
including generic regions and generated native execution. It is not a complete
captured mutation contract: the active captured-target source exposes a mismatch
between captured-input loan identities and isolated closure resource products,
alongside conservative captured-region store permission. That regression remains
an acceptance requirement, not a waived diagnostic. Complete guarded storage,
native labels/handlers and compiler/library/self-hosted acceptance remain open.

## Checked borrow access and instantiated capture provenance

PlaceFlow publishes checked access for each explicit Core borrow and each
branded borrowed-refinement binding through its existing loan checks. A record
names the exact subject, any additional refinement fields and the existing
evaluated rvalue owner. Rejected loans publish no permission. EscapeFlow consumes
that per-callable product before constructing the borrowed value; it no longer
compares instantiated captured roots with the diagnostic spellings of formal
input loans. The former global borrow-event name set and suffix matching are
removed. Captured values retain their actual storage identities and debts.

Resource products bind the complete semantic Typed Core input, independently of
the local continuation product's narrower control-shape dependency projection.
Lifted products share the enclosing arena seal rather than re-hashing it for
each closure. Escape, quantity and ownership/lowering entry points validate
that seal. A changed local name or layout cannot reuse an earlier borrow proof.
Escape analysis requires an admitted loan product: it retains the original
ownership failures and publishes no control-lifetime result for rejected input,
rather than treating a failed borrow as an executed unknown call operand.

Explicit, refinement and invocation reborrows share the same escape-value target
projection. It projects actual referents without projecting or deleting retained
loan dependencies; logical region links remain available for later stores.
Borrowed refinement fields no longer receive an unprojected whole-subject value.
Rvalue borrows evaluate their recorded owner once and retain its local escape
obligation. Missing access evidence is not caller-owned or temporary authority.

This repairs the formal/actual captured-loan mismatch, including moved, borrowed
and nested capture execution. The generic captured-target replacement regression
still fails on conservative storage-region matching (G5008): its loan-access
failure is gone, but complete captured mutation permission is not established.
Distinct body-region constraints and guarded storage outcomes still require
authoritative producer/consumer integration. No runtime reference representation
or source lifetime guarantee changes, and full compiler/library/self-hosted
acceptance remains open.

## Closed body regions and directional invocation constraints

Body inference publishes `BodyRegionConstraints`: distinct closed existential
regions, rigid local-storage upper bounds, and directed outlives obligations.
The bounded constraint solver checks every induced rigid-boundary requirement
against the lexical environment. It identifies only regions proved equivalent;
unrelated elision holes do not become equal or static. Frozen Core independently
checks that product before using its facts. Callable contracts retain the
connected constraints of their free residents and result terms. Inference holes
and universal placeholders still cannot cross a persistence boundary.

Calls, trait receivers, operation inputs, constructor fields and assignment use
the shared directional region alignment before ordinary type unification.
Environment scopes join the same type-outlives constraints before sealing.
Assignment transports callable refinements without replacing the destination's
reference regions or declared callable ABI. The trait solver derives nominal
variance by a bounded monotone fixed point over normalized representation fields;
unresolved projections and compiler brands remain invariant. Protocol identities
and mutable referents retain their invariant obligations.

Resident invocation stores and both resource consumers use these closed region
relations without equating captured and explicit inputs. Returned constructor
payloads retain the sealed instantiated capture type separately from the longer
incoming value's provenance. Generic lifetime substitution keeps free caller
regions rigid. Frozen invocation validation rechecks selected declaration and
resident prerequisites, including phantom bounds. The existing implementation
substitution producer accepts the caller's scoped solver when quantified Fn
evidence determines Output/Effects binders absent from a generic receiver head;
closed materialization uses the same producer without lexical assumptions.
Associated Output inference uses the existing structural implementation matcher,
so a represented `Option<U>` equality can determine U without allowing U to
capture a predicate-local quantified region.

Fingerprints, instance identities and callable metadata transport closed region
identities. Fusion freshens template-local regions before inserting caller
arguments and carries their constraints into the receiving Core. Callable
serialization retains the product; decoded metadata rejects malformed constraints.
Source typing now admits the whole body batch before inter-body control/resource
analysis, so rejected region inference cannot publish missing provenance as an
invocation fact. The runtime reference representation is unchanged.

This repairs the previously active generic captured-target replacement, including
generated native execution, and preserves incoming captured-loan rejection. It
does not supply complete guarded storage outcomes, native owned handlers, full
library composition or self-hosting. Those acceptance requirements remain open.
The new nested-output generic capture execution fixture still reaches missing
checked borrow access at its caller argument; structural output selection is
repaired, but that source/resource boundary remains an active regression.

## Strict computed field subjects

PlaceFlow's existing subject-evaluation rule now covers every computed field
base, not only dereferenced handles. A static local projection is still a place;
a call, constructor or other computed base must first evaluate its strict inputs
and publish their ordinary loan/control facts. Nonlocal completion stops before
field access. Nested fields reuse that rule without evaluating their base twice.
Escape and lowering consume the resulting existing products; no missing access
record becomes permission and no second argument-provenance walk is introduced.

This repairs the nested-output capture fixture left open above. Targeted tests
also prove conflicting argument-loan rejection, exactly-once VM/native side
effects, and nonlocal helper exits through a projected result. It does not
complete guarded storage outcomes, library composition or native handlers.

## Literal type evidence

Core literal elaboration supplies intrinsic element and extent evidence before
ordinary type/const inference freezes it. An array literal retains its exact
length even in an unresolved or absent expected context; only an explicit
bootstrap `Array<T>` context selects the legacy carrier. Later generic calls,
patterns, materialization and runtime layout consume the existing fixed-array
type rather than recovering a length from expression syntax.

A contextual octet literal first resolves the selected standard Slice identity,
then unifies its element with `u8` through the existing inference context. It
still constructs sealed static data and invokes the manifest-bound wrapper as
an ordinary Core call. A rigid or incompatible element cannot acquire byte-view
authority. Partial resolution exposes solved components without defaulting
unrelated holes; full zonking and the existing layout/provenance validators
remain required at persistence and execution boundaries.

This repairs these contextual literal producers, not all bootstrap literal
extensions, library ownership contracts or full compiler/self-hosted acceptance.

## Terminated statements and borrowed generated captures

The body parser preserves a trailing statement terminator as an explicit unit
tail in the ordinary strict block sequence, before destructuring continuations
are formed. Core contextualizes that unit result, not the discarded expression.
Existing resource rules retain the discarded value's ownership obligation and
cleanup; shared continuation facts still prevent an unreachable unit suffix
from turning a transfer into normal completion. No downstream pass reconstructs
semicolon syntax or gains independent disposal authority.

Generated callable construction consumes the verified capture formation mode.
Copy and move establish owned homes; borrowed captures retain the original slot
and its actual writable initialization flags. Capturing an already lent input
reuses its exact registered home. A local frame capture uses a non-owning home
view guarded by that frame's live lease. Nested invocation lends and restores
this same initialization product, not a separately populated shadow mask.

Native storage distinguishes owned, external-argument and borrowed-frame
retirement authority. Releasing a borrowed view neither clears the source flags
nor revokes resident handles still owned by that frame. Reference-byte metadata
retains such a view strongly, but never retains its backing frame: returned
references may outlive the closure while the frame is live, and every checked
payload access fails after frame expiry. References to owning homes retain the
existing weak-owner contract. Resident copies check source lifetime and mask
before touching source bytes. Native ABI generation 13 records this changed
capture-storage contract; portable bytecode and reference representation do not
change.

This repairs statement-result loss and generated borrowed-capture copying,
including nested and mixed invocation. It does not discharge the full library's
remaining quantity and mandatory-tail obligations, complete guarded storage,
native handlers or self-hosted acceptance.

## Logical dependency absence, projections and cyclic joins

EscapeFlow's existing value snapshot distinguishes a constructed value's empty
additional logical debt from unknown physical provenance. Evaluated fields still
retain their own loans. Opaque incoming carriers use the existing projected-value
fallback when logical regions are installed beneath fields, preserving untouched
caller-owned contents instead of manufacturing a sparse unknown alternative.

Region resolution consumes the existing graph's edges and per-node contents.
A dependency backedge contributes no new union member; it is not an unknown
runtime value. A cycle needs grounded evidence, and a missing node remains
unknown even when another connected node is known. Later local loans, control
brands and unresolved replacements remain in the same snapshot queried by
return, store, suspension and mandatory-tail checks. No second Core traversal
or independently populated provenance graph is introduced.

For a checked expression in the current body's rigid generic namespace, the
type parameter was fixed outside that activation. Its result snapshot may
therefore retain frame independence without claiming reference absence, validity
or an exact referent. Inference cells and explicit reference types do not receive
that proof. An unknown payload from a different callable's abstract namespace
still requires its existing input projection or independent closed-type proof.

This repairs the library's source-level tail-provenance failures, not all tail
execution. The generic callback regression now reaches the executable verifier's
missing preservation proof after indirect invocation. The branch-joined vector
regression reaches unresolved nested getter storage. Their original execution
assertions remain acceptance obligations; source admission does not waive either
receiving boundary or the library's remaining minimum-use requirements.

## Nested reference-result residents

The interface-aware callable reference contract traverses returned referents as
well as outer handles. Explicit dereference components distinguish a stored
reference's own lifetime from the shorter borrow used to load it. Generic
referents leave a partial contract for ordinary call instantiation to refine;
recursive or growing referent layouts retain finite observed paths without
claiming complete coverage. Input and output discovery share the same layout
traversal and keep their distinct completeness obligations.

PlaceFlow stores these nested result paths in its existing origin snapshots and
transports them with aliases. EscapeFlow's reference value retains declared
resident contents separately from both the handle's loan union and its possible
physical targets. The containing value retains the inner debts before loading,
while a copied stored reference need not retain its former container's shorter
borrow. Logical region links remain in the existing storage graph. No lifetime
relation becomes a physical address or permission for a strong update.

Dereference reads exact live local storage when that identity is known, so a
replacement cannot be hidden by an older declared snapshot. An outside-frame
storage class cannot erase separately retained inner local debt. Unknown joins
remain unknown, and writes without a complete destination still reject. Both
resource consumers use the frozen callable contract rather than reconstructing
the getter body or recognizing a library owner by name.

This repairs nested heap-getter reads and the Box getter/ownership regression,
including generated native execution. It does not establish arbitrary logical
write destinations, complete guarded storage or executable tail preservation
after mutation. The branch-joined vector regression now reaches the independent
runtime tail verifier; full library minimum-use and self-hosting gates remain
open.

## Per-input executable frame-preservation requirements

The executable tail verifier publishes a checked conjunction for each preserving
helper. Inputs require an independent transitive address graph unless that exact
typed reference parameter has been proved to require only independent referent
contents. Borrowing a local container and inserting an incoming reference can
therefore have different requirements within one call. Raw pointers do not gain
the weaker typed-reference proof.

The existing bytecode control verifier establishes these contracts under explicit
input hypotheses. A candidate weakening is checked together with every previously
accepted weakening; individually successful probes are not combined without
checking their conjunction. A stronger memory-preservation proof also suffices.
Recursive graph propagation starts with weak hypotheses and only strengthens
contracts, rechecking callers when a requirement changes. No source annotation,
helper name or separate instruction walker supplies the proof.

Ordinary and tail calls discharge the same per-input contract before retaining
frame facts. The previous all-whole-input and all-reference-content summary sets
are replaced by this product. Destruction and invocation preservation remain
separate requirements; unknown callbacks still revoke the relevant facts. Existing
local replacement, raw mutation and saved-continuation invalidation rules remain
in force. Decoding recomputes the summaries from the executable graph.

This repairs the branch-joined vector tail regression through fresh/decoded VM
and generated native execution. It does not prove the behavior of an abstract
callable parameter or repair an incompatible tail ABI. Verifier generation 39
records the changed proof contract; runtime storage and portable instruction
encoding are unchanged.

## Shared ordinary and tail invocation ABIs

Runtime MIR direct and mandatory-tail calls use one representation-compatibility
rule for parameters and normal results. Source/Core retain semantic contract
authority; different erased environment refinements do not change a callable's
resident ABI. The earlier tail-only exact type equality is removed.

The receiving executable verifier independently applies the same call relation
to ordinary result slots and inherited tail continuations. One target-local
generic substitution must satisfy every parameter and the normal destination.
Callable receiver permissions follow variance: arguments and nested callable
inputs have opposite directions, results preserve supplied capabilities, and
mutable referents remain invariant. Safety, effects, arity and operation
specialization retain their existing checks. Numeric generic indices belonging
to different activations do not become the same binder.

A terminal target supplies no normal payload; a returning target cannot inherit
a continuation declared terminal. Mandatory transfer still requires its exact
frame-independence, handler, capture and execution-safety proofs. Signature
compatibility does not discharge these control and storage obligations. Decoding
reconstructs this ABI proof, and no source annotation supplies executable
callable permission. Native packet and resident representations are unchanged.

Native reference authentication retains the same backing origin and logical
projection while constructing the requested shared view. View formation, byte
admission and re-encoding use the existing scoped receiver relation, not generic
inference or a new storage layout. VM borrowing of native-backed residents
consumes the same rule and retains the requested view through reborrowing.
Mutable referents stay invariant, and a weakened re-encoded view cannot recover
the origin's stronger permissions.
Generated reborrowing delegates origin/type/initialization checks to that shared
producer; its redundant exact-layout check is removed. Frame expiry, pointer
identity, initialization and partial-byte-write revocation remain independent.

This repairs the stateless-callable tail ABI regression, not preservation after
an abstract callback invocation or full tail fusion. Verifier generation 40 and
cache generation 131 record the corrected boundary. Full library minimum-use,
guarded resource contracts, native handlers and self-hosting remain open.

## Executable entry behavior and storage-exposure history

The existing executable control verifier observes destruction and invocation
behavior at direct call edges before argument consumption or invalidation. The
program proof closes those incoming must constraints to a greatest fixed point
and uses them when checking actual direct-only function bodies. All callers must
agree; recursive propagation cannot retain a property refuted by another caller.
Program entry, first-class callable targets and executable destructor entry paths
begin unknown, including captured inputs. Missing indirect-entry evidence never
becomes a direct-call guarantee.

These entry constraints are distinct from universal helper summaries checked
under explicit parameter hypotheses. Actual callers cannot establish universal
result or memory behavior under arbitrary arguments. Decoding reconstructs both
products from executable semantics; source annotations and stored assertions do
not certify either proof. Invocation and destruction remain independent facts.

Address exposure is a persistent may fact in that same control state, not a
whole-body prediction. Executed borrows and borrowed captures expose their source
storage; reborrowing an existing handle does not expose the handle's own slot.
Joins union exposure, and moves or storage death never erase escaped-address
history. Label and saved-continuation capabilities conservatively expose the
whole activation; snapshots and restorations retain this state. An immediately
dominating whole-slot initialization probe can prove an uninitialized,
not-yet-exposed local empty. A future borrow cannot force its initial cleanup
branch, but any already exposed predecessor keeps the branch conservative.

This replaces the old whole-function exposure scan and repairs the original
generic callback tail regression through fresh/decoded VM and generated native
O0/O2. It does not establish general indirect-entry/result provenance, complete
guarded resource contracts, native handlers, full library acceptance or
self-hosting. Cache generation 132 and verifier generation 41 record this proof
boundary; runtime and serialized instruction representations are unchanged.

## Absent performances versus may-effect permissions

The shared callable-control coverage producer derives absence of algebraic
performance from complete execution alternatives and their ordered events. A
returning outcome alone is insufficient: earlier performance, cancellation,
terminal operations, unknown paths and empty coverage cannot establish absence.
The existing invocation-frame projection excludes strict caller operands from
this callee-only fact. Storage-read-only and performance-absence checks share
that projection but retain separate obligations: source cleanup cannot perform
outward effects even when its storage writes are unknown.

PlaceFlow's minimum-use suspension consumer now uses this checked invocation
fact before falling back to the conservative declared effect row. A may row
cannot invent a cancellation edge when complete execution excludes performance.
Label transfers and their owner dispositions remain independently checked;
unknown callbacks still require cancellation-safe retained state.

The same control evaluator interprets a handler's protected computation. When
every alternative proves no performance, no operation clause can run or replay
that computation, so normal and label results retain ordinary alias/provenance
facts. A performing or unsupported alternative keeps the whole handler unknown
and marks its invocation coverage incomplete. This does not model resumption or
cancellation generally, nor fabricate clause execution from the permitted row.

Cache generation 133 records this source-analysis correction. It repairs direct,
transitive, aliased and generic unused-effect regressions without adding a new
Core walker or granting zero use to retained linear owners. General guarded
generic cancellation/resource contracts remain incomplete: the full library
still reports its 11 G5024 obligations, and self-hosted acceptance remains open.

## Conditional residual ownership at closed specialization

PlaceFlow's existing owner disposition rule publishes an open call-row
obligation using owner-relative transferred paths and selected constructor
openings. Each residual state is retained; a move on another alternative cannot
discharge it. Enclosing handler operations preserve ordering and continuation
quantities so substitution cannot choose an outer handler over a matching inner
one. Ordinary affine residents also retain copying obligations for replay.
Known callable invocation and borrowed-storage analysis keep their own lanes.

The generic ownership product transports these requirements without asserting
that an unknown operation is harmless or that an owner is discardable. Concrete
specialization closes the rows and resident types with the normal substitution
and trait solver, then uses the same disposition/layout rule as source checking.
Optional or terminal abandonment requires zero use; repeated resumption requires
copying. Missing declarations and unresolved rows reject. A closed empty row or
exact-once continuation can preserve a pending positive-use resident.

Every demanded function-value or direct-call instance crosses this boundary;
lifted bodies use the enclosing instance's actual substitutions. The specialized
constructor discharges the requirements and retains a private proof bound to
the source product, definition and exact instance. Independent structural
validation rejects mismatched proof reuse. Check and Build consume the same
specialization gate. No consumer reconstructs owner transitions from another
Core walk, and neither source annotations nor a cache generation certify use.

Cache 134 records this request-local conditional contract. It is not the full
serialized guarded-interface format or complete callback/loan replay analysis.
The library root now retains two quantified observer-row failures; their exact
call-lifetime relation must survive selection before effect accounting can
consume it. Full library and self-hosted acceptance remain unproved.

## Selected callable declarations and instantiated invocation effects

Elaboration publishes each call's selected declaration before argument-region
alignment and its resulting invocation effect row in `CoreCallContract`.
The declaration is an unrefined callable view: actual receiver permissions,
capture identities and prerequisites remain on the callee value. Parameter and
effect regions keep their original relation instead of reconstructing a lexical
Fn predicate from shortened actual argument views. Missing associated Effects
equality remains a symbolic projection, never an implicit empty row.

Independent Core validation proves selection from the actual callee's concrete
callable relation or scoped ordinary/quantified trait evidence. Compiler-owned
Label evidence supplies its own pure transfer contract, not a default Fn effect
definition. The shared directional lifetime alignment then checks every argument
with one substitution and verifies the instantiated declaration row. Unproved
relations and altered rows reject. Invocation metadata participates in normal
inference sealing, canonicality, binder scope and body fingerprints. Structural
fusion maps it through the same invocation frame as other semantic types.

Minimum-use suspension consumes the instantiated row. Handler payload transfer
uses the pre-alignment parameter/effect relation, and unsafe validation and
terminal lowering consume the selected safety/result view. The separate lexical
effect recovery and its PlaceFlow binding transport are removed. Existing
callee-value prerequisite and receiver checks retain their independent authority;
the declaration view cannot certify a forged capture environment.

Contextual row checking applies the ordinary complete subset constraint before
requiring solved allowed-row metadata. Empty requirements can fit an unresolved
context without granting permission for a missing named effect or rigid tail.
Library callback declarations propagate their actual selected effect rows through
ordinary generic signatures. This repairs the quantified observer accounting and
full-library root composition, not complete guarded interfaces, general compact
effect inference, unannotated universal closure generalization or every library
execution graph. Cache 135 records the changed source boundary; runtime and
serialized instruction representations are unchanged.

## Body-defined contextual effect rows

The ordinary call and operation checker emits the requirements of an inferred
compact callable. Every requirement retains its expression's exact complete
handler coverage. Nested callable formation starts a separate scope, and
explicit typed closures keep their written declaration rather than acquiring
the enclosing row. This extends elaboration's effect producer, not a second
source/Core effect walk. Deferred subtraction participates in ordinary pending
inference and must close before Typed Core is published.

A body-owned row variable is separate from its contextual expectation and from
rows of unknown callback inputs. The definition is the least union of its
requirements: its own recursive resumption contribution adds no new member.
Independent unknown inputs remain unknown, and recursion beneath mixed-kind
arguments still fails the ordinary occurs check. Only after defining the body
row does inference equate it with the selected contextual contract. Permission
to perform a wider row cannot populate the callable's exact recorded row.

Whole-row holes can bind symbolic associated projections. The shared normalizer
selects a known callable's compiler-owned Fn/RunsIn relation without demanding
that its Output/Effects be concrete first. The existing selector still checks
receiver access, safety and residual predicates; ordinary implementation-head
selection is unchanged. Source permission checking uses the same subset rule
again after normalization. An owned F:Fn bound also remains owned evidence:
capture formation uses its existing copy-or-move rule, not an invented &F bound.

Cache 136 records this inference and formation correction. Generic symbolic
row subtraction, higher-ranked input generalization, complete guarded interfaces,
native handlers and full compiler/library/self-hosted acceptance remain open.

## Constrained pattern subjects and dependent numeric defaults

The shared structural pattern elaborator consumes the body's exact lexical
projection solver and emits ordinary type equalities when a named nominal,
tuple or fixed-array pattern supplies the required shape of an open subject.
Its constrained decision retains that type at the point of inspection. Core
conversion consumes the decision instead of requiring the original projection
to have a concrete head already. Completion coverage uses the same constrained
subject; the equality must still close before the body can be published.
Neither a pattern name nor an associated result selects an implementation head.
`is`, completion/let patterns and operation payloads share this entry point.
The final ordinary call-argument equality now uses the same deferred rule after
the selected call's existing lifetime alignment.

Numeric defaulting consumes dependencies from those existing pending type
equalities. Open application inputs are distinct from inferred result roots:
default an independent numeric input, propagate normalization/equality, then
consider the dependent result's default. Type, const, row and region uncertainty
remain represented, and a different projection's own application is not a
result variable. Real cyclic result dependencies remain unresolved. This reuses
the type algebra's variable collector, not source order or another Core walk.
Body-region closure supplies another propagation boundary; no unknown result
is generalized merely because its numeric default is waiting.

Pattern sealing and independent Core validation share literal type/width
admission with initial elaboration. A width learned after projection selection
must still fit every literal. Core also checks each completion, `is` and
operation pattern against its actual structural subject. Existing custom-Drop
and ownership checks remain in force after the type is known. These constraints
do not grant field disposal or erase a destructor.

Cache 137 records this source boundary; executable formats and runtime ABIs are
unchanged. Float-conversion execution now passes, while the iterator source
progresses to remaining ownership/provenance obligations. This is not complete
pattern, library, guarded-interface, native-handler or self-hosted acceptance.

## Resumable generated segments and shared resident control frames

The verified executable graph now supplies the same activation, handler,
continuation, resumption-return and cleanup state to VM and LLVM execution.
`vm_backend/execution.rs` defines the frame-transition boundary consumed by
both native emission and machine-entry validation. A generated function runs
LLVM computation until that boundary and returns its next verified location.
The common program runtime performs the original transition. Ordinary calls,
deep resumption and mandatory tails do not retain recursive generated C frames.
Local scalar, aggregate, branch, pattern and memory operations remain generated
instructions; unsupported native instructions still reject during graph admission.

There is no synthesized HostCall body or second adapted executable graph.
The old generated mixed-import bridge, synchronous callable dispatcher and
tail-packet bridge are removed. Source/code identities, layouts and the exact
engine partition remain sealed into the native module witness. Explicitly
VM-selected bodies share that graph and control state, not an independently
trusted replacement. Public foreign imports retain their separate authority
and callback ABI; selecting a VM body grants no external-call authority.

Native frame planning extends the ordinary runtime storage plan with each
non-scalar resident's checked native layout. Both engines establish its home
before an engine crossing. Machine entry lends those homes' actual logical
initialization masks and returns every loan before resuming runtime control.
Private scalar spill bytes are reconstructed from scalar value snapshots.
Temporary resident homes detach before either engine mutates a saved snapshot,
including an empty provisional slot. Disarming an argument releases its carrier,
not another continuation's allocation. Source-storage brands and lent captures
retain identity; synchronization transports their home as well as their value.
An actual storage death still expires the allocation and cannot be undone by
restoring a snapshot. New lexical activation cannot reuse an older provisional
home as its storage owner.

Both engines use the same checked borrow producer and persistent address-exposure
fact. A borrow of a temporary prevents later carrier relocation from replacing
its backing storage. Native reference bytes retain the existing weak home origin;
they neither own the referent nor recreate an expired home. The former separately
borrowed generated-stack home/reference representation is removed. Generated
initialization loans remain the live view of actual resident homes, not a shadow
reference authority.

Label and resumption residents use the existing byte-transport lease domain.
A compiler control identity and fresh token authenticate the retained typed
value; arbitrary bytes, another domain, a changed type or a partial overwrite
cannot reconstruct it. Invocation separately checks the live destination or
handler. A transported token is not proof that its dynamic control owner remains
active. Callable environments keep their existing source Copy and destruction
rules; carrier release alone is not source cleanup.

Structural fusion compares physical invocation operands with their own checked,
instantiated value contracts. Comparing them with the template's pre-substitution
regions had incorrectly demanded code expansion for an ordinary borrowed
resumption call. The existing invocation representation is the authority; no
new callable-target guessing is introduced.

Cache 138 and native ABI 14 record this integrated runtime boundary; portable
bytecode and verifier generations are unchanged. Tested native/mixed paths now
include owned installation, returning/deep resumptions, completion transforms,
partial forwarding, exact replay, cancellation and captured borrowed payloads.
This is not yet full native-handler acceptance. General borrowed/cross-frame
resumption proof transport, mandatory-tail handler activation fusion, complete
zero-marshalling/performance accounting and foreign-control admission remain
separate obligations. Full source/library and self-hosted acceptance also remain
open. The earlier generated-stack descriptions document superseded checkpoints,
not a second active representation alongside these shared resident frames.

## Caller-owned resumption inputs through checked helpers

The existing executable control verifier now runs under symbolic capability
inputs as well as concrete local handler tokens. Structural input paths retain
their caller namespace through aliases, products and ordinary result relations;
they are not local handler brands. A helper may return the caller's capability
to its still-live owner, but cannot return a locally captured or unknown token.
Opaque foreign/effect transfers remain unproved, and borrowed storage does not
acquire an owned callable input path merely from its type.

The whole-program transfer product publishes finite helper contracts for input
invocation and result transport. May-invocation history and guaranteed invocation
on every normal path are separate facts in the same control state. Direct calls
instantiate those contracts with their actual capabilities. Both direct resumption
instructions and helper invocation audit suspended suffixes with the same control
transition; only guaranteed invocation discharges a one-shot continuation. The
producer rechecks published contracts after frame-preservation hypotheses settle.
Decoded graphs reconstruct this evidence rather than trusting source annotations.

UseFlow's existing checked-body quantity execution now covers capability-consuming
helpers as well as factory results, with the original caller capability keys.
The former factory-only entry condition is removed. Runtime MIR-to-VM return
inference runs on the complete executable batch because a helper's resumption can
make the caller's completion reachable. No source inlining or new runtime bridge
substitutes for ordinary helper activation.

Cache 139 and verifier 42 record this proof boundary; native ABI 14 and portable
bytecode 72 are unchanged. This initial contract admits at most one invocation of
one input capability, with no helper-local active delimiter around it. Ordered
multiple invocations, borrowed capability storage and arbitrary recursive helper
proofs remain open. Missing evidence rejects; an unordered may-call set cannot
certify replay counts or delimiter order.

## Branded resumption places and directional quantity views

Evaluation MIR retains a resumption place's lexical identity and complete
contract. Its receiving validator checks them against the active binder before
Control MIR resolves the actual token slot. PlaceFlow's existing projection and
loan liveness rules classify that binder as storage; escape consumes the same
checked borrow product. Borrowing no longer invents a temporary source owner
which later aliases the binder's slot and collides with its lifetime identity.

The executable resident domain retains possible control contents in a borrowed
view without granting owned invocation authority. Shared exposure preserves the
source's exact token; writable exposure revokes it. Existing reference-origin
mutation and handler-expiry rules remain required. Noninvoking checked helpers
can receive the shared handle, but borrowed invocation and arbitrary writable
control transport are not established by this proof.

Elaboration keeps directional invocation comparison views separate from actual
argument and transfer value contracts. Contextual rewriting of a reusable named
function does not apply to a lexical resumption. A helper's one-shot parameter
must not rewrite an optional binder's `[0,1]` value into `[1,1]`.

Cache 140 and verifier 43 record these boundaries; bytecode 72 and native ABI 14
are unchanged. The shared-borrow helper regression passes fresh/decoded VM and
native/mixed O0/O2, with forged place identity/type and writable-exposure rejection.
Optional helper cancellation now passes Core but remains an active executable
policy failure. Repeated ordinary helper calls still expose premature replay
owner consumption. Both regressions remain preserved; ordered replay, dynamic
cancellation, mandatory-tail handler fusion and full zero-marshalling acceptance
are not complete.

## Optional cancellation and protected continuation ownership

One checked quantity-to-policy projection supplies both executable MIR paths.
Optional `[0,1]`, exact one-shot `[1,1]`, and exact finite replay no longer share
a cancellation policy. Both VM engines reject an explicit normal cancellation
of an exact one-shot frame. The portable policy encoding preserves the distinction.

The existing helper contract records possible cancellation separately from
possible invocation and guaranteed invocation. Guaranteed disposition means
invocation or cancellation on every normal path; it cannot discharge an exact
invocation requirement. Callable destruction of a symbolic input participates
in that same verifier state. Cleanup after a guaranteed invocation does not
claim another cancellation. Final contract revalidation and decoded proof
reconstruction remain mandatory, and the single-input/single-invocation bound
still applies.

Proven handler expiry retains a distinct expired control value in the resident
domain. It cannot be invoked, escaped or joined back into live authority, but
releasing its inert bytes is not cancellation of an unknown branch. Opaque
mutation still loses that proof. The shared runtime may release a handle after
its dynamic owner has ended without searching for or recreating that owner.

Explicit invocation arguments establish owned parameter slots; capture inputs
lend existing storage. The executable exposure product retains that distinction
at entry. An immediately preceding whole-slot initialization probe can settle
either outcome for an unexposed slot using its existing definite state. An
exposed or partially projected slot does not gain the proof. This allows actual
conditional argument cleanup to establish disposition without inventing a path
where a fresh incoming owner was already absent.

Callable disposal dispatches an uninvoked optional token to the common runtime
abandonment transition, including from an ordinary helper. It retains the
delimiter marker needed by completion while destroying the suspended branch.
A spent token does not cancel again. The former replay-only ownership list is
now the common `continuation_owned` partition consumed by replay and cancellation.
Its original Cleanup MIR producer selects definitions on the protected graph,
not every lexical descendant: a sibling clause's newly initialized storage is
not part of the suspended computation. Retained nonowned slots include initially
empty slots, with the same source-allocation brands guarding later synchronization.
Existing frame cleanup executes inner frames before their owners and preserves
outer borrowed storage.

Cache 141, verifier 44, bytecode 73/schema 117 and native ABI 15 record this
integrated contract. Focused execution covers both helper branches, same-frame
and deeper-frame owned cancellation, legacy cancellation and direct replay.
Full replay transport and ordered multi-invocation helper proofs remain open.
Arbitrary resumption-bearing destruction during abandonment, complete borrowed
invocation, mandatory-tail handler fusion and zero-marshalling/performance
acceptance also require further integration; these tests do not certify them.

## Quantity-derived replay-handle transport

UseFlow publishes replay-handle transport from its existing checked value and
invocation execution. Every represented alternative at an occurrence must be
a finite replay resumption; callable type compatibility is insufficient. The
product binds the complete source body. Helper execution under one caller's
inputs cannot publish universal permission for that helper's code. Staged source
and receiving resource products retain this result rather than discarding it
after diagnostics, and Ownership MIR consumes its occurrence projection.

`RetainResumption` is an explicit ownership and executable operation, distinct
from source Copy, moving an owner, or copying a suspended computation. It retains
a carrier of the same dynamic delimiter and remaining invocation budget. Both
runtime emitters preserve this operation through ordinary arguments, aliases,
structural projections and result transfers. The independent executable verifier
requires a matching exact live replay token; unknown, expired, merely callable,
and one-shot values cannot acquire this authority. The shared native/VM control
runtime transports the authenticated small handle without copying its branch.
Ordinary copying constructors and projections enforce the same prohibition on
duplicating owned resumption contents. Shared reference copying retains its
separate handle permission and does not copy the referenced continuation.

Resident control joins use the existing initialization facts. A positively empty
uninitialized slot contributes no present nonresumption alternative, while a
present ordinary value still destroys exact token agreement. Possible control
taint survives even when readability is absent. Cleanup of a replay carrier
does not cancel its delimiter-owned budget. Normal cancellation with remaining
required uses fails at the runtime's existing hostile-bytecode accounting gate.

Cache 142, verifier 45, bytecode 74/schema 118 and native ABI 16 record this
boundary. Ordered multiple invocations within one helper remain an unsupported
proof obligation, not an unordered invocation-count shortcut. Final replay must
still be migrated to consume the original snapshot instead of copying every
invocation. Borrowed invocation, mandatory-tail handler fusion and complete
zero-marshalling/performance acceptance remain open.

## Original continuation consumption on final replay

The shared runtime delimiter state now distinguishes protected execution, a
pending original continuation, and a spent replay clause. Issuing an early
snapshot decrements the budget retained with that original. The final exact
invocation takes the original storage and capture-loan identities without
allocating a replay copy. Both execution engines and non-returning snapshot
transfers consume this same transition; a non-returning transfer cannot abandon
remaining required invocations.

A spent clause is not an active effect delimiter. It cannot capture or retain
new resumption authority, forward a nonexistent original, or replay again.
Closing it destroys no extra snapshot. Abandonment and nested replay copying
preserve this distinction, rather than treating absence of a continuation as
permission to reactivate a delimiter. Earlier snapshots still use the existing
ownership partition, initialization masks and shared rebasing map.

Cache 143 and native ABI 17 record the runtime change; verifier 45 and bytecode
74/schema 118 are unchanged. Ordered multi-invocation helper proofs, general
borrowed invocation, foreign-control admission, mandatory-tail handler fusion
and complete zero-marshalling/performance acceptance remain open.

## Ordered executable helper capability histories

The executable control verifier carries finite ordered invocation/disposal
histories in its existing state. CFG joins union complete path alternatives;
events within a path do not commute. Normal-return histories and reachable
event prefixes are separate parts of the published helper contract. Prefixes
cover non-returning executions without discharging a caller's normal-return
obligation. Empty coverage is distinct from one known empty execution.

Ordinary calls instantiate explicit and structural input paths against the
actual capabilities. Each alternative runs its events through the existing
resumption and disposal transitions in order, then only normal alternatives
rejoin the caller's control state. Multiple helper inputs may name one dynamic
delimiter. Disposal after invocation releases a spent handle; it is not another
invocation or permission to cancel an uninvoked exact one-shot continuation.
Return transport retains the existing structural resident relation.

The previous unordered invocation map, may-invocation set and guaranteed-use
sets are removed, together with the single-input/single-invocation admission
restriction. Final whole-program revalidation still checks the complete contract.
Growing traces, recursive capability loops and exhausted finite bounds reject
without publishing a truncated result. Helper-local active delimiters around
symbolic invocation remain unsupported rather than disappearing from a trace.

Cache 144 and verifier 46 record this proof change. Runtime and serialized
formats remain at native ABI 17 and bytecode 74/schema 118. General callable
field invocation still exposes an independent projection-ownership failure:
moving a generic callable field for its first call makes a second call fail at
runtime. Its regression remains active. Complete borrowed invocation, executable
replay-count admission, foreign-control admission, mandatory-tail handler fusion
and zero-marshalling/performance acceptance remain open.

## Evaluated invocation receiver views

Evaluation MIR now prepares place-based callees before evaluating arguments.
The frozen call contract identifies that receiver; Control MIR independently
matches it to its producer and rejects other consumers. Preparation is not an
ordinary read, source Copy, field move, or source `&F` coercion. Ownership,
specialization and cleanup preserve a same-typed non-owning receiver operation.
Static symbolic targets retain their existing erasure; runtime receivers use
explicit preparation and consuming-call instructions. Ordinary expression
caching cannot substitute a call-specific view for an owned Core value.

The existing executable resident domain wraps prepared views, including views
of ordinary callables. The verifier requires that wrapper at invocation and
rejects copying, moving, aggregation, return, disposal and all other executable
consumers. Borrowed storage cannot manufacture owned Fn permission. Invocation
unwraps only the authenticated receiver, uses the existing ordered capability
transition and retires the temporary before taking a resumption snapshot.
Source owners and capture environments are not copied merely to call a field.

Both engines transport this explicit carrier role in their shared register
storage. A suspended prepared view is rebased using the existing branch-wide
owner/environment map, not independently copied or retained as an outer owner.
Native carrier homes detach when rebasing, while borrowed outer environments
keep their identity. No second source analysis supplies this runtime role.

Cache 145, verifier 47, bytecode 75/schema 119 and native ABI 18 record the
boundary. The former generic-field replay failure passes across engines, as do
ordinary mutable capture fields and strict computed-receiver evaluation. This
does not complete receiver access/cleanup integration: replacing a receiver in
its argument still exposes destroyed native environment authority, and an
argument performance under replay exposes a remaining callable-owner quantity
failure in cleanup lowering. Both source regressions remain active. General
borrowed resumption invocation, executable replay-count admission, foreign-control
admission, mandatory-tail handler fusion and full zero-marshalling/performance
acceptance remain open.

## Structural resident quantities at ownership lowering

Ownership MIR derives a tuple or array owner's quantity from its evaluated
field owners in the existing quantity fixed point. A known callable environment's
Copy permission is distinct from its invocation interval and survives these
structural wrappers, ordinary forwarding and capture formation. Nominal values
retain their selected Use contract instead of inheriting physical field authority.

Replacement constraints include structural field writes as well as whole-slot
assignment. Unique borrowing or capture exposure limits initializer refinements
to the declared resident contract; an unknown writer cannot leave stale Copy
permission. Local storage and a reference carrier's referent remain distinct.
The receiving ownership validator independently bounds constructor and replacement
quantities by their input permissions. Cleanup replay consumes this same owner
inventory; it gains no callable-type exception or separate replay quantity rule.

Cache 146 records this source-to-ownership correction. The protected callable
aggregate with a prepared receiver and an argument performance now passes the
fresh/decoded VM and native/mixed execution matrix. This does not resolve receiver
lifetime across argument replacement or the remaining general native-handler
acceptance obligations. Runtime, verifier and portable formats are unchanged.

## Delimiter-wide executable invocation budgets

The existing executable handler frame carries the remaining invocation bounds
of its captured operation. Aliases do not receive new budgets. CFG joins retain
the extrema of all represented remaining counts; invocation requires authority
on every path and exact normal cancellation requires every path to be spent.
Direct resumption and ordered helper histories use the same decrement transition.
Non-returning snapshot transfer must consume the final invocation rather than
abandon required future replay.

Active protected execution is represented separately from a captured or spent
clause, independently of retained audit snapshots. Deep resumption and forwarding
restore the active state explicitly; clearing a one-shot snapshot cannot make
its serviced clause an active effect delimiter. Capture and handle retention
continue to require a live pending invocation. Runtime counters, continuation
ownership and final-original consumption remain unchanged.

Cache 147 and verifier 48 record this proof boundary. Local performances and
ordered helper use reject edited under/over-count policies before execution.
Cross-frame performance audit coverage is still incomplete: an ordinary callee's
resumptive performance does not yet seed its caller's clause, and the preserved
decoded mutation exposes that missing edge. This is not full executable replay
admission or completion of the remaining native-handler obligations.

## Outward executable operations and ordinary-call continuations

The executable control verifier publishes reachable outward operation identities
through direct calls, local performances and forwarding. The operation universe
comes from the existing checked program-wide payload/resumption ABI. Indirect
invocation uses its callable row over that universe; unresolved rows conservatively
admit every represented operation. Every first-class target must fit the row its
producer publishes, so editing a callable to appear pure cannot hide its body's
performance. Source effects are not reconstructed by a second Core walker.

The whole-program transfer product closes these may edges to a finite least fixed
point. Previously unreachable caller clauses can expose further operations.
Missing bodies, failed verification and unresolved final coverage cannot publish
absence. Helper capability contracts are rebuilt when the effect graph grows;
frame-preservation hypotheses strengthen around the same closed control edges.
Receiving body checks require their actual observations to remain covered by the
published product. No provisional empty set crosses that boundary.

A saved continuation distinguishes a local performance result from an ordinary
callee's normal return. Resuming the former initializes its operation result;
resuming the latter restores the separately checked normal call-result state and
audits the caller suffix under the pending completion ABI. The clause itself sees
consumed argument carriers and no future normal call result. The prior terminal-
only call seeder is removed. All continuation consumers share restoration rules.

Operation packets retain value provenance independently of suspended registers.
Forwarding transfers that packet, not the contents of future call-result slots.
An unmatched local forwarding edge can leave the ordinary activation; a returning
outer handler reinstates the declined deep delimiter and its saved suffix. Both
local and cross-frame dispatch retain first-active matching and delimiter-wide
budgets. A may-operation set cannot order performances relative to spending other
local capabilities in the same helper: unrepresented interleavings still reject.

Cache 148 and verifier 49 record this executable proof boundary. Bytecode
75/schema 119 and native ABI 18 are unchanged. The former ordinary-callee replay
count regression now rejects forged counts. General borrowed invocation,
helper-local symbolic delimiters, foreign-control admission, mandatory-tail fusion
and full zero-marshalling/performance acceptance remain open. Receiver replacement
still lacks its complete lifetime contract. An indirect replay fixture also
exposes stale resident quantity on a specialized callable parameter; its known
environment is Copy, but cleanup still receives the template's narrower quantity.
Neither remaining source regression is waived by the executable audit.

## Closed resident quantity constraints

Ownership MIR publishes its existing quantity equations as a retained product:
declaration inputs, known constructors, structural products, forwarding, captures,
replacement residents and writable exposure. Specialization substitutes the
normal closed types and solves those same equations again. It no longer copies
the template's owner quantities unchanged. Ownership-created consuming temporaries
extend the same product rather than losing their forwarding relation.

The existing trait/structural quantity solver distinguishes a declared contract
from additional sealed resident evidence. A known callable capture layout may
prove resident Copy independently of the callable's invocation interval. Unknown
environments and resumptions retain their declared interval; an empty capture
list alone proves nothing. Nested structural fields use the same solver and
nominal restrictions remain selected through ordinary declared prerequisites.
Resident refinements cannot select a source trait implementation or widen the
contract of storage exposed to an unknown writer.

Cleanup consumes the resulting closed owner inventory without a replay-specific
callable exception. A private dependency seal binds those quantities to the
receiving specialized instance, types, operations, loans and capture contracts
after symbolic-target representation mapping. Independent structural validation
and proof binding reject edited or mismatched inputs. Nonconverging constraints
reject instead of publishing a partial solution.

Cache 149 records this ownership/specialization correction; executable verifier,
bytecode and native ABI generations are unchanged. The indirect-callee replay
regression and its owned-Copy-capture composition now pass across engines. Receiver
replacement still lacks its complete lifetime contract. Borrowed invocation,
helper-local symbolic delimiters, foreign-control admission, mandatory-tail fusion
and full zero-marshalling/performance acceptance remain separate open obligations.

## Strict quantity input snapshots

UseFlow freezes the evaluated callee before its strict arguments, and freezes
each argument and aggregate field before evaluating the next. Ordinary invocation,
checked helper execution and operation-payload escape consume these same value
snapshots. Later replacement of source storage cannot change the capability
already supplied at an earlier position. Closure formation refreshes its capture
snapshot on each execution, while retaining the existing frame-local cache scope.
The prior late argument lookup and recursive outgoing-value lookup are removed.
Known enum-constructor layout checking still supplies the typed escape contract;
it selects fields from the evaluated product, not from the final environment.

Specialization also binds retained resident-quantity equations to their original
Ownership MIR input before closing them. The existing closed receiving seal is
not permission to reuse stale source equations after an instruction, owner,
alias, loan or capture-contract change.

Cache 150 records these source/ownership boundaries. Snapshot analysis now rejects
the original affine receiver's double use instead of charging the replacement.
Runtime strict-value materialization is still incomplete: an ordinary argument
or aggregate field can retain a source alias until after a later operand replaces
it. Both new execution regressions remain active, alongside the prepared receiver's
native lifetime failure. A correct quantity snapshot is not a runtime lifetime
or materialization proof, and none of the remaining native-handler acceptance
requirements is waived.

## Strict runtime value acquisition

Evaluation MIR now distinguishes deferred place reads, acquired values and
invocation-only views. Every strict ordinary argument, aggregate field, operation
payload, intrinsic input and assignment RHS is acquired before the next operand
is evaluated. Existing rvalues already own their storage and need no additional
acquisition. Place projections and invocation preparation retain their distinct
observational contracts; neither a late consumer nor expression-cache reuse may
turn an acquisition back into an alias of replaceable source storage.

The receiving Evaluation validator derives operand roles from instruction
definitions and rejects unacquired strict inputs and acquisition of an
invocation-only view. Control carries an explicit acquisition, distinct from a
forwarded observation. Ownership selects the existing checked Copy, move or
resumption-retention operation at that point and tracks the resulting temporary
through the ordinary inventory. An affine argument therefore leaves its source
owner before the call, and the call transfers the acquired owner. No runtime
opcode, callable ABI or independent source analysis is introduced.

Cache 151 fixes both ordinary argument and aggregate-field replacement execution
regressions. All 51 other handler-reentry tests pass across their fresh/decoded VM,
native and mixed execution matrix. The prepared-receiver native lifetime
regression remains active and excluded from that passing count: observation of
an invocation resident still does not itself preserve ownership against a later
replacement. The existing associated-effect forwarding integration fixture also
fails at the earlier source G5024 minimum-use check; this checkpoint does not
claim that suite passes.

## Stored body-region views

Runtime and legacy MIR Store validation share the existing region-term traversal
to compare storage types modulo closed body-local loan identities. Source/Core
still establish directional lifetime validity, and executable reference
provenance still governs actual storage access and escape. A store does not
equate those source loans or acquire a new outlives proof. Rigid, generic and
bound regions, reference mutability, callable receiver permission, safety and
all remaining type contracts are retained by this comparison.

Cache 152 fixes assignment between checked reference handles whose body-local
loan IDs differ. The borrowed receiver selected before replacement of its
reference handle now passes the full VM/native/mixed matrix. Existing reference
replacement/escape checks and assigned-tuple outlives checks also pass. Repeated
invocation of an owned callable with mutable scalar captures preserves its
capture storage, demonstrating why indiscriminate receiver copying is not a
lifetime fix. The original owned-receiver replacement still fails natively;
a capture-bearing replacement regression additionally exposes Control's exact
receiver/place type check conflating stored and value-refined callable contracts.
Both remain active, not ignored or counted as passing acceptance gates.

## Normalized callable value joins

Core applies retained callable joins to the value and both sides of each join
after resolving them in the same inference world. Previously an initializer
containing an already-solved inference cell could miss a join that its later,
resolved local read received. The constructor/binding then retained a nominal
capture environment while its invocation used the joined environment view.

Types, generic arguments and effect rows now consume the same kind-preserving,
binder-aware join application. This changes normalization order, not the join's
receiver, capture, region or residual-predicate rules. No additional binding-type
table, Core field or downstream callable coercion is introduced. Existing typed
consumers receive the corrected source product.

Cache 153 fixes the capture-bearing replacement case's Control type mismatch.
Its execution gate remains failing in the VM with a result error (`ResultType`,
I64 on both sides); receiver lifetime is not proved by type agreement. All 17 Evaluation
integration checks pass, including direct and generic join consistency. Selected
generic/quantified callback checks and wrong receiver/post-state rejection pass.
The 31-test borrowed-callable run had 27 passes and four failures; each failure
also reproduced with this normalization change removed. Their cancellation and
residual-predicate expectations remain active and are not claimed as solved.

## Ordered exact storage replacements

The shared callable-control evaluator now represents checked exact assignments
in its existing ordered execution log. RHS acquisition precedes destination
evaluation. Local bindings and reference handles retain storage identity;
place reads apply the log, while already evaluated operands keep their original
value snapshots. Writes survive lexical binding restoration, helper return and
local-label transfer. Branch alternatives retain their separate guards and logs.
No independent Core mutation walker or second mutable storage graph is added.

A partial replacement invalidates whole-aggregate forwarding provenance without
erasing untouched field origins. The changed resident has an origin distinct
from the assignment expression's Unit result. Existing return-payload consumers
therefore project updated fields rather than forwarding the original aggregate.
Read-only coverage classifies every store as a write; performance-absence coverage
can distinguish a represented write from an algebraic suspension. Minimum-use
checking consumes that same complete execution proof.

Symbolic referent aliases, opaque field shapes, unproved replacement cleanup and
owned-capture identity across source Copy/Move remain unresolved. Owned environment
slots are typed identities rather than ordinary lexical slots; a source alias
cannot authorize a strong update of that environment. Storage-log queries charge
the existing bounded control work budget and publish unknown on exhaustion.

Cache 154 fixes the false cancellation rejection for a nonperforming helper that
mutates exact local storage. Its fresh/decoded VM and native O0/O2 gate passes,
and an actually performing alternative still rejects. Control tests cover scopes,
aliases, helpers, borrowed captures, guards, transfers, strict input snapshots,
partial-result provenance and conservative unsupported destinations. Eight older
control tests still fail at source G4155 before this analysis; all eight reproduced
with this change removed. Receiver acquisition/lifetime across argument replacement
is still open: an ordered write fact is not itself a loan-retention or ownership
proof. General borrowed resumption invocation, helper-local symbolic delimiters,
foreign-control admission, mandatory-tail fusion and full zero-marshalling/
performance acceptance also remain open. Executable and runtime generations do
not change.

## Retained reference residents at strict boundaries

PlaceFlow's existing strict sequence evaluator now publishes positional input
residents in its loan graph before evaluating the next operand. Invocation
stores, declared reference/callable results and observed normal/label returns
consume those residents. Aggregate construction and assignment destination
evaluation use the same acquisition rule. The invocation adapter no longer
accepts a Core expression as a deferred storage lookup, and the old recursive
call-result argument reconstruction is removed.

Value transport preserves backing loans and upstream reborrow ancestry without
borrowing the replaceable source handle slot. A borrowed unique receiver view
retains its carrier authority instead. Results inherit those debts before input
temporaries retire. Repeated evaluation of a shared Core node acquires distinct
input residents; a completed expression result is not a memoized source value.
Empty aggregate payload proofs survive this publication and retirement boundary.

Cache 155 rejects mutation of an original referent after its reference was
evaluated as an argument or field and its source handle was subsequently replaced.
It also retains assignment RHS provenance across destination side effects.
Positive replacement, upstream unique reborrows, captures, borrowed receiver
views, shared-Core occurrences and fresh/decoded VM/native execution are covered.
Twenty-seven reference-result tests pass; one newly preserved handler-payload
regression still fails: clause binding reconstructs the operation's inputs after
argument replacement. That consumer has not yet migrated, so this checkpoint
does not establish complete operation-payload or guarded suspension provenance.

Nearby tests also retain baseline failures: label-call preparation rejects two
fixtures, one temporary-borrow fixture expects a different source diagnostic,
and another fails with destroyed native environment authority. All four failures
reproduce with this change removed. Owned receiver acquisition/lifetime, general
borrowed resumption invocation, helper-local symbolic delimiters, foreign-control
admission, mandatory-tail fusion and full zero-marshalling/performance acceptance
remain open. Executable verifier, portable formats and runtime ABI do not change.

## Deferred handler payload bindings

The existing active handler frame now carries both suspension disposition and
the input relation for its directly protected invocation. Strict operation and
call consumers publish clause payload transfers while their evaluated inputs
still exist. Clause binding consumes that product; it no longer rereads the
operation's or helper's Core arguments from post-computation storage.

Ordinary pattern binding and handler payload binding share a deferred reference
snapshot containing physical/logical provenance and upstream source-carrier
ancestry. Installing a snapshot does not depend on a retired argument temporary's
namespace. Source Copy/Move transfers existing debt without borrowing its old
handle slot; a real upstream unique reborrow remains suspended. An unobserved
input relation is explicit and is not a proof of an empty reference footprint.

Cache 156 fixes the preserved handler-payload replacement regression. Direct and
helper-forwarded payloads, tuple fields, upstream carrier suspension/release and
native O0/O2 execution pass. All 30 reference-result tests pass, as do selected
ordinary pattern/capture, positional borrowed-payload and label-return loan gates.
This migrates the existing direct-protected-invocation relation, not a general
guarded suspension-state solver: nested performances, branch correlation and
payload liveness across arbitrary resumption/suffix interleavings still require
that broader product. The cache-155 baseline failures and remaining receiver,
native-handler and full-conformance obligations are unchanged. No executable or
runtime format changes.

## Prepared nominal label authority

Runtime MIR receiver preparation now consumes the same compiler-owned nominal
label Fn view as invocation validation. A label value can be selected before
strict arguments without becoming an addressable environment. The preparation
keeps its exact nominal type and brand; it does not authorize a label reborrow,
change an arbitrary nominal into a callable, or infer a local transfer target.
Existing runtime proof erasure and executable destination authentication remain
independent requirements. No new label representation or semantic walker is added.

Cache 157 fixes both preserved G7041 label-preparation regressions. Generic
label forwarding with reference payloads passes fresh/decoded VM and native/mixed
O0/O2 execution. Runtime validation rejects a changed destination brand, label
addressing and non-callable preparation. This repairs the receiving type contract,
not owned callable acquisition across argument replacement, general borrowed
resumption invocation, mandatory-tail fusion or complete native-handler and
full-conformance acceptance. Executable formats and runtime ABI are unchanged.

## Checked invocation acquisition

Evaluation MIR no longer grants an invocation-only carrier because the callee
looks like a place. PlaceFlow publishes the receiver acquisition selected by
its existing loan transitions. A retained owned receiver keeps its source
storage live across every strict argument. That retention is not a source
`&F` coercion and does not supply borrowed Fn permission or change invocation
quantity. The original receiver contract remains authoritative.

Receiver retention is an alternative in that same source solver. Its complete
state is committed only when the argument transitions preserve the proposed
storage loan; otherwise ordinary owned acquisition must satisfy the existing
Copy/move rules. Alternative work has a shared structural budget which does not
roll back, and exhaustion rejects. Shared Core calls with inconsistent selected
acquisitions reject instead of publishing a permission from one occurrence for
another. Lifted bodies consume their own resource product, not their parent's
receiver choices. The full typed input fingerprint binds these facts to lowering.

Cache 158 fixes the two preserved native receiver-replacement failures, while
repeated mutable capture invocation and field-receiver replay retain their
existing environments. No runtime pinning or unconditional source Copy is added;
existing acquisition, invocation, quantity and cleanup operations implement the
selected result. Evaluation tests distinguish overlapping from disjoint field
replacement and retain the resolved callable value type on owned acquisition.

This is not complete receiver or native-handler acceptance. The computed-field
factory still retains a conservative callable-result loan on its input. New
active tests expose tuple callable replacement typing and helper-stored callable
quantity/initialization failures. A borrowed-callable integration run reports
27 passes and four expected-rejection failures; the unused generic cancellation
case also reproduces with the previous receiver logic, while its executed
cancellation counterpart rejects. These failures are not reclassified as
passes. General borrowed resumption invocation, guarded resource interleavings,
mandatory-tail fusion, foreign control and full performance acceptance remain
open. Verifier 49, bytecode 75/schema 119 and native ABI 18 are unchanged.

## Directional stored callable inputs

The callable type product owns the directional invocation input view previously
local to Core call checking. Assignment and both MIR Store validators consume
that same rule. Owned tuple and array products propagate the input view while
reference handles retain their unchanged referent contract. Type comparison
still checks all other components, including closed-body versus rigid regions,
receiver authority, effects and safety. A comparison view does not rewrite the
acquired value's quantity or weaken the destination's declared ABI.

Cache 159 repairs the preserved whole-tuple receiver replacement through fresh/
decoded VM and native/mixed O0/O2. Source tests retain distinct acquired and
destination callable quantities through direct, tuple and fixed-array stores;
receiving rule tests reject reversed or strengthened permissions and referent
coercion. Helper-mediated receiver replacement still requires a correction to
resident quantity and initialization, not a runtime keepalive. Computed factory
lifetime, general borrowed resumption invocation, guarded interleavings,
mandatory-tail fusion, foreign control and full performance acceptance remain
open. Executable and runtime generations do not change.

## Executed resident permissions for storage views

The retained ownership quantity product distinguishes an initial produced value,
replacement residents, declared writable exposure and whole-storage constraints.
For whole-slot observations of changing storage, the existing Control CFG derives
the reaching resident at every executed use, not merely at the earlier Read.
A deferred view used after replacement therefore cannot keep an old acquisition
permission. Complete ordinary joins retain every possible resident; missing state
has no permission. Dynamic control transfers conservatively retain the global
storage constraint rather than infer unrepresented handler interleavings.

The ordinary quantity fixed point solves these inputs with its existing products,
capture equations and slot-wide replacement/exposure bounds. Storage owners retain
their whole-lifetime guarantee while an earlier acquired value can retain stronger
resident permission. Specialization closes this same product; no second Core walk,
runtime pin or new Copy operation supplies the distinction. Ownership validation
binds the exact receiving input, including operation order, before accepting the
point-sensitive result. Source availability and runtime initialization checks
remain independent requirements.

Cache 160 admits the earlier scalar-capture receiver acquisition before writable
exposure through fresh/decoded VM and native/mixed O0/O2. Post-exposure and joined
reads retain their restricted permissions, earlier replacement/field negatives
remain enforced, and reordered operations cannot reuse the proof. The preserved
helper-mutation case still has its source callable-transfer obligation. Projected
and referent view refinements remain conservative, as do dynamic interleavings;
computed factory lifetime and the broader native-handler acceptance gates remain
open. Executable and runtime generations do not change.

## Checked outgoing assignment boundaries

The existing PlaceFlow assignment transition produces the ownership boundary
from actual reference targets, using the same resolved destinations for store
validation and resident-origin updates. Retained lifetime debt is not destination
authority. Repeated occurrences must agree, and the full typed-body seal binds
the resulting product. UseFlow consumes positive outside-frame evidence for a
callable assignment transfer, after RHS acquisition and destination evaluation.
Tracked direct local storage retains its resident accounting. Unrepresented
local/unknown storage of quantity capabilities rejects; general local-reference
resident tracking remains an explicit integration obligation.

Native referent initialization probes use the existing authenticated reference
and backing initialization tree. They inspect the selected shell without reading
payload or confusing same-address zero-sized fields. No second initialization
map or callable-specific storage exception is introduced.

Cache 161 verifies source transfer boundaries, destination order, stale evidence
and combined-demand rejection, plus factory-callable replacement through fresh/
decoded VM and native/mixed O0/O2. A VM/native probe test covers move-out, disjoint
zero-sized fields and restoration. Native ABI becomes 19. The original helper
mutation still fails writable-callable referent ABI validation; mutable reference
invariance remains enforced. This is not complete native-handler acceptance.

## Writable callable resident alternatives

A concrete writable referent supplies a possible future resident, not merely
an optional structural annotation. Fresh unique borrowing of an owned place
feeds that alternative into the existing callable value join. The shared
contract rule intersects environment and receiver authority while retaining
capture-region and invocation debt. Callable ABI components remain fixed;
the storage-view transformation does not traverse existing references or
callable parameters/results. Owned tuple and array products compose the rule.

Cache 162 repairs the preserved helper-mutation receiver gate through fresh/
decoded VM and native/mixed O0/O2, with nine selected receiver gates passing.
Post-exposure borrowed access rejects and capture debt remains attached.
This is a whole-body type join, not point-sensitive receiver permission:
the new earlier-borrowed-invocation regression still fails G4304 after a later
helper replacement erases its refinement. That integration obligation, nominal
storage refinements, computed-factory lifetime and full native-handler acceptance
remain open. No executable or runtime ABI generation changes.

## Owned factory-result footprints

Complete normal-return alternatives in the existing invocation relation can
prove a callable result's capture footprint owned. This is distinct from both
physical-reference target coverage and absence of observed loans. Unknown
control, missing return alternatives and borrowed captures do not establish it.
PlaceFlow and EscapeFlow consume that same returned product before installing
the fallback for possible hidden factory captures. Declared capture regions,
forwarded callable residents, free result regions and explicit outlives debts
remain independent obligations. The duplicate PlaceFlow result-path derivation
is removed; no source-name exception or new Core walk supplies this evidence.

Cache 163 verifies capture-free factory receiver acquisition through fresh/
decoded VM and native/mixed O0/O2, while an actually captured input retains its
strict-argument conflict. Unknown/mixed return and declared/forwarded-debt tests
remain enforced. The original arithmetic-prefix receiver is still blocked by
missing-body control outcomes, and point-sensitive borrowed receiver contracts
and full native-handler acceptance remain open. Runtime generations are unchanged.

## Manifest-bound scalar control outcomes

The staged control producer consumes the same runtime identity bindings as MIR
lowering. Declaration admission shares the manifest's exact signature check;
closed integer inputs/results share the existing materialized scalar ABI. No
source name, empty effect row or missing body establishes runtime authority.
Open generic, non-scalar and unsupported primitive contracts remain unknown.
The frozen summary batch includes the runtime bindings in its dependency seal;
body-only binding, changed selectors and changed declarations cannot reuse it.

Returning integer leaves produce unknown scalar values, not invented literals
or forwarding provenance. Checked arithmetic, shifts and checked conversions
retain a distinct possible runtime trap. Traps stop their strict suffix without
becoming algebraic cancellation, label transfer or divergence. Ordered execution,
coverage limits, return footprints and both resource consumers continue through
the same invocation relation; no new consumer-side primitive analysis is added.

Cache 164 fixes the preserved arithmetic-prefix computed receiver across fresh/
decoded VM and native/mixed O0/O2. Binding/ABI rejection, trap/return distinctions
and truncated coverage remain checked. Earlier point-sensitive borrowed receiver
contracts, general borrowed resumptions, guarded interleavings, mandatory-tail
fusion, foreign-control admission and full performance acceptance remain open.
Executable and runtime generations are unchanged.

## Constructed callable values and binding storage contracts

Typed Core bindings retain their stored type separately from the initializer's
produced type. The existing normalized join producer applies whole-storage
constraints to that binding without replacing a callable constructor's own
checked environment and receiver contract. Nested resident terms still consume
the same joins. This preserves constructed code evidence, not point-sensitive
permission for every subsequent read of its storage.

Evaluation carries the stored binding contract explicitly; Control allocates the
binding with that type rather than reconstructing it from the initializer.
PlaceFlow's stored destruction/minimum contracts and structural fusion consume
the same field. Source, Evaluation and Control validation check the directional
initialization relation. Fingerprints, inference sealing, projection-domain and
binder validation include the new type. Runtime/legacy stores share that same
type-owned resident comparison: weakening cannot invent receiver/environment
authority or erase capture/predicate debt, and does not traverse reference
referents, callable ABIs or nominal identities.

Cache 165 verifies distinct constructed/stored contracts, stale fingerprints,
forged receiver and capture-debt rejection, and the helper replacement execution
matrix. The handler integration run remains 62 passing and one failing: the
earlier borrowed receiver still fails G4304 after its slot is widened. Actual
borrowed-invocation authority must be established at its executed acquisition,
not recovered from the constructor merely because it once occupied the slot.
That source/executable proof migration and the remaining native-handler gates
are not completed by this storage boundary. Runtime formats are unchanged.

## Executed borrowed receiver obligations

Frozen declaration validation separates callable ABI/prerequisite selection
from borrowed receiver permission. A widened reference type can leave an explicit
pending receiver obligation, not a successful standalone validation. The staged
control batch retains these obligations in its body dependency seals. Binding
discharges them from the existing evaluator's actual invocation inputs, with
complete coverage across isolated callable occurrences. Expanded caller-specific
inputs, missing observations, unknown paths and analysis limits cannot establish
a helper's universal permission. No source ownership product is published before
this binding, and ordinary loan checking still rejects conflicting mutation.

The executable verifier independently transports receiver permissions in its
existing resident-value product. The bounded must contract covers every possible
callable leaf; heterogeneous products remain conservative. Checked construction,
owned value transfers, borrows and projections supply the evidence. CFG joins
intersect it; replacement, writable exposure and unknown execution revoke it,
including aliases and saved continuations. Structural reference-origin transport
uses the same producer so aggregate aliases cannot hide from invalidation.
Invocation authenticates its input before its own mutation invalidates suffix
facts. Forgetting a reference view's contract cannot retain hidden stronger
permission. Neither the reference's ABI nor its native backing layout changes.

Cache 166 and verifier 50 repair the earlier borrowed receiver regression.
The full handler-reentry gate passes all 63 tests, covering fresh/decoded VM and
native/mixed O0/O2 execution. Source checks reject incomplete/stale evidence;
executable checks reject replaced residents, mixed-permission joins, unknown
writers and weakened-reference authority. Removing the checked constructor's
permission also rejects after decoding. A newly added tuple-projection composition
still fails Core G4183: widening its parent tuple has not widened an earlier
projected field type. That join-projection integration remains active; it is not
included in the preceding 63-test passing checkpoint. This is not yet full native-handler
acceptance: general borrowed resumption admission, helper-local symbolic
delimiters, guarded interleavings, foreign control, mandatory-tail handling and
complete shared-storage/performance evidence remain to be assessed or completed.
Bytecode 75/schema 119 and native ABI 19 remain unchanged.

## Structural projections of stored callable joins

The type-owned callable join relation publishes its owned structural projections
after both sides are normalized in the same inference world. Tuple and array
fields consume the parent's storage constraint; references, nominal identities
and callable input/result contracts do not acquire independent leaf rewrites.
Constructed callable values retain their own checked environment and receiver
contract while nested stored residents consume the same projected joins.

Core, Control, Ownership, Specialized, Cleanup and executable MIR validate
structural construction using the existing directional stored-resident relation.
An aggregate's stored field may forget additional receiver authority, but it
cannot invent authority or erase captured-region and predicate obligations.
The previous exact-field comparisons at these boundaries are removed. Legacy
MIR consumes the same rule. Native resident field transport uses the whole-home
type/layout relation and retains authenticated environment identity and logical
initialization holes; it does not create a new closure or grant source Copy.

Cache 167 fixes the preserved projected borrowed-receiver regression. The full
handler-reentry gate passes 64/64, including fresh/decoded VM and native/mixed
O0/O2 execution. Focused type, Core, Control and native tests cover projection
boundaries, receiver strengthening, captured debt, environment identity and
partial initialization. Verifier 50, bytecode 75/schema 119 and native ABI 19
are unchanged. This closes the receiver/storage regressions, not the remaining
native-handler admission and shared-storage/performance acceptance audit.

## Measured resident entry transport

The existing native allocation owners supply opt-in backing-extent and bulk-copy
measurements to both native and mixed runners. Machine entry measures the interval
in which each already-present addressable resident is admitted, before generated
computation starts. Empty future frame slots and private scalar spills are not
shared-object adapters. Counters saturate explicitly; they do not claim to measure
Rust metadata, allocator-internal work or process RSS. No profile fact supplies
semantic authority or changes storage admission.

Profiled replay and shared-payload integration checks observe zero resident-entry
allocations and copied bytes. A 1,000-iteration mixed mandatory-tail cycle completes
its local handler before each backedge at O0/O2 under eight-call/eight-handler/
eight-continuation and 128-KiB native limits. Its VM and decoded executions pass as
well. This supplies evidence for ended delimiters, not a waiver for an active
unfused handler at a mandatory tail site.

The new cross-engine unique operation-payload address/mutation regression still
fails source G5013 before execution. EscapeFlow retains directly performed payloads
but clears helper-performed clause bindings, so a checked unique reborrow has no
incoming payload snapshot. The test remains active. Its address and mutation
assertions have not passed and complete shared-handler storage acceptance remains
open. Cache 167, verifier 50, bytecode 75/schema 119 and native ABI 19 are unchanged.

## Evaluated helper-performance payloads

The sealed callable-control relation now projects operation payloads from the
same evaluated explicit/captured inputs as ordinary returns and label transfers.
Its performance coverage is distinct from normal-return coverage. A resumable
operation at a proved tail frontier retains its input relation, but does not
prove what the handler or resumption returns. Skipped suffixes, pending invocations
or pattern decisions, opaque execution and limits revoke that frontier. Complete
branch alternatives retain every possible payload, not only the first observed
performance. Terminal performances consume the same relation.

PlaceFlow acquires these payload snapshots before releasing invocation inputs;
EscapeFlow acquires them at the same evaluated call boundary. Both bind handler
patterns from the published product. The old PlaceFlow inference from separately
declared operation lifetimes is removed: unrelated lifetime indices cannot supply
a referent identity. Unknown performance coverage still supplies no borrow proof.

The existing ordered storage evaluator also represents scalar writes through
symbolic input references. These are weak writes: later possibly aliased reads
lose known contents and prior guards, without acquiring the RHS or equating
distinct inputs. Already evaluated operands and local reference handles retain
their identities. Reference-containing external writes and unresolved cleanup
retain their existing conservative boundary.

Cache 168 closes the unique-payload address/mutation regression in fresh/decoded
VM, native and both mixed directions at O0/O2, with zero measured resident-entry
allocations and copied bytes. The full handler-reentry gate passes 66/66, including
nested aggregate payload reborrows and rejection of helper payloads escaping local
storage. Focused producer checks cover captured inputs, branch alternatives,
pending resumption suffixes, limits and alias invalidation. This completes this
source provenance boundary, not general guarded resumption analysis or the whole
native-handler admission audit. Executable formats and native ABI are unchanged.

## Helper-local delimiters and owned runtime branches

The executable verifier's ordered capability product retains producer-local
resumption trace dependencies while auditing a helper's local handlers. Closing
the worklist expands those dependencies before publication. Returning paths
compose in order; nonreturning paths preserve only executed prefixes. Missing
dependencies, cycles and finite expansion limits reject. No raw local trace
reference or incomplete event set can become a caller contract. Ordinary helper
frames remain executable; source inlining is not this admission proof.

The shared runtime distinguishes a logical owning activation from its coordinate
in an ordinary call path. A performance can cross returning-resumption edges and
enter a helper's saved clause path. Its continuation retains exactly those crossed
edges; resuming restores them in order after the new clause-return edge. Dispatch
selects the real owner's clause context, and payload/result transport uses the
two paths' actual common ancestor. Source homes, native reference authority and
logical initialization remain the existing storage representation.

Every ordinary snapshot of one performance shares its remaining invocation
authority. Consuming the original invalidates older clause views without making
them active effect delimiters. Checked replay duplicates internal authority with
one rebasing map, preserving aliases across retained clause paths; outside
pending obligations remain shared. Final use still transfers the original.

Handler installation publishes the runtime's outside-storage frontier from the
existing protected-owner partition and actual caller views. A clause view is
not ownership of the protected roots retained by its pending continuation.
Replay and cancellation consume this same frontier across all captured call and
clause paths. Shared source synchronization matches activation and allocation
identities, never an unrelated frame at the same numeric depth. Cleanup walks
the retained paths in execution-return order and consumes pending authority once.
Terminal cancellation preserves unrelated enclosing return edges.

Cache 169, verifier 51 and native ABI 20/control convention v2 verify all 75
handler-reentry tests through fresh/decoded VM and native/mixed O0/O2 execution.
Focused checks cover local trace closure, missing/cyclic evidence, shared versus
copied budgets, actual-path reference transport, protected Drop and payload
mutation. Bytecode 75/schema 119 are unchanged. Retained-control limits and local
label-transfer composition remain under milestone review; this checkpoint does
not claim general guarded source analysis or full compiler/library conformance.

## Retained control graph limits

The shared runtime's remaining-control limit counts pending performances and
returning-resumption edges across the complete retained graph. Ordinary views
retain their identities, while the existing replay identity map creates distinct
internal edges and preserves copied aliases. A spent pending view has no live
authority; its running continuation's return edge still counts. Runtime branch
transitions check this product and active handler depth before further execution.
The previous top-level pending-handler count is removed.

Ordinary handler views share their immutable pending image rather than recursively
cloning retained subgraphs. Mutable packet access uses copy-on-write metadata;
final consumption still transfers the original resident storage and one shared
use authority. This is not source Copy, an alternate continuation budget or a
new native value representation.

Cache 170 verifies exact low/enough limits in fresh/decoded VM and native/mixed
O0/O2, branch/replay alias identity, protected cleanup, and the existing bounded
1,000-iteration handler/tail cycle. Verifier 51, native ABI 20/control v2 and
bytecode 75/schema 119 are unchanged. Local-label transfer composition remains
under milestone review. The counters do not claim exact allocator/RSS accounting.

## Lexical handler exits and dynamic return frontiers

Cleanup's existing label contract retains exact handler-clause identities.
Runtime lowering now preserves those identities through clause installation,
control-table freezing, block editing and VM LIR relocation. Executable leaves
name both their retained lexical prefix and their crossed installations. The
old function-local depth and instruction-local fallback are removed. Receiving
MIR validates the prefix against its frozen scope product; LIR rejects missing
or non-installation relocation targets; the bytecode verifier checks ordered,
live, nonrepeated identities and consistent branded destinations.

An installation retains its actual outside-handler frontier in the existing
control frame. Resumption call-site handlers can be interposed among lexical
entries, including within the same logical activation. Leaving a local label
preserves those entries when no delimiter is crossed. Crossing a delimiter
also leaves call-site entries belonging to its discarded clause path, using
the installation frontier rather than a count of same-owner frames. Verifier
and runtime consume this same distinction. First-class label carriers retain
the actual handler prefix and authenticate their original activation coordinate;
they gain no new opaque-call or structural-fusion permission.

The shared runtime removes only crossed resumption-return edges. Their saved
clause paths use the existing abandonment worklist and storage frontier; an
unrelated outer resumption return survives. No independent label stack, new
resident representation or native marshalling bridge is introduced.

Cache 171, verifier 52, bytecode 76/schema 120 and native ABI 21/control v3
record these contracts. Focused tests cover local and callee labels, interposed
call-site handlers, selective return-edge abandonment, malformed prefixes,
relocation and wire rejection. The clause-Drop composition test remains an
active source failure: ownership currently skips a handler clause when the
protected computation eventually transfers to a label, despite its earlier
performance. That source suspension-input boundary remains to be repaired;
this checkpoint does not claim full native-handler or language acceptance.

## Executed suspension inputs and dynamic clause ownership

PlaceFlow's existing handler input product retains the complete ownership state
at an executed suspension, before any future result is materialized. Exact-use
performances supply inputs even when the protected suffix later leaves a label.
Cancellation minimum-use states are a projection of the same snapshots. An
unresolved call row conservatively retains possible enclosing clause inputs;
it neither supplies payload provenance nor discharges conditional obligations.
Unobserved clauses are still checked, but cannot publish an invented exit.
Returning protected states remain conservative post-resumption alternatives.

Evaluated result carriers keep their temporary ancestor relation until retirement.
Deferred pattern transfers retain exact live input loans alongside source ancestry;
installation authenticates those loans against the restored state. Retired or
replaced temporary names alone grant no reborrow permission. The original payload
escape regression still reaches the source escape rejection.

Cleanup's existing ownership inventory publishes protected roots and per-clause
owning roots from frozen definition, scope and exit facts. It stops at handler
completion and labels outside the delimiter. Runtime MIR, VM LIR and bytecode
carry that one product; their receiving checks reject absent and noncanonical
roots. The executable verifier starts clause roots uninitialized on every
performance, helper dispatch and forwarding edge, without erasing the saved
continuation's facts.

The shared runtime uses those roots to start a distinct dynamic clause allocation.
An older returning clause retains its own homes and allocation brands; entering
the same clause again neither overwrites nor destroys those residents. The
installation storage frontier records the current clause's shared homes while its
continuation runs. Abandoning that clause's return edge consumes its clause-owned
roots, not unrelated outer storage. This extends the existing frame/ownership
contract rather than guessing ownership from whether a register is initialized.

Cache 172, verifier 53, bytecode 77/schema 121 and native ABI 22/control v4 name
these contracts. Source and executable checks cover stale input loans, moved
inputs, fresh clause initialization, selective label cleanup and deep clause
re-entry. Complete guarded source-resource analysis remains a separate obligation.

## Source Copy acquisition from runtime storage views

Ownership lowering publishes an explicit place acquisition for a referent value;
only intermediate reference observations retain the non-owning view operation.
Its validator rejects a reference observation with an owning destination.
Cleanup MIR's `ValueTransfer::Copy` remains the authority for acquiring an owned
resident from a place. Runtime lowering now preserves that acquisition after a
reference or aggregate projection: the physical read produces a non-owning view,
then the existing `Copy` operation produces the owning destination. Whole-value
copies already use that operation. Moves, reborrows, retained resumptions and
non-owning reference reads keep their distinct paths.

Both execution engines consume their existing structural owned-copy machinery,
which duplicates callable environments and their owned captures while preserving
borrowed referents. No read opcode gains implicit ownership, no runtime lifetime
check is weakened, and no second ownership inventory is introduced. Cache 173
invalidates earlier lowering; executable schema and native ABI are unchanged.

This repairs already-proven Copy transfers. Propagating concrete resident quantity
through stateful callable projections remains an active failing source regression:
ownership lowering currently emits two moves for accepted repeated tuple reads.

## Resident evidence before source transfer selection

Ownership lowering now uses the existing trait solver's sealed resident-use
query when initializing the same quantity equations that specialization closes.
It does so before classifying storage observations and choosing transfer modes;
closing a quantity after a Move has already been chosen is too late. Declared
quantities remain distinct and continue to bound replacements and writable
exposure. Missing resident evidence falls back only to the declared guarantee.

Cache 174 fixes stateful callable copies through tuple and nominal projections.
The focused ownership checks and VM/decoded/LLVM stateful-copy matrix pass.
The source lane still delegates ordinary affine callable occurrences to invocation
checking; the new unique-capture double-projection rejection test remains active
and fails because source acceptance precedes a runtime second-move rejection.
Repairing source carrier ownership without conflating it with resumption-use
budgets and borrowed invocation remains the next boundary obligation.

## Source ownership of materialized callable carriers

PlaceFlow consumes the same sealed resident-use query before deciding whether
an ordinary value occurrence copies or moves storage. Materialized callable
environments no longer bypass its existing move-path rules merely because their
invocations also carry quantitative obligations. Direct aliases and aggregate
projections preserve canonical place identities, including typed annotations.
Borrowed invocation still retains the source carrier through its existing
receiver-acquisition relation; it is not an ordinary owning occurrence.

Cache 175 closes the concrete unique-capture double-transfer regression. Its
positive matrix also checks repeated invocation after one affine transfer.
Opaque callable and resumption contracts retain the existing quantitative lane;
missing environment evidence does not grant Copy or establish physical absence.
The source and execution gates above do not prove complete guarded ownership
through every opaque/generic control boundary.

## Normalize grouped types at the syntax boundary

The declaration and body type parsers retain comma presence until they have
distinguished a callable parameter list from a parenthesized type. Both then
use one HeaderType constructor: a single comma-free item is its grouped child;
all other lists retain tuple arity. Elaborators, associated Fn argument-pack
validation, and later representations receive the normalized type, not an
artificial singleton tuple requiring consumer-specific repairs.

Cache 176 invalidates earlier parsing. No executable wire format or ABI changes.
Parser and VM/decoded/LLVM grouping checks pass, including rejection of scalar
Fn argument packs and lack of implicit tuple conversions. Grouping does not add
an effect-row equality or borrowed-call authority to an opaque callable.

## Prepared receiver transport through label forwarding

Executable forwarding-shim analysis consumes both owned indirect invocation
and the prepared invocation protocol emitted for ordinary source helpers.
Its existing input-origin product distinguishes a prepared receiver from an
owned input: preparation acquires the exact input identity without consuming
it, and only an ordinary carrier can supply the transferred payload. Cleanup
still must be harmless label disposal; unknown instructions remain unproved.

The resulting Shim is consumed by the existing local-label transfer worklist,
which validates the destination rather than declaring a nonreturning call or
its suffix harmless. Exposed storage and mixed label/callable identities do
not supply an exact local destination. Cache 177 restores pure helper tail
proofs across this protocol migration; no alternate source-name proof or
blanket call-preservation exception is introduced.
