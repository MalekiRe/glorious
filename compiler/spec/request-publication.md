# Combined request publication

The database now owns its public dependency ledger inside the non-generic
engine. A request claims one execution, derives revision/parent from its admitted
session, and obtains its diagnostic fingerprint from the actual snapshot pin.
Independent package/body, dependency-node/edge, and diagnostic/provenance limits
are supplied at claim time. All components charge the stored request controls.

`stage_request` transfers an affine payload into an opaque session-qualified
adapter. There is no payload accessor before `finish_request`; changing the
payload type does not duplicate the publication state machine. Closing or
cancelling the owning session invalidates its authority, including after slot
reuse. Callers must explicitly close/cancel abandoned sessions; dropping the
local payload adapter does not perform an effectful database rollback.

Preparation rejects active query attempts, freezes new query admission, checks
every demanded package, canonicalizes diagnostics, and builds the dependency
row. Diagnostic length observations are resolved internally against the pinned
world, not supplied by providers. Error diagnostics reject successful outcome
publication and are returned as an owned canonical failure batch. Warnings and
notes remain part of the successful outcome. Service-specific recovery/result
variants and failure mapping still require their concrete service adapters.

The final package permission holds a unique registry loan. Parent-version and
capacity checks, row construction, and allocation of a missing dependency
directory slot happen before the final cancellation check. The slot is resolved
before that check; afterwards only existing-row assignment, version assignment,
the permitted package-phase transition, and returning the owned result remain.
There is no yield between these operations. A cancelled or rejected replacement
does not remove the previously published row. Temporary empty directory slots
are neither externally observable nor retained on a returning failure.

Request abort drops unpublished diagnostics/rows and rolls back package staging.
It does not undo independently committed query memos. Revision collection drops
the public dependency row only after history proves that the retired revision
has no pins. A retained child row does not strongly retain its parent revision.

## Verification and remaining work

All three new integrated source histories pass (209.94 seconds). They cover owned
outcomes, canonical warning batches and fingerprint binding, late cancellation
of a replacement, immediate-parent reuse, pin-aware retirement, unstaged package
rejection, invalid related spans despite a newer accepting world, shared work
exhaustion, active-query rejection, stale parent replacement, frozen query
admission, and stale staged tokens after session-slot reuse. Programs are
independently decoded/verified before execution. The temporary lowering trace
was removed and the original authoring MIR source hash restored before this run.
The expanded 34-test kernel suite also passes, including 36 recorded program
executions, in 454.81 seconds. Evidence:
`target/compiler-check/run-3bgy4_c2/report.json`, source-lock SHA-256
`8fc2563c37f1cc5a97d45bd6222763c7c31e45f14112a134f0357486b8faac22`.
This is the publication closure before the subsequent typed-store reclamation
work, not a claim that later edits inherit those results.

This is the shared publication mechanism, not `CompilationOutcome` API parity.
The payload in these tests is synthetic; real package AST/Core/MIR products,
artifacts/manifests, the concrete normalized world, closed provider capabilities,
and compiler/service providers remain open. Counts are not hierarchical memory
leases. VM aggregate copies, directory growth, and old-row release still need
physical cost certification; a logically non-failing slot swap is not proof of
bounded runtime allocation or crash-safe external artifact publication.
