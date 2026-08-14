# Dependency Tracking and Invalidation

The compiler records dependency facts as immutable products owned by the
`CompilerDatabase`. They are never process-global state and they never give a
request authority to observe another revision's input world.

## Product identities

Stage zero tracks these typed products:

- `Input(FileKey)` — supplied source bytes.
- `Interface(ModuleKey)` — the frozen public interface of one module.
- `Fixity(ModuleKey)` — source-defined operator environment.
- `Body(DefKey)` — parsed body syntax before semantic elaboration.
- `Core(DefKey)` — frozen, validated typed Core for one declaration.
- `Mir(DefKey)` — lowered MIR for one callable.
- `Artifact(PackageKey)` — a verified VM program.

The service records source-to-interface, interface-to-fixity,
source-to-body, body/interface/fixity-to-Core, Core-to-MIR, and reachable-MIR-to-artifact
edges while it runs the real semantic phases. Facts are staged with the
request's interface-cache transaction and publish only after the final
cancellation check accepts the outcome. Failed, cancelled, and
resource-limited requests publish neither cache products nor dependency facts.

## Red/green validation

For a child revision, each staged product is compared with the same typed
product in its immediate parent. A product is green when its fingerprint and
dependency shape are equal; it is red otherwise. This is value validation,
not blind transitive dirtiness: a changed source may require an interface to
be checked, but an equal public-interface fingerprint is green and does not
invalidate downstream clients. This permits private body edits to leave
interfaces and fixities reusable while changing only the Core/MIR/artifact
products whose values actually changed.

When a product is red, the trace names the first canonical changed input when
one is available. Missing parent facts are cold: the compiler recomputes
rather than relying on retention or a historical cache entry.

## Tooling contract

`StageZeroCompiler::dependency_trace` returns the fingerprint, direct typed
dependencies, and `Cold`, `Green`, or `Red { first_changed }` status for a
single published product. `dependency_traces` returns the complete ordered
revision ledger. Both APIs are inspection-only and return no result for an
unpublished or collected revision.

The ledger is pruned when its retired revision is safely collected. A child
whose parent has already been collected starts cold, preserving correctness
without making revision retention a semantic requirement.
