# Source-owned hierarchical budgets

`kernel::operation::budget` implements a bounded, request-owned budget pool as
ordinary Glorious source. It builds on the existing generational storage arena;
it has no native budget callback. The caller supplies the pool's database/owner
namespace, as with the other kernel stores, and must not reuse that namespace
for another simultaneously live owner.

Budget handles are duplicable identities, not copies of counters. Immutable
parent links form a forest. A child keeps its parent live, and retirement checks
children, outstanding charges, and reservation records. Retired handles remain
stale after slot reuse. This storage model allows a suspended provider to retain
IDs without retaining a unique pool or database borrow.

## Accounting and cleanup

An acquisition builds a checked ancestor path and charges the actual request
controls for each inspected node. It then validates ceilings in root-to-leaf
order, matching the Rust `Budget` reference's error precedence. Only after the
whole path and any required lease-record capacity are admitted are counters
changed. Failure leaves budget counters unchanged; the work spent checking the
path is not refunded. Overflow is rejected using subtraction from the remaining
ceiling rather than a wrapping prospective total.

Direct charges and leases are distinct. A direct release cannot consume a
child's charge or a lease's reservation. A lease has an affine public token and
a pool-owned reservation record. Explicit release validates its store identity
and generation, releases its ancestors, and clears the token only on success.
Foreign-pool rejection preserves the original token. Zero-sized leases still
retain their budget until released.

The request owner must drive `close_step` to completion on every session exit.
Closing blocks new budgets and acquisitions and scans one lease slot per step,
releasing at most one ancestor chain. It also reclaims temporary reservations
whose public tokens were discarded. Explicitly retained leases stay charged;
their product owner must keep the pool alive and release them after disposal.
The scan remains usable after cancellation or work exhaustion, and repeated
calls do not restart it. Closing does not refund direct cumulative work charges.
Dropping the pool releases its self-contained storage; this is not a destructor
that mutates an external database.

`grow_lease` validates the existing lease and checks its ancestor path before
changing any counters. It does not consume another reservation slot. Retention
is idempotent, including for zero-sized leases, and explicit release remains
available after close. `retained_reservations` distinguishes the retained owner
count from all live reservation records. The new retained-lease history checks
growth, full ancestor-first resource errors, foreign ownership, cancellation,
temporary close reclamation, retained counters, and final retirement in result
groups `[21, 20]`. The initial registry integration is described below.

## Evidence and remaining integration

The source tests execute a three-level/sibling history against Rust `Budget`,
including complete resource-error fields; a 22-check lease/retirement history;
and a 28-check overflow, work-exhaustion, abandoned-token, and close history.
They compile the complete production source closure and independently verify
the serialized bytecode before execution. The existing four Rust operation
tests remain reference evidence, not source API parity.

The expanded unfiltered source gate passes all 51 tests in 291.53 seconds
(`target/compiler-check/run-n4lywn96/report.json`), with 53 execution records,
the existing 12 workers and resource limits, and `release_ready: false`.

## Registry request integration

Every admitted registry request now owns one private pool: a shared memory root
and the two current source/line-index family budgets. `open_with_resources`
accepts family ceilings and a reservation-record ceiling; ordinary `open` uses
the request memory ceiling for both families and the memo limit for reservation
records, since product leases outlive active attempts. The registry issues monotonically distinct pool
owners, rejects owner exhaustion, and does not reuse an owner after failed
admission. Public reservation tokens also retain the checked session handle.

`reserve` charges the engine's actual request-memory counter before admitting
the phase lease. A phase, capacity, or work failure rolls back that memory
reservation without refunding work. Explicit release and the request close
scan decrement that same counter, even after cancellation. Root failures retain
precedence over phase failures. `resource_stats` reports the pool's outstanding
reservations; `memory_spent` reports the actual request counter, including any
other trusted-driver charges. These quantities coincide in the new fixture,
which checks them after rejection, release, and each close step.

Request close first drains provider drivers, then reclaims temporary reservation records,
and only then releases the database session/revision pin. The registry's normal
collection safe-point checks apply to reserve/release/inspection. Rejected
foreign, stale, or already-released tokens cannot mutate another request's
counters. Reservation bookkeeping is not a semantic query dependency.

`tests/registry/resources.glorious` executes real cold and memoized line-index
queries across two requests, along with phase/root limits, shared-counter
rollback, lease-record exhaustion, cancellation, dropped and zero-sized tokens,
collection exclusion, close-time pin retention, session-slot reuse, and
work-exhaustion rollback. Its current four result groups are `[3, 41, 27, 28]`; the
native harness checks each group separately after independently verifying the
serialized program. The full first request now also rejects automatic source
allocation without disturbing its manual reservations. A separate request
produces the actual source/index buffers and retains their 20-byte charge over
memo hits. The original manual ceilings and reservation-record limit are unchanged.

The earlier manual-reservation fixture (`[3, 38, 27, 28]`) passed in the full
52-test source gate in 297.35 seconds
(`target/compiler-check/run-5o47hyfl/report.json`), with 54 execution records,
unchanged limits/workers, and `release_ready: false`.

This does not complete M1 or the public operation API. The initial provider
integration below covers only selected backing allocations. In particular,
caller-declared reservations are not a census of
Vec capacities, arena backing storage, or physical VM allocations. Host
cancellation polling and physical memory accounting remain open. Acquisition
and cleanup in the generic pool currently traverse an ancestor
chain synchronously; they are not certified constant-time scheduler quanta.
The synchronous commit pass has no provider callbacks or yields, but transport
polling and deep-hierarchy latency still need executable certification. No
public contract inventory entry is marked complete by these tests.

## Retained product charges

The generic database now owns explicit product-memory reservations independently
of the request-owned phase pool. A trusted producer calls
`reserve_product_memory` while its attempt is computing, before materializing
the value. Growth uses the actual request's shared memory ceiling; ordinary
temporary releases cannot consume the retained portion. Zero-sized reservations
still allocate an ownership record. Failed admission does not change the charge.

The attempt owns the reservation until publication. Successful publication
transfers it to the database's product record before delivery; parent reuse adds
an owner of that same record without charging another request. Abort reclaims a
pending reservation even after cancellation. On rejected publication the staged
value is destroyed before the attempt's charge is refunded.

While the producing request is open, its actual controls remain authoritative.
Closing moves the retained counter into a separate generational owner, without
keeping the request, packages, revision pin, or session slot alive. The retained
owner preserves cumulative work and only the retained memory charge. The final
memo owner produces an opaque release token carrying the value and reservation.
Acknowledgment checks database/product identity, destroys the value, then refunds
the charge. A foreign acknowledgment changes neither value nor charge; retry
after success is closed. The last reservation removes its counter owner.

`tests/engine/product_memory.glorious` compiles and executes four independent
result groups, `[54, 22, 21, 25]`: cross-request/parent lifetime and final disposal,
cancelled pending-attempt cleanup, rejected recovered-product publication, and
deferred staged-publication cleanup.
They include growth, zero-sized admission, phase rejection, complete root-limit
fields, overflow, protection against temporary refunds, session reuse, foreign
acknowledgments, and preserved work. The original unreserved product-release
history remains a separate compatibility regression.

The trusted typed-store registry now uses `database::publish_staged`: failure
drops the database wrapper but leaves the attempt charged until the registry
has removed its concrete source/index value and aborts. Normal `publish` owns
its value directly and still aborts on publication failure. Driver cleanup
also clears a suspended line builder before aborting its attempt. These orderings
are prerequisites for attaching automatic allocation reservations to providers.

The preceding full unfiltered source gate passed all 53 tests in 317.23 seconds
(`target/compiler-check/run-z_95s4k3/report.json`), with 55 execution records,
the existing 12 workers and resource limits, and `release_ready: false`.

After phase retention and deferred typed-store publication, the full unfiltered
gate passes all 54 tests in 318.64 seconds
(`target/compiler-check/run-all572xe/report.json`), with 56 execution records
and the same workers, guards, and `release_ready: false`.

The generic fixture uses declared logical charges: its three-byte payload charge
is not a measurement of Vec capacity or VM backing allocations. That fixture
alone does not complete physical accounting or M1/M2.

## Initial provider backing-storage integration

Source copies and line-index builders now acquire shared-root and family-phase
reservations before allocating their backing buffers. `Vec::initial_capacity`
and `Vec::reserved_capacity` use the same capacity policy as `Vec::grow`, including
zero-sized types. A source copy reserves its destination byte capacity; a line
builder reserves its initial u32 capacity and each actual growth delta. This
does not precharge a guessed maximum number of lines.

Shared-root admission precedes phase admission. A rejected new phase lease
discards the pending root reservation; rejected growth shrinks only the newly
admitted delta. Existing builder memory and spent work remain intact. Staged
dependency observations, like staged publication, defer abort until the
provider has destroyed any owned value.

Phase pools live in a generational owner arena bounded by active sessions plus
memo capacity. A request references its pool; typed product stores own retained
phase leases. Closing reclaims temporary leases and removes the request/pin,
while a pool with retained products remains independently owned. Final collection
destroys the concrete value, releases its phase lease, and then acknowledges
the shared-root release. Empty closed phase and root owners are reclaimed.

`ownership_stats` reports these owner/lease counts; authenticated
`product_resources` reports the original producer's phase counters, even when
the inspecting request has a zero memory ceiling. Neither is a semantic read.
The new provider history covers growth, zero-memory memo hits and parent reuse,
producer close, final disposal, root/phase errors, reservation-record exhaustion,
and cancellation with a live builder. It also retains and disposes a zero-byte
source product under a zero memory ceiling. Its seven independent result groups
are `[77, 30, 30, 30, 30, 23, 27]`. It inspects counters between scheduler steps
so failed growth cannot leave an excess charge until later cleanup.

Seven focused standard-library vector/destruction tests pass, including a new
18-check capacity-preflight history for empty, minimum, doubled, exact-required,
u32, and zero-sized storage. Existing destruction and allocation-lifetime guards
remain unchanged.

The full unfiltered source gate passes all 55 tests in 343.49 seconds
(`target/compiler-check/run-9hgug8g_/report.json`), with 57 execution records,
the existing 12 workers and resource guards, and `release_ready: false`.

This accounting covers retained copied-text and line-start backing capacities,
not allocator peak/transient behavior, world inputs, arena/lease metadata,
fingerprint buffers, call frames, or the full VM/native allocation census.
Transport polling, complete physical accounting, and remaining compiler-family
providers are still open.

## Resumable source materialization

The registry now retains an affine source-copy builder between scheduler steps.
It reserves the destination capacity and prepays `length + 1` byte work once,
then copies at most 4 KiB per step. Chunk ends retreat at most three bytes to a
UTF-8 boundary; appending validated string slices does not revalidate the whole
destination. Every continuation checks the actual request controls and the
pinned blob's stamp. Small copies finish in the initial materialization step.

Cancellation, source mismatch, and premature completion destroy partial buffers;
driver cleanup removes the copy builder before refunding phase/root reservations.
Only a finished blob enters publication. Capacity allocation remains synchronous,
and these byte bounds do not certify transport polling or a 50 ms latency bound.

The new five-part source history returns `[17, 8, 7, 7, 28]`: exact copy and
one-shot completion, cancellation, source mismatch, premature completion, and
registry cancellation/close. Its 8,225-byte input places four-byte code points
across chunk boundaries, producing cursors 4,095, 8,190, and 8,225. It checks
unchanged prepaid work and zero remaining owners/reservations after cleanup.
The focused history passes in 105.32 seconds. The full unfiltered gate passes
all 56 tests in 350.38 seconds (`target/compiler-check/run-93dk84z7/report.json`),
with 58 execution records, the existing 12 workers and resource guards, and
`release_ready: false`.
