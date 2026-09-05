# Canonical dependency ledger

The source ledger is a kernel component owned by the combined request publisher.
Its traces preserve the Rust dependency ledger's public projection; they do
not replace query execution provenance or first-observation replay journals.

## Representation and validation

`Node` has the eight reference variants in their reference order. Digests
compare canonical bytes, not their little-endian storage words. Module keys
compare package then path; strings compare their bytes. Instance keys retain
the callable plus full canonical substitution bytes, ordered in that order;
their BLAKE3 fingerprint is not an ordering substitute. The fingerprint uses
the reference's domain-separated `Digest::of_parts` formula. Hash-table hashes
are internal indexing aids, never persisted semantic identities.

The ledger exposed a C0 materialization bug: otherwise-unused bodies demanded
executable trait-method instances absent from the entry-rooted instance graph.
Non-ledger fixtures failed with `G7032`, while the ledger fixtures selected the
methods and passed. The authoring service now checks these missing targets
against final executable reachability; see A11 in `authoring.md`. Digest and
node hashing retain their ordinary trait calls, with no additional intrinsic.

A transaction stages indexed facts and replaces repeated records of the same
node. Sealing sorts roots and edges, deduplicates edges, validates the graph,
and builds a private trace row. Every sorting/edge/DFS/comparison transition
is explicitly stepped and charges request work. DFS uses an owned stack;
graph depth does not become recursive evaluator depth. The test drivers have
their own finite polling fuel.

Missing evidence takes precedence over cycles, including in initial revisions.
For complete acyclic facts, green requires an equal fingerprint **and** equal
canonical dependency identities in the immediate parent's retained row. A
changed child does not by itself make an unchanged parent product red. Red
explanations propagate the first canonical changed edge, or name the product
itself when only its value/edge shape changes. Absent parent evidence is cold.

Published rows have nonreused versions. A transaction checks its captured
parent-row version on every step and at commit, so replacement or retirement
cannot mix parent histories. Errors discard staging; subsequent uncancelled
uses report a closed transaction. Directory allocation and capacity checks
precede the final cancellation check and existing-slot replacement of the
visible row. Trace references and slices borrow
the ledger owner; staging is not visible through those accessors.

## Integration requirements still open

- The database now derives revision and immediate parent from its pinned
  session and owns publication/retirement of public rows. Three integrated
  histories pass; see [request-publication.md](request-publication.md).
  Low-level `begin` still only validates database/ordinal shape, not admission.
- Instance argument validation/normalization and construction of canonical
  substitution bytes belong to the future typed term/instance subsystem.
  The ledger currently accepts that trusted stable identity projection; it is
  not a decoder or a complete `InstanceKey::new` API for untrusted arguments.
- Concrete provider capabilities must prevent access to low-level replacement
  controls and independent ledger commits; the generic database adapter keeps
  its owned ledger private and charges actual session controls.
- Add hierarchical memory leases and compiler-scale retention/cost evidence.
  Current limits bound logical nodes and raw staged edges, not physical bytes.
  Sorting is stepped insertion sort, with quadratic worst-case comparisons;
  array copying, hashing long keys, and final storage release are not certified
  constant-time merely because the traversal has explicit cursors.

The executable fixtures cover canonical keys, red/green value histories,
dependency-identity changes, sibling parent selection, cycles, missing facts,
cancellation, resource/capacity rejection, and parent replacement/retirement.
These are synthetic ledger histories, not compiler provider or bootstrap parity.
