# Request-owned package staging

The non-generic package registry lives inside the query engine's authenticated
request entry. The database facade checks package membership through the
request's pinned immutable world. The temporary generic world adapter has a
`PackageWorld` membership trait; it cannot substitute an ambient mutable world
or a caller-supplied membership boolean. A concrete normalized compiler world
and its exact root/source membership remain part of the source-provider work.

Package/body operations charge the same stored controls as query evaluation.
Cancellation rolls back all unfinished package metadata; cleanup and inspection
remain usable after cancellation and do not refund spent work. A previously
pinned request survives revision retirement. Closing the session drops its
registry and releases its snapshot through the existing database close path.

Body scratch authority is an opaque session-qualified, nonreused ordinal.
Publishing or abandoning a consumed body fails. A token from another session,
including an old generation of a reused session slot, cannot discharge a live
body. Package staging rejects active scratch. Local package rollback makes
that package terminal and prevents opening further packages; enclosing request
rollback clears every unfinished package. Already committed metadata survives
subsequent cleanup.

Preparation freezes mutation and checks one package per step. If any package
is unstaged, the stepper constructs the complete canonical list of offending
package keys before returning the lifecycle failure. It never commits a prefix
of the package set. The low-level commit primitive checks cancellation and
changes a single request phase, so all prepared package metadata becomes
committed together and scratch counts become zero.

## Still open

- The database deliberately exposes **no package-only commit**. The combined
  request publisher now holds a unique package permission across the final
  ledger commit and rejects outstanding query attempts. Its three integrated
  histories pass; see [request-publication.md](request-publication.md).
- The registry currently owns lifecycle metadata, not AST/Core/MIR scratch or
  the final package products. Those owners and their rollback must be attached
  when the compiler providers are implemented; zero counters do not prove
  physical reclamation of not-yet-implemented products.
- Low-level unclaimed sessions derive package/body ceilings from the engine's
  read ceiling. Claiming a request sets independent limits before any package
  is opened. Hierarchical memory leases remain open. Body capacity bounds all
  ordinals issued by that request, not just concurrently live bodies. Revoked
  token metadata remains bounded by that ceiling until request cleanup.
- Full canonical metadata enumeration, exact service failure mapping, and
  compiler-scale cancellation/retention evidence
  remain outstanding. Metadata can presently be inspected by exact package key.
- Missing-package ordering uses explicitly stepped insertion sort. Its worst
  case is quadratic; physical string hashing/copying/release costs are not
  constant-time merely because validation has a cursor.

The source fixtures exercise lifecycle and database histories, not compilation
or the final request-wide publication boundary. Their assertions use small
typed predicate helpers: C0 does not lower every completion-handler expression
inside a let initializer or a call argument, including some implicit scalar
boolean-to-library-`Bool` coercions. The checks and failure distinctions remain
the same; this is not a new compiler primitive or a backend relaxation.
