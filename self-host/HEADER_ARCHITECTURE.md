# Semantic header architecture

This slice makes parsed declaration headers a semantic compiler representation
rather than a compact wire-oriented record format.

## Completed cutover

Header type syntax now has one source of truth:

```text
TypeNode
    tokens: TokenSpan
    kind: HeaderTypeKind
```

`HeaderTypeKind` owns the payload appropriate to each type form:

- path names;
- shared and unique reference lifetime/referent data;
- tuple elements;
- type-application constructor and arguments;
- the never type.

There is no stored numeric type tag beside the enum. `GenericParamKind`
similarly replaces the generic-parameter kind byte.

Nominal source order is now represented by one `Vec<NominalHeader>` instead of
parallel kind and index arrays. Each entry identifies both the declaration kind
and its arena ordinal, so the two facts cannot become misaligned.

All header token intervals use the frontend `TokenSpan` abstraction, all
contiguous header arena ranges use `IdRange`, and the parser uses the shared
`TokenCursor`. Header parsing no longer owns independent span, range, or cursor
storage types.

## Consumer boundary

The persistent representation is semantic even where an untouched consumer
still asks for a scalar projection. `header_kind` and `header_index` derive
their answers exhaustively from `NominalHeader`; no mirrored numeric arrays are
retained. `HeaderTypeView` likewise borrows the semantic type enum and exposes
only the data required by interface collection.

These projections are adapters, not a second representation. They can be
removed when the interface collector is migrated to consume `NominalHeader`
directly.

## Removed probe surface

The header module no longer owns filesystem/process applications or a custom
binary snapshot writer. The corresponding header-only and interface-only Rust
wire-probe test binaries were removed with that host surface. The production
compiler continues to exercise header parsing and interface collection through
the ordinary self-host pipeline.

This is intentional: phase-local executable protocols should not force the
compiler's semantic storage to retain numeric tags, parallel arrays, or
serialization-only accessors.

## Preserved semantic invariants

- Declaration and type token spans remain half-open.
- Declaration traversal remains in scanner source order.
- Callable ordinals remain aligned with callable arena allocation.
- Struct fields and enum variants remain contiguous arena ranges.
- Type paths, tuple elements, applications, references, and never types retain
  their existing parsing and diagnostic behavior.
- Header error codes and primary/related token identities remain available to
  the centralized diagnostic boundary.
- Bodies still receive the same fixity lookup facts.
- Resolution and elaboration still receive the same callable, nominal, field,
  variant, parameter, and type views.

## Next representation slice

The body parser still stores a universal numeric `ExprNode` with packed edges.
The next analogous cutover should replace it with a semantic `ExprKind` while
updating resolution and elaboration in the same change, so no numeric body
adapter becomes permanent.
