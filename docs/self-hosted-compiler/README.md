# Self-hosted compiler design series

**Status:** incomplete proposal series  
**Current implementation status:** see [`../self-hosting.md`](../self-hosting.md)

This directory contains design work for a future trustworthy self-hosted
compiler. It does not describe the current Stage0 implementation unless a
document explicitly links a claim to current code or a checked ledger.

## Maintained entries

- [`00-snowflake-document-roadmap.md`](00-snowflake-document-roadmap.md) —
  intended 32-chapter structure.
- [`01-architecture-and-trust-boundaries.md`](01-architecture-and-trust-boundaries.md)
- [`02-compilation-inputs-revisions-and-session-ownership.md`](02-compilation-inputs-revisions-and-session-ownership.md)
- [`05-dependency-tracking-and-invalidation.md`](05-dependency-tracking-and-invalidation.md)
- [`stage0-semantic-test-map.md`](stage0-semantic-test-map.md) — generated
  inventory for the current Rust baseline, not a proposal chapter.
- [`00-snowflake-synopsis-compendium.md`](00-snowflake-synopsis-compendium.md) —
  concise index replacing the generated 1.4 MB compendium.

Chapters 03, 04, and 06–32 have not been split into maintained chapter files.
The roadmap therefore describes an intended corpus, not a completed one.

The original generated compendium remains available in Git history at baseline
`3fd2e0ddf3c10e2d558ad21190b975500374ed71`. The old Stage1 readiness report
is preserved under [`../archive/`](../archive/).
