# Legacy tooling

`grand`, `grandfmt`, and `grand-lsp` depended on the removed pre-Stage0 Rust
compiler. They are intentionally disabled and must not be used or repaired by
adding compatibility dependencies.

They will be restructured as new clients of the current Stage0 compiler
architecture. Their source remains only as historical reference until that
replacement work begins.

The former `self-host/` implementation was also removed. A new self-hosted
compiler will be designed from the current bootstrapped architecture rather
than migrated from that source tree.
