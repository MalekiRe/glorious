# Mirrored compiler modules

Each completed source file here is named `<stage0-module>.glorious` and owns
the public facade listed in `docs/self-host-stage0/module-ledger.tsv`. Shared
implementation kernels may live under `src/internal/`, but no public module
may delegate semantics to Rust Stage0.
