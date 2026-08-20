# Retired self-host readiness report

Status: historical only.

This report described the removed `self-host/` compiler and its Stage0
bootstrap experiment. That source tree and the pre-Stage0 Rust compiler it
depended on were intentionally removed so that a new self-hosted compiler can
be designed from the current bootstrapped architecture.

The previous `check` and `emit` reproduction commands are no longer runnable
and must not be treated as release evidence. In particular, the former
Stage-1/2 convergence claim is retired with the source tree.

The active executable conformance evidence is the independent Rust Stage0
compiler and VM:

```bash
cargo test --workspace
```

Future self-host work must define a new canonical source closure, bootstrap
manifest, Stage1-to-Stage2 convergence procedure, and release-readiness report.
