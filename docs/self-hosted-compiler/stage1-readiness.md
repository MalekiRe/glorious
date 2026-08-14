# Stage-1 Readiness Report

Status: audited against the canonical self-host compiler source materialized by
the released `grc` seed.

## Reproduction

Run from a clean checkout with the released seed available at
`target/release/grc`:

```bash
CARGO_TARGET_DIR="$PWD/target" \
  tooling/self-host-stage0.sh check --seed "$PWD/target/release/grc"
```

This materializes the production compiler and its shipped standard-library
surface into one canonical source input, supplies the frozen host-capability
and runtime-leaf manifest, and drives Stage0 through headers, bodies, trait
selection, const/quantity checking, MIR, VM emission, and verification.

For the artifact boundary, run:

```bash
CARGO_TARGET_DIR="$PWD/target" \
  tooling/self-host-stage0.sh emit \
  --seed "$PWD/target/release/grc" \
  --artifact "$PWD/target/stage1.grbc" \
  --manifest "$PWD/target/stage1.manifest"
```

The harness independently re-verifies the serialized VM artifact, checks that
the bootstrap manifest binds it, and proves that a deliberately corrupted
adjacent manifest is rejected.

## Current result

The canonical `check` command succeeds with no Stage0 diagnostics. This closes
the source-level blocker inventory for the following domains in the shipped
program:

| Domain | Result |
| --- | --- |
| Modules and interfaces | accepted |
| Generic nominal layouts and direct-call materialization | accepted |
| Traits and associated projections | accepted |
| Structural `u32` consts and quantities | accepted |
| Typed Core and ownership validation | accepted |
| MIR lowering, VM emission, and verifier boundary | covered by the `emit` reproduction command |

## Remaining blockers

There are no Stage0 language-semantic diagnostics from the canonical shipped
source in `check` mode. A retained `emit` artifact and Stage-1/2 convergence
remain separate bootstrap evidence: execute the verified stage-one artifact
against the same canonical input and compare its stage-two product under the
bootstrap manifest contract. That work requires a stage-one host invocation;
it is not evidence that a Stage0 language feature is missing.
