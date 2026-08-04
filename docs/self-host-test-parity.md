# Self-host test parity gate

The self-hosted compiler is not considered test-compatible with the Rust bootstrap compiler merely because it compiles the production source or reaches a bytecode fixed point. It must also reproduce the accepted behavior and rejection diagnostics exercised by every bootstrap integration-test suite.

`crates/grandiose/tests/self_host_parity.tsv` is the checked-in inventory. Every top-level Rust file in `crates/grandiose/tests` has exactly one semantic family and one status:

- `unported`: there is no self-host oracle comparison for the suite yet;
- `partial`: useful infrastructure or some cases exist, but the suite's behavior is not fully covered;
- `covered`: one or more named `#[test]` functions execute a Rust-oracle/self-host comparison for the suite.

`parity_manifest_is_complete_and_truthful` derives the integration-suite list from the filesystem. It fails when a suite is added or removed without updating the inventory, when a family or status is invalid, or when a covered entry links to a missing executable self-host test. The gate deliberately does not infer coverage from similar filenames or compiler progress.

The eight existing self-host layers—lexer, scanner, headers, interfaces, body grouping, name resolution, typed Core, and bytecode—are linked explicitly. Other suites remain `unported` until their positive cases and rejection behavior are compared. Move a suite through `partial` to `covered` only after adding a focused self-host parity test and linking its exact test function in the manifest.

`tests/support/parity.rs` supplies deterministic recursive corpus discovery and a shared outcome comparison that represents accepted output bytes and stable rejection codes. Future parity tests should use those helpers where practical, retain focused fixtures for failures, and avoid accepting looser diagnostics than the bootstrap suite.
