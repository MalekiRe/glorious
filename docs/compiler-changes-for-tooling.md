# Compiler changes the tooling wants

`tooling/grand` now drives the versioned G1 compiler contract: ordered
`.glorious` inputs, JSON diagnostics, check-only compilation, `.grbc` output,
and execution through `grvm`. The numbered list records the completed compiler
surfaces on which the tooling depends.

**Status: items 1–9, per-body incremental inference, and compiler-owned local/type
side tables are real and integration-tested.**
`tooling/grand/src/contract.rs` is the normative spec (capabilities probe,
CLI shapes, JSON schemas); grand implements the contract directly, verified by
`tooling/grand/tests/contract.rs` against subprocess mocks of the versioned
compiler and VM protocols.
The real compiler answers `--capabilities` truthfully, and grand gates every
optional path on that response. The current probe contract is:

```
$ grc --capabilities
{"grc":"0.1.0","contract":1,"multi-file":true,"modules":true,
 "artifact-major":1,"artifact-minor":0,
 "seed-identity-version":1,
 "seed-identity":"grandiose-seed-v1;grc-contract=1;grvm-contract=1;artifact=1.0;features=000000000000013f",
 "phases":["lex","scan","resolve","check"],
 "emit":["bytecode","grbc","mir","core","provisional",
         "interfaces-json","std-interfaces-json"],"diagnostics-json":true,
 "serve":{"protocol":1,"transport":"json-lines",
          "max-request-bytes":1048576,"max-arguments":128,
          "max-inputs":64,"max-source-bytes":16777216}}
$ grc --diagnostics json [--phase check] [-o OUT] SOURCE...   # diagnostics: stderr, one JSON object/line
$ grc --emit interfaces-json SOURCE...                        # stdout: JSON array of declarations
$ grc --emit std-interfaces-json                              # stdout: prelude declarations
$ grvm --capabilities
{"grvm":"0.1.0","contract":1,"contract-min":1,"contract-max":1,
 "artifact-major":1,"artifact-minor-min":0,"artifact-minor-max":0,
 "seed-identity-version":1,
 "accepted-seed-identities":["grandiose-seed-v1;grc-contract=1;grvm-contract=1;artifact=1.0;features=000000000000013f"]}
```

`grc --serve` reads one JSON request per line. A compile request is
`{"protocol":1,"id":N,"method":"compile","arguments":[...]}`; its argument
array is exactly the one-shot compiler argument vector. Responses contain the
same protocol and ID, process-style `status`, captured `stdout`/`stderr`, a
monotonic last-good `generation`, `transaction` (`committed`, `unchanged`, or
`retained`), and the exact source-bundle fingerprint. `shutdown` is the only
other method. Protocol, request, argument, input-count, and aggregate source
limits are checked before compilation.

1. **Multiple source inputs, package roots, and a segment table.**
   `grc SOURCE... -o OUT` accepts an application root plus hermetic additional
   inputs; repeatable `--dependency NAME=PATH` marks separate dependency package
   roots. **Implemented:** `grc` discovers each root's declared module closure,
   validates the hybrid module layout, owns canonical bundle ordering, and maps
   every diagnostic back to its original file. Grand passes the application root
   and explicit dependency roots when the capability is present.

2. **`--diagnostics json`.**
   One JSON object per diagnostic: code, severity, title, labels as
   `{file, start_byte, end_byte, line, col, message}`, note, help. With (1) it
   makes grand's error output precise; it is also the substrate of LSP phase 1
   (see docs/tooling-plan.md §1.2). **Implemented for batch compilation.**

3. **Check-only mode (`--phase check`).**
   Stop after the checked compiler pipeline and emit nothing. **Implemented:**
   `grand check` uses this path and fingerprints successful checks. The real
   compiler also implements truthful earlier `lex`, declaration-`scan`, and
   interface/name/type `resolve` stop boundaries; none writes an artifact.
   `resolve` validates compiler interfaces without elaborating callable bodies,
   running ownership, constructing Core/MIR, or lowering bytecode. Grand
   capability-gates this distinct boundary rather than substituting `check`.

4. **`--emit interfaces-json`.**
   Declaration-scan products (callables + signatures, types, effects,
   fixities, spans, doc comments) without body elaboration. Powers grand's
   cross-package/module identity preflight and LSP navigation.
   **Implemented:** the real parser supplies ordered file/line/signature/doc
   metadata plus stable namespace-qualified identities and exact file-local
   declaration/name byte spans. The LSP consumes these directly, including module
   paths and explicitly marked dependency package roots.

5. **A real `grc` binary with `--version`.**
   **Implemented:** the native Rust bootstrap ships a real `grc` binary
   with `--version` and a contract version. Grand fingerprints its identity;
   compiler contract ranges and emitted artifact major/minor are rejected when
   incompatible. Grand probes the selected VM before compilation, rejects an
   incompatible VM contract or artifact range, and fingerprints the compiler
   and VM identities atomically using executable-content digests rather than
   mutable timestamps. The compiler advertises a deterministic released-seed
   identity derived from the compiler/VM contract revisions, artifact version,
   and supported artifact feature set. The VM advertises a sorted acceptance
   set. Grand requires matching protocol/identity metadata before consulting
   build freshness, includes it in the atomic toolchain fingerprint, and passes
   the selected identity to `grvm run` for a second check before artifact load.
   Missing or malformed metadata, version mismatch, and an unaccepted identity
   fail closed.

6. **Comment syntax, lexed as trivia.**
   Line + nested block comments per docs/frontend-design.md. Prerequisite for
   the formatter and for doc comments in (4). **Implemented:** the semantic
   lexer, shared gap-free lossless trivia stream, and declaration doc
   extraction all consume the same source bytes.

7. **Distributed std-lib manifest.**
   The bootstrap embeds `distributed_std.glorious` invisibly. Tooling needs to know
   which names are implicit (collision checks, LSP hover/completion, and the
   eventual `std-lib.glorious` prepend contract). A `--emit std-interfaces-json` or
   a shipped interface file both work. **Implemented:** `std-interfaces-json`
   reports only the trusted embedded-prelude segment and grand consumes it for
   collision preflight.

8. **Object/executable emission.**
   **The canonical G1 path is implemented:** grand forwards `-O` levels to the
   compiler, requires bytecode emission, and runs `.grbc` through `grvm`.

9. **Session mode (`grc --serve`).**
   **Implemented:** one long-lived process accepts repeated resolve,
   check, interface, and compile requests through the versioned JSON-line
   protocol above. Every request revalidates the complete ordered source bundle;
   successful snapshots commit atomically, failed requests retain the previous
   bounded last-good snapshot, and byte-identical requests are reported as
   unchanged. The session and one-shot paths call the same phase/output driver,
   so diagnostics and artifacts are identical. Oversized and malformed requests
   fail without poisoning the process, and process restart begins with empty
   state. Grand validates the advertised protocol but remains a batch client;
   spawning a session for one build would add no benefit. The Rust LSP maintains
   one `IncrementalCompilerSession` per workspace root. The session reuses unchanged
   body inference results when the declaration context fingerprint is unchanged and
   transactionally restores its cache after failure. Compiler-owned semantic side
   tables expose exact local definitions/references, scope ranges, inferred local
   types, and expression types. The LSP uses them for local hover, definition,
   references, rename, completion, and inferred-type inlay hints, while last-good
   snapshots fail closed across edited or shifted source.

Contract tests exercise bytecode selection and VM invocation through hermetic
subprocess protocol fixtures, while the real `grc`/`grvm` pair is used by the
repository integration gate.
