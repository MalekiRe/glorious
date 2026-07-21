# Compiler changes the tooling wants

`tooling/grand` (the build tool) drives the compiler strictly as-is: an
executable invoked `grc <input.gr> <output.ll>`, one input file, diagnostics as
rendered text on stderr, nonzero exit on failure. Everything below is what the
compiler should grow *later* — none of it blocks the build tool, and each item
lists the workaround grand uses today so the seams are easy to find (grep for
the item number in `tooling/grand/src/`). Ordered roughly by value.

**Status: the contract for items 1–5 and 7 is now concrete and fully mocked.**
`tooling/grand/src/contract.rs` is the normative spec (capabilities probe,
CLI shapes, JSON schemas); grand already implements both sides of every
capability with graceful legacy fallback, verified by
`tooling/grand/tests/contract.rs` against a bash mock of the future `grc`
(real subprocess protocol) and the in-process fake
(`GRAND_COMPILER=fake` + `GRAND_FAKE_CAPS=multi-file,check,diagnostics,interfaces,std`).
Implementing an item in the real compiler means: answer `--capabilities`
truthfully and match the contract; grand lights the path up automatically —
no grand changes needed. The probe contract:

```
$ grc --capabilities
{"grc":"0.1.0","contract":1,"multi-file":true,"phases":["check"],
 "emit":["interfaces-json","std-interfaces-json"],"diagnostics-json":true}
$ grc --diagnostics json [--phase check] [-o OUT] SOURCE...   # diagnostics: stderr, one JSON object/line
$ grc --emit interfaces-json SOURCE...                        # stdout: JSON array of declarations
$ grc --emit std-interfaces-json                              # stdout: prelude declarations
```

1. **Multiple source inputs + a segment table.**
   `grc SOURCE... -o OUT` concatenating in argument order (the architecture.md
   §7 contract), with diagnostics reporting original file/line via a segment
   map. *Today:* grand concatenates everything into
   `target/grand/<stem>.gr` itself and writes `<stem>.map.json` beside it;
   compiler diagnostics point into the bundle and the user (or grand's failure
   hint) maps lines back by hand. This is the single highest-value change:
   it deletes the worst UX wart in `grand build`.

2. **`--emit diagnostics-json`.**
   One JSON object per diagnostic: code, severity, title, labels as
   `{file, start_byte, end_byte, line, col, message}`, note, help. With (1) it
   makes grand's error output precise; it is also the entire substrate of LSP
   phase 1 (see docs/tooling-plan.md §1.2). *Today:* stderr passes through
   verbatim.

3. **Check-only mode (`--phase check`).**
   Stop after the frontend, emit nothing. *Today:* `grand check` compiles all
   the way to `.ll` and discards it — correct but wasteful, and it means check
   latency includes codegen.

4. **`--emit interfaces-json`.**
   Declaration-scan products (callables + signatures, types, effects,
   fixities, spans, doc comments) without body elaboration. Powers grand's
   cross-package name-collision preflight (flat namespace!) and LSP phase 2.
   *Today:* collisions surface as confusing duplicate-definition errors from
   deep inside the compiler.

5. **A real `grc` binary with `--version`.**
   Today `compiler/grc` is a bash wrapper over `cargo run -p grandiose`, so
   the first compile silently pays a cargo build, and grand cannot check the
   toolchain version against `[backend] minimum-version`. Ship the bootstrap
   as a built binary (and keep the `<input> <output>` CLI stable or version
   it). *Today:* grand discovers `GRAND_COMPILER` env → `compiler/grc` upward
   from the project → `grc` on PATH, and does no version checking.

6. **Comment syntax, lexed as trivia.**
   Line + nested block comments per docs/frontend-design.md. Prerequisite for
   the formatter and for doc comments in (4); the batch compiler only needs to
   skip them. *Today:* source with comments simply doesn't lex.

7. **Distributed std-lib manifest.**
   The bootstrap embeds `distributed_std.gr` invisibly. Tooling needs to know
   which names are implicit (collision checks, LSP hover/completion, and the
   eventual `std-lib.glorious` prepend contract). A `--emit std-interfaces` or
   a shipped interface file both work. *Today:* grand is unaware of the
   prelude; a user package colliding with it gets a raw compiler error.

8. **Object/executable emission.**
   Long-term the compiler (or a driver library it exposes) should own
   `-O` levels and native emission. *Today:* grand shells `llvm-as` + `lli
   --dlopen=<runtime.so>` (interp target) or `clang <ll> native_entry.c`
   (native target) — see `tooling/grand/src/target.rs`; the `Target` enum is
   the seam where a compiler-owned backend (or the VM, if it returns) slots in.

9. **Session mode (`grc --serve`).**
   Long-lived process holding post-scan state, per-body re-elaboration,
   span→type/def side tables. This is LSP phase 3; full design and rationale
   in docs/tooling-plan.md §4.4. Nothing in grand depends on it.

While none of this exists, `GRAND_COMPILER=fake` makes grand emit a trivial
exit-0 module instead of compiling, which is how grand's own test suite runs
without a working compiler or LLVM toolchain (`tooling/grand/tests/e2e.rs`).
