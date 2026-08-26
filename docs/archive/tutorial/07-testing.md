# 7. Tests, errors, and tooling

Every file directly under `tests/` is a fresh executable. Tests call the same
local dependency as the real application:

```glorious
main() -> () {
    let source = "+++++[>++++++++<-]>++.";
    let parsed = brainfuck_core::parse(
        Bytes::iter(&String::as_bytes(&source))
    );
    assert(parsed is Result::Ok(_));

    let output = brainfuck_core::run_with_io(
        &parsed.0,
        Bytes::iter(&String::as_bytes(&""))
    );
    assert(output is Result::Ok(_))
}
```

`is Result::Ok(_)` refines the enum variant. The subsequent `.0` projection is
therefore checked, rather than an unchecked unwrap.

The suite covers comments, nested loops, unmatched brackets, pointer
underflow, deterministic input/output, Unicode `String::chars` iteration, a
transfer loop, and classic Hello World.

Run the gates from `tutorial/brainfuck`:

```console
grand fmt
grand check
grand test
grand run -- samples/hello.bf
```

The formatter is fail-closed: it parses, formats, reparses, and checks token
equivalence before writing. Compiler diagnostics include source spans; the
application converts domain errors to stable user-facing messages only at the
outer boundary.

The individual test executables are under `tutorial/brainfuck/tests` in the
checkout. Each is a small standalone example built around the pattern above.
