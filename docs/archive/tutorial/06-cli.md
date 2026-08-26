# 6. The command-line boundary

The application accepts a Brainfuck file and optional literal input:

```console
grand run -- samples/cat.bf "Grandiose"
```

The tutorial manifest grants only the host authority used by this command:

```toml
[runtime]
capabilities = ["process.args", "fs.read", "fs.write", "diagnostic"]
```

These are the exact grants required by the current compiled artifact. The
tutorial source reads arguments and the named Brainfuck file, then writes its
output through the diagnostic channel. It does not write files; `fs.write` is
present because the current whole-standard-library image retains that host
import until dead host-import pruning runs.

Its effect row states exactly which host capabilities it needs:

```glorious
application() -> () / {ProcessArgs, FileRead, Diagnostic} {
    let arguments = process_args();
    // Validate arguments, read source, parse, execute, and report output.
}

main() -> () { run_compiler_host(application) }
```

`/ { ... }` is part of the callable type. `run_compiler_host` installs the
standard handlers and closes that row before the VM enters `main`.

The boundary adapts host `Bytes` into an owned iterator, then handles the parse
result before execution:

```glorious
let source = read_file(move path);
handle perform ParseCase::inspect(
    brainfuck_core::parse(Bytes::iter(&source))
) {
    ParseCase::inspect(Result::Err(error)) =>
        write_diagnostic(brainfuck_core::parse_error_message(move error)),
    ParseCase::inspect(Result::Ok(program)) => {
        perform RunCase::inspect(brainfuck_core::run_with_io(
            &program,
            Bytes::iter(&String::as_bytes(&input))
        ));
        ()
    }
}
```

The parse handler passes `program` directly from the `Ok` pattern; no unchecked
unwrap is involved. A nested run handler converts successful output to `Bytes`
and then UTF-8 for display. The
current host surface has no stdout capability, so visible output uses
`write_diagnostic`; binary output remains a byte vector inside the interpreter.

The full boundary is in `tutorial/brainfuck/src/main.glorious`; the excerpt
above contains the important capability, effect-row, and result-handling shape.
