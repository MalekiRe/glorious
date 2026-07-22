# 4. Effects and deterministic I/O

Execution should not know whether bytes came from a terminal, a file, or a
test. The library declares that capability as an effect:

```glorious
effect BrainIo {
    [1,1] read() -> u8;
    [1,1] write(value: u8) -> ();
}
```

An effect operation describes a request. `[1,1]` says its continuation must be
resumed exactly once. The handler captures uniquely owned input and output state;
operations expose only the values the interpreter needs.

The interpreter performs requests:

```glorious
let value = perform BrainIo::read();
set_current(tape, move value);
perform BrainIo::write(current(&*tape));
```

`run_with_io` installs the deterministic handler:

```glorious
handle { execute_sequence(/* borrowed state */) } {
    BrainIo::read() with continuation =>
        resume(move continuation, read_byte(&mut input)),
    BrainIo::write(byte) with continuation => {
        Vec::push(&mut output, move byte);
        resume(move continuation, ())
    }
}
```

The captured `input` and `output` are uniquely borrowed only inside their
clauses. Each clause consumes its continuation with `move` and resumes once. Reading
past the supplied input yields zero. Tests therefore need no global stdin or
stdout: source plus input deterministically produces a `Vec<u8>`.

The executable uses a separate set of standard host effects—`ProcessArgs`,
`FileRead`, and `Diagnostic`. Keeping host I/O at the outer boundary makes the
core handler reusable.
