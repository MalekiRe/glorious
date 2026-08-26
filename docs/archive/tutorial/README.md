# A Brainfuck interpreter in Grandiose

This book builds a complete Brainfuck interpreter using only the language and
tooling implemented in this repository. The finished package lives in the
`tutorial/brainfuck` directory and is checked as part of the tutorial itself.

The implementation deliberately uses the language's interesting pieces rather
than hiding them behind host code: packages and modules, private representation,
enums, recursive parsing and execution, `Vec<T>`, `Bytes`, `String` iterators,
checked `Result` and `Option` values, unique borrows, generic trait dispatch,
custom fixity, library-defined control flow, and algebraic effects.

The result is recognizably Grandiose source rather than a host-language shim:

```glorious
if(byte represents 93) {
    Result::Ok(Sequence { instructions: Vec::new(), closed: true })
} else {
    parse_sequence(parser, nested)
}
```

Later chapters unpack the standard library's `if ... else` abstraction, the
project's `represents` infix function, and the ownership rules behind this
recursive call.

From `tutorial/brainfuck`, the intended workflow is:

```console
grand check
grand test
grand fmt --check
grand run -- samples/hello.bf
```

`grand run` executes compiled G1 bytecode through `grvm`; it does not invoke the
compiler's internal recovery evaluator.
