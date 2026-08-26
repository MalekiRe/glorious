# 5. Library-defined control flow and execution

Grandiose's familiar control syntax is built from ordinary declarations. In
the standard library, `if` accepts a `Result`. Exactly,
`type Bool = Option<()>`, and `Option` is Result-backed. The infix `else` lazily
receives its right-hand block:

```glorious
infixr 1 else;

effect __ResultCase<A, E> { inspect(value: Result<A, E>) -> !; }

if<A, E, B, F>(condition: Result<A, E>, body: F) -> Result<B, E>
    where F: Fn<(), Output=B>, A: Use<[0,0]> {
    handle perform __ResultCase<A, E>::inspect(condition) {
        __ResultCase::inspect(Result::Ok(_)) => Result::Ok(body()),
        __ResultCase::inspect(Result::Err(error)) => Result::Err(error)
    }
}
```

`infixr 1 else;` gives `else` low precedence and right associativity. A source
form such as `if(condition) { yes() } else { no() }` groups as one expression. The
blocks are anonymous zero-argument callables, so only the selected block runs.
The `Use<[0,0]>` bound says the successful condition payload must be
destructible without use.

The parser also defines a small domain operator:

```glorious
infixl 20 represents;

pub represents(byte: u8, command: u8) -> Bool {
    move byte == move command
}

if(byte represents 93) { /* closing bracket */ } else { /* continue */ }
```

Fixity affects grouping, not implementation: `represents` is still an ordinary
two-argument function.

Execution walks the flat instruction vector recursively. At `LoopStart(span)`,
a zero cell advances past the matching `LoopEnd`; otherwise `execute_loop`
recursively runs the body until the cell becomes zero. Encountering `LoopEnd`
returns to that recursive caller. Shared borrows keep the program alive while
unique borrows mutate only the tape, input iterator, and output.

In the checkout, the complete `execute_sequence` implementation is in
`tutorial/brainfuck/library/src/lib.glorious`. Trace the three cases described
above on paper: a simple instruction, a skipped loop, and a repeated loop.
