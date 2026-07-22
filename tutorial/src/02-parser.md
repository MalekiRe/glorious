# 2. Parsing bytes into a checked instruction stream

Brainfuck has eight command bytes; every other byte is a comment. An enum gives
those commands names. Recursive descent preserves bracket nesting while loops
are stored as matched flat markers, avoiding a recursive storage cycle.

```glorious
pub enum Instruction {
    MoveRight,
    MoveLeft,
    Increment,
    Decrement,
    Output,
    Input,
    LoopStart(usize),
    LoopEnd
}

pub struct Program {
    private instructions: Vec<Instruction>,
    private length: usize
}
```

The `usize` on `LoopStart` is the number of instructions to skip when the
current cell is zero. The stored length lets dependency code avoid rediscovering
vector metadata during recursion. `Program.instructions` is private: execution can borrow it
through `program_instructions`, but application code cannot forge malformed
markers.

Parsing owns a `BytesIter` and advances it recursively:

```glorious
struct Parser {
    private bytes: BytesIter,
    private offset: usize
}

pub parse(bytes: BytesIter) -> Result<Program, ParseError> {
    let parser = Parser { bytes: move bytes, offset: 0 };
    handle perform SequenceCase::inspect(parse_sequence(&mut parser, false)) {
        SequenceCase::inspect(Result::Err(error)) => Result::Err(error),
        SequenceCase::inspect(Result::Ok(sequence)) => {
            let Sequence { instructions, closed: _ } = move sequence;
            Result::Ok(Program { instructions: move instructions })
        }
    }
}
```

`move bytes` transfers the iterator into `Parser`; there is no second live
owner. `parse_sequence` calls itself after every token and once more for a `[`
body. It returns `Result::Err` for an unmatched `]` or an unfinished loop, so
invalid input remains ordinary typed data rather than a trap.

When a nested body is complete, the parser flattens it:

```glorious
let span = Vec::len(&body) + 1;
Vec::push(&mut instructions, Instruction::LoopStart(move span));
Vec::append(&mut instructions, move body);
Vec::push(&mut instructions, Instruction::LoopEnd);
```

`&body` is a shared borrow used only to compute length. `move body` then
transfers the vector into `append`; using `body` afterward would be rejected.

The complete parser is in
`tutorial/brainfuck/library/src/lib.glorious`; this chapter has shown the
representation, ownership transfer, recursive step, and loop-flattening core.
