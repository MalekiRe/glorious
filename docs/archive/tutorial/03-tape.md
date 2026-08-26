# 3. A private, bounded tape

The Brainfuck tape owns a vector and a cursor. Both fields are private, so all
state transitions preserve the invariant that at least one cell exists.

```glorious
struct Tape {
    private cells: Vec<u8>,
    private length: usize,
    private cursor: usize
}

new_tape() -> Tape {
    let cells = Vec::new();
    fill_cells(&mut cells, 256);
    Tape { cells: move cells, length: 256, cursor: 0 }
}
```

Mutation requires a unique borrow. The dereference on the left writes through
the reference returned by `Vec::index_mut`:

```glorious
set_current(tape: &mut Tape, value: u8) -> () {
    *Vec::index_mut(&mut tape.cells, tape.cursor) = move value;
    ()
}
```

The borrow cannot overlap another access to the same tape. The implementation
therefore reads the current cell first, computes a new value, and then calls
`set_current`.

Arithmetic is expressed with a trait and generic helpers:

```glorious
pub trait CellArithmetic {
    increment(self: Self) -> Self;
    decrement(self: Self) -> Self;
}

impl CellArithmetic for u8 {
    increment(self: u8) -> u8 { wrapping_add(move self, 1) }
    decrement(self: u8) -> u8 { wrapping_sub(move self, 1) }
}

increment_cell<T>(value: T) -> T where T: CellArithmetic {
    CellArithmetic::increment(move value)
}
```

The `where` clause is explicit evidence that `T` supports the operation.
Wrapping `u8` arithmetic gives conventional Brainfuck cell behavior. Moving
left from cell zero returns `PointerUnderflow`; moving beyond cell 255 returns
`PointerOverflow`. The deliberately small bound keeps the tutorial quick while
making both boundary errors testable.
