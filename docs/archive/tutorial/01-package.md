# 1. Packages, modules, and privacy

The runnable project is an application with a local library dependency. This is
useful structure, not ceremony: `grand test` builds every test file as a fresh
crate root, so both the executable and its tests import exactly the same checked
interpreter library.

```toml
[project]
name = "brainfuck-tutorial"
version = "0.1.0"
entry = "src/main.glorious"
sources = []

[dependencies]
brainfuck-core = { path = "library" }
```

Dependency names use kebab-case in the manifest and normalize to underscores in
source, so the application refers to this package as `brainfuck_core`.

The executable also contains a small inline module:

```glorious
pub mod cli {
    struct ArgumentsPolicy { private empty: String }

    pub usage() -> String {
        "usage: brainfuck-tutorial <program.bf> [input]"
    }
}
```

`pub mod cli { ... }` makes the module name visible, while declarations without
`pub` remain private to it. `ArgumentsPolicy` can therefore be constructed and
destructured only inside `cli`. The interpreter applies the same rule to parser
and tape state: callers receive useful operations, never representation access.
This matters for ownership because a value with private fields must be passed
back to code authorized to destructure and consume it.

Project layout:

```text
brainfuck/
├── grandiose.toml
├── library/
│   ├── grandiose.toml
│   └── src/lib.glorious
├── src/main.glorious
├── samples/
└── tests/
```

The complete application and library are in
`tutorial/brainfuck/src/main.glorious` and
`tutorial/brainfuck/library/src/lib.glorious`. The following chapters extract
and explain the important sections so the hosted book remains self-contained.
