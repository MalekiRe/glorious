# Grandiose for Zed

This extension associates `*.glorious` files with Grandiose and starts
`grand-lsp` over stdio. Its real Tree-sitter grammar lives at the repository
root; it is not a Rust grammar alias.

Zed requires a grammar repository and an immutable revision. The checked-in
`PUBLISH_COMMIT` marker in `extension.toml` must be replaced, in a follow-up
commit, with the first Grandiose commit that contains the root grammar. Until
that pin is made, Zed's development-extension installer will reject the grammar
source as expected.

The server path may be overridden in Zed settings:

```jsonc
"lsp": {
  "grand-lsp": {
    "binary": { "path": "/absolute/path/to/grand-lsp" }
  }
}
```

The server advertises its standard library at the read-only virtual URI
`grandiose-std:/distributed_std.glorious`. Zed currently has no extension API
for registering the custom `grandiose/virtualDocument` content provider, so a
definition into that URI cannot be opened in Zed. Project-file definitions and
all standard LSP features are unaffected.
