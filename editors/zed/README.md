# Grandiose for Zed

This extension associates `*.glorious` files with Grandiose and starts
`grand-lsp` over stdio. Its real Tree-sitter grammar lives at the repository
root; it is not a Rust grammar alias.

Zed requires a grammar repository and an immutable revision. The extension
pins the first Grandiose commit containing the root grammar, so development
extension installs fetch the native Grandiose parser reproducibly.

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
