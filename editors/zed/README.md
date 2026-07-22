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

The server materializes its embedded standard library in grand's
content-addressed cache. Go-to-definition returns an ordinary `file://` URI, so
Zed can open definitions such as the library implementation of `if` without a
custom content provider. The cached source is marked read-only.
