# Grandiose for Zed

**Status:** syntax highlighting available; `grand-lsp` integration unsupported

This extension contains the Grandiose grammar and language configuration. Its
manifest and Rust extension code also retain a pre-Stage0 `grand-lsp` launcher.

The active repository does not provide a supported language server:
`tooling/lsp` is excluded from the root workspace and is marked as disabled
pending a Stage0 redesign. Treat the extension as syntax support only.
Diagnostics, navigation, formatting, and language-server download behavior are
legacy and may fail.

A future Stage0-native language server should update the manifest, launcher,
release workflow, and all editor documentation together. Packaging the current
extension is not evidence that the LSP is supported.
