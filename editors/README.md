# Editor support

**Status:** syntax assets available; language-server integration legacy

The editor directories contain syntax highlighting, language configuration,
and historical `grand-lsp` integration.

`grand-lsp` is excluded from the active Rust compiler workspace and its own
package metadata marks it as a disabled legacy server pending a Stage0
redesign. Therefore:

- syntax highlighting and language configuration may be used and maintained;
- diagnostics, navigation, semantic tokens, formatting, and other LSP features
  are not supported by the active Stage0 toolchain;
- packaging an extension or finding legacy launch code does not make the
  language server a supported release artifact.

See [`../tooling/LEGACY.md`](../tooling/LEGACY.md) for the legacy boundary and
[`../docs/README.md`](../docs/README.md) for documentation authority.

- [`vscode/README.md`](vscode/README.md) — VS Code syntax package and legacy LSP
  caveat.
- [`zed/README.md`](zed/README.md) — Zed syntax package and legacy LSP caveat.
