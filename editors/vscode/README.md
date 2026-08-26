# Grandiose for VS Code

**Status:** syntax highlighting available; `grand-lsp` integration unsupported

The extension contributes the `.glorious` language id, TextMate grammar, and
language configuration. Its JavaScript client and `grandiose.serverPath`
setting are retained from the pre-Stage0 language-server integration.

The active repository does not ship a supported `grand-lsp`: the server crate
is excluded from the root workspace and identifies itself as disabled pending a
Stage0 redesign. Installing or packaging this extension should therefore be
understood as installing syntax support, not a working diagnostics,
navigation, or formatting stack.

## Validate and package syntax assets

```sh
cd editors/vscode
npm ci
npm run validate
npm run package
```

These commands validate/package the extension files. They do not validate an
LSP server.

Do not publish release notes that promise LSP features until a Stage0-native
server has an explicit implementation contract and end-to-end tests.
