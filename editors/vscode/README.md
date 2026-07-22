# Grandiose for VS Code

Syntax highlighting (TextMate grammar) plus full LSP features via `grand-lsp`:
diagnostics as you type, document symbols, go-to-definition (locals and
cross-file), hover with signatures + doc comments, completion (locals,
workspace, std prelude, keywords), find-references, rename, and formatting.
Only `.glorious` source files are recognized.

Go-to-definition on standard-library names such as `if` opens the exact library
source embedded in the running server. The server materializes that source as a
read-only, content-addressed cache file; it does not create or modify a project
file, and VS Code needs no custom URI provider.

## Setup

1. Build the server once:
   ```
   cd tooling/lsp && cargo build --release
   ```
   and put `tooling/lsp/target/release/grand-lsp` on PATH (or set
   `grandiose.serverPath` in VS Code settings to its absolute path;
   setting it to `grand` uses `grand lsp` instead).
2. Install the exact locked dependencies and launch:
   ```
   cd editors/vscode
   npm ci --ignore-scripts
   ```
   - For development: open this folder in VS Code and press F5 (Extension
     Development Host).
   - To install permanently: `npm run package` and
     `code --install-extension grandiose-0.1.0.vsix`.

Syntax highlighting works immediately with no server; LSP features light up
when `grand-lsp` is reachable.

## Reproducible packages

The extension pins both its runtime language client and `@vscode/vsce`; CI uses
Node 24 and `npm ci` against `package-lock.json`. From the repository root,
`editors/package-local.sh /path/to/empty-output-directory` builds a host-native
standalone `grand-lsp` archive and the VSIX, then writes a `.sha256` file beside
each artifact. It refuses to overwrite an existing artifact.

The `Editor release artifacts` workflow performs the same locked VSIX build and
produces standalone language-server archives for Linux x86-64, macOS Apple
Silicon, and Windows x86-64. It is triggered manually or by an `editor-v*` tag
and uploads workflow artifacts only; it does not publish to the VS Code
Marketplace or create a public release. Verify a downloaded file with
`sha256sum -c <artifact>.sha256` (or the platform's equivalent) before use.
