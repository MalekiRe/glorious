# Grandiose editor setup

The canonical source suffix is `.glorious`; `.gr` remains a legacy compatibility
suffix. Build `tooling/lsp` and place `grand-lsp` on `PATH`, or use `grand lsp`
as the stdio language-server command. Both commands speak ordinary LSP over
stdin/stdout and require no editor-specific transport.

## Neovim

With `nvim-lspconfig`, register `.glorious` and start the server from the nearest
directory containing `grandiose.toml`:

```lua
vim.filetype.add({ extension = { glorious = "grandiose", gr = "grandiose" } })
vim.lsp.config.grandiose = {
  cmd = { "grand-lsp" },
  filetypes = { "grandiose" },
  root_markers = { "grandiose.toml", ".git" },
}
vim.lsp.enable("grandiose")
```

## Helix

Add this to `languages.toml`:

```toml
[language-server.grandiose]
command = "grand-lsp"

[[language]]
name = "grandiose"
scope = "source.grandiose"
file-types = ["glorious", "gr"]
roots = ["grandiose.toml", ".git"]
language-servers = ["grandiose"]
```

## Zed and other clients

Configure a language named `Grandiose` for `*.glorious` and `*.gr`, with
`grandiose.toml` as its project marker and `grand-lsp` as its stdio server.
Clients which accept an argument-bearing command may use `grand lsp` instead.

The server accepts `workspaceFolders` and checks each project as an independent
bundle; completion, definition, rename, and reference searches stay within the
originating root. Document versions are monotonic, malformed ranged changes are
ignored under the advertised full-sync contract, and cancelled requests cannot
flush pending diagnostics. Byte/UTF-16 conversion clamps invalid byte and
surrogate-interior positions without panicking.
The TextMate grammar used by the VS Code extension is available at
`editors/vscode/syntaxes/grandiose.tmLanguage.json` for clients which accept
external grammars.

The VS Code extension has its own setup instructions in
`editors/vscode/README.md`.

## Distribution artifacts

Run `editors/package-local.sh <new-output-directory>` to produce a locked VSIX,
a host-native `grand-lsp` archive, and SHA-256 checksum files. Cross-platform
standalone server archives are built by `.github/workflows/editor-release.yml`
for Linux x86-64, macOS Apple Silicon, and Windows x86-64. The workflow stores
artifacts in the CI run and never publishes externally; installation and
checksum verification are documented in `editors/vscode/README.md`.
