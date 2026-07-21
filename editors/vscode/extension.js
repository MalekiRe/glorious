// Grandiose VS Code extension: thin LSP client around grand-lsp.
const vscode = require("vscode");
const { LanguageClient } = require("vscode-languageclient/node");

let client;

function activate(context) {
  const configured = vscode.workspace
    .getConfiguration("grandiose")
    .get("serverPath", "grand-lsp");
  // `grand` works too: it delegates `grand lsp` to the sibling grand-lsp.
  const serverOptions =
    configured === "grand"
      ? { command: "grand", args: ["lsp"] }
      : { command: configured, args: [] };
  client = new LanguageClient(
    "grandiose",
    "Grandiose Language Server",
    { run: serverOptions, debug: serverOptions },
    {
      documentSelector: [{ scheme: "file", language: "grandiose" }],
      synchronize: {
        fileEvents: vscode.workspace.createFileSystemWatcher(
          "**/*.{glorious,gr,toml}"
        ),
      },
    }
  );
  context.subscriptions.push({ dispose: () => client && client.stop() });
  client.start();
}

function deactivate() {
  return client ? client.stop() : undefined;
}

module.exports = { activate, deactivate };
