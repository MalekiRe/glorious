import { readFileSync } from "node:fs";

const manifest = JSON.parse(readFileSync(new URL("../package.json", import.meta.url)));
const grammar = JSON.parse(
  readFileSync(new URL("../syntaxes/grandiose.tmLanguage.json", import.meta.url))
);
const extension = readFileSync(new URL("../extension.js", import.meta.url), "utf8");

function requireInvariant(condition, message) {
  if (!condition) {
    throw new Error(message);
  }
}

requireInvariant(manifest.name === "grandiose", "extension name must stay canonical");
requireInvariant(manifest.publisher === "grandiose-lang", "publisher must stay canonical");
requireInvariant(/^\d+\.\d+\.\d+$/.test(manifest.version), "version must be semver");
requireInvariant(manifest.main === "./extension.js", "extension entrypoint drifted");
requireInvariant(
  manifest.activationEvents?.includes("onLanguage:grandiose"),
  "Grandiose language activation is missing"
);
const language = manifest.contributes?.languages?.find(({ id }) => id === "grandiose");
requireInvariant(language, "Grandiose language contribution is missing");
requireInvariant(
  [".glorious", ".gr"].every((suffix) => language.extensions.includes(suffix)),
  "canonical and compatibility source suffixes must both be packaged"
);
requireInvariant(
  manifest.contributes?.grammars?.some(
    ({ language, scopeName, path }) =>
      language === "grandiose" &&
      scopeName === "source.grandiose" &&
      path === "./syntaxes/grandiose.tmLanguage.json"
  ),
  "grammar contribution does not match the packaged grammar"
);
requireInvariant(grammar.scopeName === "source.grandiose", "grammar scope drifted");
requireInvariant(
  manifest.dependencies?.["vscode-languageclient"] === "9.0.1",
  "runtime client dependency must be exactly pinned"
);
requireInvariant(
  manifest.devDependencies?.["@vscode/vsce"] === "3.9.2",
  "VSIX packager must be exactly pinned"
);
requireInvariant(
  manifest.contributes?.configuration?.properties?.["grandiose.serverPath"]?.default ===
    "grand-lsp",
  "standalone grand-lsp must remain the default command"
);
requireInvariant(
  extension.includes('configured === "grand"') && extension.includes('args: ["lsp"]'),
  "grand lsp compatibility launch path is missing"
);
requireInvariant(
  extension.includes('args: []'),
  "standalone grand-lsp launch must not receive hidden arguments"
);
