#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
output_dir="${1:-$repo_root/editors/dist}"
version="$(node -p "require('$repo_root/editors/vscode/package.json').version")"
host="$(rustc -vV | sed -n 's/^host: //p')"
binary="grand-lsp"
case "$host" in
  *-windows-*) binary="grand-lsp.exe" ;;
esac
vsix="$output_dir/grandiose-$version.vsix"
archive="$output_dir/grand-lsp-$version-$host.tar.gz"

mkdir -p "$output_dir"
for artifact in "$vsix" "$archive" "$vsix.sha256" "$archive.sha256"; do
  if [[ -e "$artifact" ]]; then
    echo "refusing to overwrite existing artifact: $artifact" >&2
    exit 1
  fi
done

npm --prefix "$repo_root/editors/vscode" ci --ignore-scripts
npm --prefix "$repo_root/editors/vscode" run package -- --out "$vsix"
cargo build --release --locked --manifest-path "$repo_root/tooling/lsp/Cargo.toml"

staging="$(mktemp -d)"
trap 'rm -rf "$staging"' EXIT
cp "$repo_root/tooling/lsp/target/release/$binary" "$staging/$binary"
cp "$repo_root/editors/README.md" "$staging/README.md"
tar -C "$staging" -czf "$archive" "$binary" README.md
(
  cd "$output_dir"
  sha256sum "$(basename "$vsix")" > "$(basename "$vsix").sha256"
  sha256sum "$(basename "$archive")" > "$(basename "$archive").sha256"
)

echo "packaged editor and language-server artifacts in $output_dir"
