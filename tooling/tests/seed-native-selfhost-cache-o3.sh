#!/usr/bin/env bash
set -euo pipefail

repository=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)
temporary=$(mktemp -d)
cleanup() { rm -rf "$temporary"; }
trap cleanup EXIT

worktree="$temporary/worktree"
baseline="$temporary/baseline"
mkdir -p "$worktree" "$baseline"
git -C "$worktree" init -q
printf 'known good executable\n' > "$baseline/self-host"
checksum=$(sha256sum "$baseline/self-host" | awk '{print $1}')
printf 'schema\t1\nrevision\ttest\noptimization\tO2\ncache-fingerprint\ttest;optimization=O2\nfile\tself-host\t%s\n' "$checksum" > "$baseline/manifest.tsv"

if "$repository/tooling/seed-native-selfhost-cache.sh" --worktree "$worktree" --baseline "$baseline" >"$temporary/stdout" 2>"$temporary/stderr"; then
  echo "expected O2 baseline manifest to be rejected" >&2
  exit 1
fi
grep -q 'optimization O3' "$temporary/stderr"
[[ ! -e "$worktree/target/self-host-native-cache/manifest.tsv" ]]
