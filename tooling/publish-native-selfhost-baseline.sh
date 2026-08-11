#!/usr/bin/env bash
# Publish a verified, immutable O3/Wild native self-host cache as the baseline
# for *new* Git worktrees.  This is deliberately a copy publisher, not a
# shared cache: consumers use seed-native-selfhost-cache.sh to copy its files
# into their own target directory before doing any work.
set -euo pipefail

usage() {
  cat >&2 <<'USAGE'
usage: tooling/publish-native-selfhost-baseline.sh [--worktree DIR] [--output DIR]

Publishes the private target/self-host-native-cache from WORKTREE as a new
read-only baseline.  The output defaults to the Git-common-dir baseline path.
It refuses to replace an existing baseline.  Only an O3, Wild-linked native
compiler with an exact build fingerprint can be published.
USAGE
  exit 2
}

worktree="$PWD"
output=''
while (($#)); do
  case "$1" in
    --worktree) shift; (($#)) || usage; worktree="$1" ;;
    --output) shift; (($#)) || usage; output="$1" ;;
    -h|--help) usage ;;
    *) usage ;;
  esac
  shift
done

worktree=$(cd -- "$worktree" && pwd -P)
git -C "$worktree" rev-parse --is-inside-work-tree >/dev/null
cache="$worktree/target/self-host-native-cache"
binary="$cache/grandiose-self-host-native"
fingerprint="$cache/build.fingerprint"
route_manifest="$cache/native-route.manifest"
[[ -x "$binary" && -s "$fingerprint" && -f "$route_manifest" ]] || {
  echo "publish-native-selfhost-baseline: worktree has no complete private native cache" >&2
  exit 1
}
grep -Fxq 'optimization=O3' "$route_manifest" || {
  echo "publish-native-selfhost-baseline: private cache is not O3" >&2
  exit 1
}
readelf -p .comment "$binary" 2>/dev/null | grep -Eqi 'wild' || {
  echo "publish-native-selfhost-baseline: native compiler lacks a Wild linker marker" >&2
  exit 1
}

common=$(git -C "$worktree" rev-parse --git-common-dir)
[[ "$common" = /* ]] || common="$worktree/$common"
common=$(cd -- "$common" && pwd -P)
if [[ -z "$output" ]]; then
  output="$common/grandiose-native-selfhost-baseline"
fi
[[ "$output" = /* ]] || output="$worktree/$output"
parent=$(dirname -- "$output")
mkdir -p "$parent"
[[ ! -e "$output" ]] || {
  echo "publish-native-selfhost-baseline: refusing to replace baseline: $output" >&2
  exit 1
}

stage=$(mktemp -d "$parent/.grandiose-native-selfhost-baseline.XXXXXX")
cleanup() { rm -rf -- "$stage"; }
trap cleanup EXIT
cp -- "$binary" "$stage/grandiose-self-host-native"
cp -- "$fingerprint" "$stage/build.fingerprint"
revision=$(git -C "$worktree" rev-parse HEAD)
{
  printf 'schema\t1\n'
  printf 'revision\t%s\n' "$revision"
  printf 'optimization\tO3\n'
  printf 'cache-fingerprint\t%s\n' "$(<"$fingerprint")"
  for file in grandiose-self-host-native build.fingerprint; do
    printf 'file\t%s\t%s\n' "$file" "$(sha256sum "$stage/$file" | awk '{print $1}')"
  done
} > "$stage/manifest.tsv"
# Consumers only require ordinary file reads.  Removing write bits makes an
# accidental shared-cache mutation visible instead of silently corrupting
# later worktree seeds.
chmod a-w "$stage"/*
mv -- "$stage" "$output"
trap - EXIT
printf '%s\n' "$output"
