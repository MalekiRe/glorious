#!/usr/bin/env bash
# Seed one worktree's private native self-host cache from a known-good,
# read-only baseline.  This deliberately never creates or updates the
# baseline: concurrent /tmp worktrees only read it, then make ordinary copies
# into their own target directory.
set -euo pipefail

usage() {
  echo "usage: $0 [--baseline DIR] [--worktree DIR]" >&2
  exit 2
}

baseline=''
worktree="$PWD"
while (($#)); do
  case "$1" in
    --baseline) shift; (($#)) || usage; baseline="$1" ;;
    --worktree) shift; (($#)) || usage; worktree="$1" ;;
    -h|--help) usage ;;
    *) usage ;;
  esac
  shift
done

worktree=$(cd "$worktree" && pwd -P)
common=$(git -C "$worktree" rev-parse --git-common-dir)
if [[ "$common" != /* ]]; then common="$worktree/$common"; fi
common=$(cd "$common" && pwd -P)
if [[ -z "$baseline" ]]; then
  baseline="$common/grandiose-native-selfhost-baseline"
fi
baseline=$(cd "$baseline" 2>/dev/null && pwd -P) || {
  echo "seed-native-selfhost-cache: baseline does not exist: $baseline" >&2
  exit 1
}

manifest="$baseline/manifest.tsv"
[[ -f "$manifest" ]] || {
  echo "seed-native-selfhost-cache: missing baseline manifest: $manifest" >&2
  exit 1
}

schema=''
revision=''
optimization=''
fingerprint=''
entries=()
while IFS=$'\t' read -r kind first second extra; do
  [[ -z "$kind" || "$kind" == \#* ]] && continue
  [[ -z "$extra" ]] || { echo "seed-native-selfhost-cache: malformed manifest row" >&2; exit 1; }
  case "$kind" in
    schema) [[ -z "$schema" ]] || { echo "seed-native-selfhost-cache: duplicate schema" >&2; exit 1; }; schema="$first" ;;
    revision) [[ -z "$revision" ]] || { echo "seed-native-selfhost-cache: duplicate revision" >&2; exit 1; }; revision="$first" ;;
    optimization) [[ -z "$optimization" ]] || { echo "seed-native-selfhost-cache: duplicate optimization" >&2; exit 1; }; optimization="$first" ;;
    cache-fingerprint) [[ -z "$fingerprint" ]] || { echo "seed-native-selfhost-cache: duplicate cache fingerprint" >&2; exit 1; }; fingerprint="$first" ;;
    file) [[ -n "$first" && -n "$second" ]] || { echo "seed-native-selfhost-cache: malformed file row" >&2; exit 1; }; entries+=("$first"$'\t'"$second") ;;
    *) echo "seed-native-selfhost-cache: unknown manifest row: $kind" >&2; exit 1 ;;
  esac
done < "$manifest"
[[ "$schema" == 1 && -n "$revision" && "$optimization" == O3 && -n "$fingerprint" && ${#entries[@]} -gt 0 ]] || {
  echo "seed-native-selfhost-cache: manifest must provide schema 1, revision, optimization O3, cache fingerprint, and files" >&2
  exit 1
}
[[ "$fingerprint" == *"optimization=O3"* ]] || {
  echo "seed-native-selfhost-cache: cache fingerprint is incompatible with required optimization=O3" >&2
  exit 1
}

destination="$worktree/target/self-host-native-cache"
mkdir -p "$destination"
stage=$(mktemp -d "$worktree/target/.self-host-native-cache.XXXXXX")
cleanup() { rm -rf "$stage"; }
trap cleanup EXIT

for entry in "${entries[@]}"; do
  path=${entry%%$'\t'*}
  expected=${entry#*$'\t'}
  [[ "$path" != /* && "$path" != *".."* && "$path" != *$'\n'* ]] || {
    echo "seed-native-selfhost-cache: unsafe baseline path: $path" >&2; exit 1;
  }
  source="$baseline/$path"
  [[ -f "$source" ]] || { echo "seed-native-selfhost-cache: missing baseline file: $path" >&2; exit 1; }
  actual=$(sha256sum "$source" | awk '{print $1}')
  [[ "$actual" == "$expected" ]] || { echo "seed-native-selfhost-cache: baseline checksum mismatch: $path" >&2; exit 1; }
  mkdir -p "$stage/$(dirname "$path")"
  cp -- "$source" "$stage/$path"
  copied=$(sha256sum "$stage/$path" | awk '{print $1}')
  [[ "$copied" == "$expected" ]] || { echo "seed-native-selfhost-cache: copied checksum mismatch: $path" >&2; exit 1; }
done

# The manifest is the ready marker.  Each payload is atomically renamed into
# this worktree's private cache before the ready marker becomes visible.
while IFS=$'\t' read -r kind path checksum; do
  [[ "$kind" == file ]] || continue
  mkdir -p "$destination/$(dirname "$path")"
  mv -- "$stage/$path" "$destination/$path"
done < "$manifest"
tmp_manifest="$destination/.manifest.tsv.$$"
cp -- "$manifest" "$tmp_manifest"
mv -- "$tmp_manifest" "$destination/manifest.tsv"
printf 'seeded revision=%s optimization=%s fingerprint=%s files=%s cache=%s\n' \
  "$revision" "$optimization" "$fingerprint" "${#entries[@]}" "$destination"
