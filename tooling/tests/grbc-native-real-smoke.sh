#!/usr/bin/env bash
# Exercise the real verified-GRBC -> O3/Wild native boundary on the smallest
# supported source-derived artifact.  This is intentionally a smoke test for
# the artifact ABI, not a self-hosting test: it never executes the bytecode or
# the resulting executable.
set -euo pipefail

readonly script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
readonly repo_root="$(cd -- "$script_dir/../.." && pwd -P)"
readonly target_dir="${CARGO_TARGET_DIR:-$repo_root/target}"
mkdir -p "$target_dir"
scratch="$(mktemp -d "$target_dir/grbc-native-real-smoke.XXXXXX")"
trap 'rm -rf -- "$scratch"' EXIT

# Keep the prerequisite route explicit and release-only.  The driver itself
# rejects missing release binaries, but building them here makes this probe
# independently runnable from a fresh worktree.
"$repo_root/tooling/ram-gate.sh" cargo build --release -p grandiose --bin grc
"$repo_root/tooling/ram-gate.sh" cargo build --release -p grandiose-vm --bin grvm

grc="$target_dir/release/grc"
grvm="$target_dir/release/grvm"
source_file="$scratch/scalar.glorious"
artifact="$scratch/scalar.grbc"
native="$scratch/scalar-native"

cat >"$source_file" <<'SOURCE'
selected() -> i64 { 42 }
main() -> () { selected(); () }
SOURCE

# `grc` emits the actual encoded artifact; native-preflight decodes and
# verifies it but has no bytecode execution command.  `grbc-native.sh` again
# preflights and lowers only its supported AOT slice to LLVM before clang O3
# links through Wild.
"$grc" -O3 --emit grbc -o "$artifact" "$source_file"
"$grvm" native-preflight "$artifact"
"$repo_root/tooling/grbc-native.sh" \
    --artifact "$artifact" \
    --output "$native" \
    --grc "$grc" \
    --grvm "$grvm"

file "$native" | grep -Fq 'ELF'
readelf -p .comment "$native" | grep -Fq 'Linker: Wild'
