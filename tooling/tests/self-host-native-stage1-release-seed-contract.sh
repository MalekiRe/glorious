#!/usr/bin/env bash
# Contract: Stage1 may copy only a receipt-bound release grc into a disposable
# snapshot; an absent or mismatched receipt remains a cold build.
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)
stage1="$repo_root/tooling/self-host-native-stage1.sh"
native="$repo_root/tooling/self-host-native.sh"
bash -n "$stage1" "$native"
grep -Fq 'readonly release_grc_seed="$repo_root/target/release/grc.stage1-seed.tsv"' "$stage1"
grep -Fq 'seed_snapshot_release_grc || record_failure snapshot-seed 1' "$stage1"
grep -Fq '"$commit" == "$run_head"' "$stage1"
grep -Fq 'cp -- "$release_grc" "$destination/grc"' "$stage1"
grep -Fq 'readonly route_grc_seed="$route_root/target/release/grc.stage1-seed.tsv"' "$native"
grep -Fq 'cargo build --release -p grandiose --bin grc' "$native"
