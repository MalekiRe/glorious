#!/usr/bin/env bash
# Proves source-owned `emit-vm` selection/arity policy dispatches to the
# actual file-backed compiler service, rather than a launcher-side shortcut.
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
readonly grvm="$root/target/debug/grvm"
readonly probe="$root/self-host-stage0/probes/g1_cli_emit_vm_file_artifact_write.glorious"

if [[ "${GRANDIOSE_GRVM_ALREADY_BUILT:-0}" != 1 ]]; then
    cargo build -q -p grandiose-vm --bin grvm
fi

temporary="$(mktemp -d)"
trap 'rm -rf "$temporary"' EXIT
printf '%s\n' 'pub fn main() -> i64 { 40 + 2 }' > "$temporary/arithmetic-input.glorious"
printf '%s\n' 'pub fn main() -> i64 { if false { 7 } else { 9 } }' > "$temporary/select-input.glorious"
printf '%s\n' 'pub fn main() -> i64 { return 40 + 2; }' > "$temporary/return-input.glorious"
printf '%s\n' 'pub fn main() -> i64 { return if false { 7 } else { 42 }; }' > "$temporary/return-select-input.glorious"
printf '%s\n' 'pub fn main() -> i64 { return 42 }' > "$temporary/return-invalid-input.glorious"
printf '%s\n' 'pub fn main() -> i64 { return if false { 7 } else { 42 } }' > "$temporary/return-select-invalid-input.glorious"
result="$(cd "$temporary" && GRANDIOSE_STAGE0_ALREADY_BUILT=1 GRANDIOSE_STAGE0_SERVICE_PROBE="$probe" GRANDIOSE_STAGE0_SERVICE_EXPECTED=136 \
    "$root/tooling/self-host-stage0-service-check.sh" \
    --runtime-host file_read __g1_fs_read crate read_file --capability file_read \
    --runtime-host file_write_atomic __g1_fs_write_atomic crate write_file_atomically --capability file_write_atomic)"
[[ "$result" == "136" ]] || { echo "self-host G1 CLI emit-vm check: source CLI dispatch failed: $result" >&2; exit 1; }
[[ "$(wc -c < "$temporary/arithmetic-output.grbc")" == "1280" ]] || { echo "self-host G1 CLI emit-vm check: expected 1280 bytes" >&2; exit 1; }
"$grvm" verify "$temporary/arithmetic-output.grbc"
"$grvm" run "$temporary/arithmetic-output.grbc"
[[ "$(wc -c < "$temporary/select-output.grbc")" == "1168" ]] || { echo "self-host G1 CLI emit-vm check: expected 1168-byte conditional artifact" >&2; exit 1; }
"$grvm" verify "$temporary/select-output.grbc"
"$grvm" run "$temporary/select-output.grbc"
[[ "$(wc -c < "$temporary/return-output.grbc")" == "1280" ]] || { echo "self-host G1 CLI emit-vm check: expected 1280-byte explicit-return binary artifact" >&2; exit 1; }
"$grvm" verify "$temporary/return-output.grbc"
# G1 executable entries are Unit-returning; the private i64 callee carries
# the value. Successful guest execution is therefore the observable contract.
"$grvm" run "$temporary/return-output.grbc"
[[ "$(wc -c < "$temporary/return-select-output.grbc")" == "1168" ]] || { echo "self-host G1 CLI emit-vm check: expected 1168-byte explicit-return conditional artifact" >&2; exit 1; }
"$grvm" verify "$temporary/return-select-output.grbc"
"$grvm" run "$temporary/return-select-output.grbc"
[[ ! -e "$temporary/invalid-output.grbc" ]] || { echo "self-host G1 CLI emit-vm check: malformed argv reached artifact publication" >&2; exit 1; }
[[ ! -e "$temporary/return-invalid-output.grbc" ]] || { echo "self-host G1 CLI emit-vm check: return without semicolon reached artifact publication" >&2; exit 1; }
[[ ! -e "$temporary/return-select-invalid-output.grbc" ]] || { echo "self-host G1 CLI emit-vm check: conditional return without semicolon reached artifact publication" >&2; exit 1; }

invalid="$temporary/invalid"
mkdir "$invalid"
printf '%s\n' 'pub fn answer() -> i64 { 40 + }' > "$invalid/arithmetic-input.glorious"
printf '%s\n' 'pub fn main() -> i64 { if false { 7 } else { 9 } }' > "$invalid/select-input.glorious"
printf '%s\n' 'pub fn main() -> i64 { return 40 + 2; }' > "$invalid/return-input.glorious"
printf '%s\n' 'pub fn main() -> i64 { return if false { 7 } else { 42 }; }' > "$invalid/return-select-input.glorious"
printf '%s\n' 'pub fn main() -> i64 { return 42 }' > "$invalid/return-invalid-input.glorious"
printf '%s\n' 'pub fn main() -> i64 { return if false { 7 } else { 42 } }' > "$invalid/return-select-invalid-input.glorious"
invalid_result="$(cd "$invalid" && GRANDIOSE_STAGE0_ALREADY_BUILT=1 GRANDIOSE_STAGE0_SERVICE_PROBE="$probe" GRANDIOSE_STAGE0_SERVICE_EXPECTED=0 \
    "$root/tooling/self-host-stage0-service-check.sh" \
    --runtime-host file_read __g1_fs_read crate read_file --capability file_read \
    --runtime-host file_write_atomic __g1_fs_write_atomic crate write_file_atomically --capability file_write_atomic)"
[[ "$invalid_result" == "0" ]] || { echo "self-host G1 CLI emit-vm check: malformed arithmetic source was accepted: $invalid_result" >&2; exit 1; }
[[ ! -e "$invalid/arithmetic-output.grbc" ]] || { echo "self-host G1 CLI emit-vm check: rejected source published an artifact" >&2; exit 1; }
printf '%s\n' "$result"
