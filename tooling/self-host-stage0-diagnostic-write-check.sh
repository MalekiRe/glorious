#!/usr/bin/env bash
# Proves diagnostic emission is an explicit runtime host effect.
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
readonly compiler="$root/target/debug/grc-stage0"
readonly support="$root/self-host-stage0/runtime/compiler_support.glorious"
readonly probe="$root/self-host-stage0/probes/diagnostic_write.glorious"

if [[ "${GRANDIOSE_STAGE0_ALREADY_BUILT:-0}" != 1 ]]; then
    cargo build -q -p grandiose-stage0 --bin grc-stage0
fi

base=(
    --root-package diagnostic-write-probe@0.1.0
    --source compiler_support@0.1.0 src/lib.glorious "$support"
    --runtime-standard-library compiler_support@0.1.0
    --runtime-leaf branch-bool crate branch_bool
    --runtime-leaf blake3 crate __g1_blake3
    --runtime-leaf text-as-bytes crate __g1_text_as_bytes
    --runtime-leaf text-eq crate __g1_text_eq
    --runtime-leaf bytes-len crate __g1_bytes_len
    --runtime-leaf bytes-get crate __g1_bytes_get
    --runtime-leaf bytes-slice crate __g1_bytes_slice --runtime-leaf bytes-concat crate __g1_bytes_concat --runtime-leaf bytes-from-array-move crate __g1_bytes_from_array_move --runtime-leaf int-shr crate __g1_int_shr --runtime-leaf int-convert-wrapping-to-u32 crate __g1_int_convert_wrapping_to_u32 --runtime-leaf int-convert-wrapping-to-u64 crate __g1_int_convert_wrapping_to_u64 --runtime-leaf int-convert-wrapping-to-u8 crate __g1_int_convert_wrapping_to_u8 --runtime-leaf int-convert-checked-to-i64 crate __g1_int_convert_checked_to_i64
    --runtime-leaf int-wrapping-add crate __g1_int_wrapping_add
    --runtime-leaf int-wrapping-sub crate __g1_int_wrapping_sub
    --runtime-leaf int-wrapping-mul crate __g1_int_wrapping_mul
    --runtime-leaf int-checked-div crate __g1_int_checked_div
    --runtime-leaf array-empty crate __g1_array_empty --runtime-leaf array-len crate __g1_array_len --runtime-leaf array-get-move crate __g1_array_get_move
    --runtime-leaf array-pop-move crate __g1_array_pop_move
)

temporary="$(mktemp -d)"
trap 'rm -rf "$temporary"' EXIT
output="$("$compiler" "${base[@]}" --runtime-host diagnostic __g1_diagnostic_write crate write_diagnostic --capability diagnostic run "$probe" 2>"$temporary/stderr")"
[[ "$output" == "7" ]] || { echo "self-host diagnostic check: expected host-bound program result" >&2; exit 1; }
grep -Fxq 'self-host-diagnostic' "$temporary/stderr" || { echo "self-host diagnostic check: host diagnostic was not emitted" >&2; exit 1; }

"$compiler" "${base[@]}" run "$probe" 2>"$temporary/unbound-stderr" >/dev/null
if grep -Fq 'self-host-diagnostic' "$temporary/unbound-stderr"; then
    echo "self-host diagnostic check: diagnostic unexpectedly escaped without authority" >&2
    exit 1
fi
