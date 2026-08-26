#!/usr/bin/env bash
# Executes the actual M07 immutable source-record facade.
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
readonly compiler="$root/target/debug/grc-stage0"
readonly support="$root/self-host-stage0/runtime/compiler_support.glorious"
readonly probe="$root/self-host-stage0/probes/source.glorious"
readonly identity="$root/self-host-stage0/src/identity/identity.glorious"
readonly source_module="$root/self-host-stage0/src/source/source.glorious"
readonly library="$root/self-host-stage0/probes/source_library.glorious"

if [[ "${GRANDIOSE_STAGE0_ALREADY_BUILT:-0}" != 1 ]]; then
    cargo build -q -p grandiose-stage0 --bin grc-stage0
fi
result="$("$compiler" \
    --root-package source-probe@0.1.0 \
    --source compiler_support@0.1.0 src/lib.glorious "$support" \
    --source source-library@0.1.0 src/lib.glorious "$library" \
    --source source-library@0.1.0 src/identity/identity.glorious "$identity" \
    --source source-library@0.1.0 src/source/source.glorious "$source_module" \
    --runtime-standard-library compiler_support@0.1.0 \
    --runtime-leaf branch-bool crate branch_bool \
    --runtime-leaf blake3 crate __g1_blake3 \
    --runtime-leaf text-as-bytes crate __g1_text_as_bytes \
    --runtime-leaf bytes-len crate __g1_bytes_len \
    --runtime-leaf bytes-get crate __g1_bytes_get \
    --runtime-leaf bytes-slice crate __g1_bytes_slice --runtime-leaf bytes-concat crate __g1_bytes_concat --runtime-leaf bytes-from-array-move crate __g1_bytes_from_array_move --runtime-leaf int-shr crate __g1_int_shr --runtime-leaf int-convert-wrapping-to-u32 crate __g1_int_convert_wrapping_to_u32 --runtime-leaf int-convert-wrapping-to-u64 crate __g1_int_convert_wrapping_to_u64 --runtime-leaf int-convert-wrapping-to-u8 crate __g1_int_convert_wrapping_to_u8 --runtime-leaf int-convert-checked-to-i64 crate __g1_int_convert_checked_to_i64 \
    --runtime-leaf int-wrapping-add crate __g1_int_wrapping_add --runtime-leaf int-wrapping-sub crate __g1_int_wrapping_sub --runtime-leaf int-wrapping-mul crate __g1_int_wrapping_mul --runtime-leaf int-checked-div crate __g1_int_checked_div --runtime-leaf text-eq crate __g1_text_eq \
    run "$probe")"
[[ "$result" == "123603" ]] || {
    echo "self-host source check: expected digest-admitted source identity, bounded reads, line counts, and canonical UTF-8 editor-position admission, got $result" >&2
    exit 1
}
printf '%s\n' "$result"
