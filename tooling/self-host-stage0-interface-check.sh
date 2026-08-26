#!/usr/bin/env bash
# Executes M10's source-defined declaration namespace/visibility boundary.
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
readonly compiler="$root/target/debug/grc-stage0"
readonly support="$root/self-host-stage0/runtime/compiler_support.glorious"
readonly probe="$root/self-host-stage0/probes/interface.glorious"
readonly interface="$root/self-host-stage0/src/interface/interface.glorious"
readonly library="$root/self-host-stage0/probes/interface_library.glorious"
readonly identity="$root/self-host-stage0/src/identity/identity.glorious"
readonly diagnostic="$root/self-host-stage0/src/diagnostic/diagnostic.glorious"
readonly source="$root/self-host-stage0/src/source/source.glorious"
readonly scanner="$root/self-host-stage0/src/scanner/scanner.glorious"
readonly header="$root/self-host-stage0/src/header/header.glorious"

if [[ "${GRANDIOSE_STAGE0_ALREADY_BUILT:-0}" != 1 ]]; then
    cargo build -q -p grandiose-stage0 --bin grc-stage0
fi
output="$("$compiler" \
    --root-package interface-probe@0.1.0 \
    --source compiler_support@0.1.0 src/lib.glorious "$support" \
    --source interface-library@0.1.0 src/lib.glorious "$library" \
    --source interface-library@0.1.0 src/identity/identity.glorious "$identity" \
    --source interface-library@0.1.0 src/diagnostic/diagnostic.glorious "$diagnostic" \
    --source interface-library@0.1.0 src/source/source.glorious "$source" \
    --source interface-library@0.1.0 src/scanner/scanner.glorious "$scanner" \
    --source interface-library@0.1.0 src/header/header.glorious "$header" \
    --source interface-library@0.1.0 src/interface/interface.glorious "$interface" \
    --runtime-standard-library compiler_support@0.1.0 \
    --runtime-leaf branch-bool crate branch_bool \
    --runtime-leaf blake3 crate __g1_blake3 \
    --runtime-leaf text-as-bytes crate __g1_text_as_bytes \
    --runtime-leaf text-eq crate __g1_text_eq \
    --runtime-leaf bytes-len crate __g1_bytes_len \
    --runtime-leaf bytes-get crate __g1_bytes_get \
    --runtime-leaf bytes-slice crate __g1_bytes_slice --runtime-leaf bytes-concat crate __g1_bytes_concat --runtime-leaf bytes-from-array-move crate __g1_bytes_from_array_move --runtime-leaf int-shr crate __g1_int_shr --runtime-leaf int-convert-wrapping-to-u32 crate __g1_int_convert_wrapping_to_u32 --runtime-leaf int-convert-wrapping-to-u64 crate __g1_int_convert_wrapping_to_u64 --runtime-leaf int-convert-wrapping-to-u8 crate __g1_int_convert_wrapping_to_u8 --runtime-leaf int-convert-checked-to-i64 crate __g1_int_convert_checked_to_i64 \
    --runtime-leaf int-wrapping-add crate __g1_int_wrapping_add --runtime-leaf int-wrapping-sub crate __g1_int_wrapping_sub --runtime-leaf int-wrapping-mul crate __g1_int_wrapping_mul --runtime-leaf int-checked-div crate __g1_int_checked_div \
    run "$probe")"
[[ "$output" == "8" ]] || {
    echo "self-host interface check: expected public declarations, fixities, host imports, aliases, and preserved auto-trait identity, got $output" >&2
    exit 1
}
printf '%s\n' "$output"
