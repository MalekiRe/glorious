#!/usr/bin/env bash
# Executes the actual M08 source-record scanner boundary.
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
readonly compiler="$root/target/debug/grc-stage0"
readonly support="$root/self-host-stage0/runtime/compiler_support.glorious"
readonly probe="$root/self-host-stage0/probes/scanner.glorious"
readonly escape_probe="$root/self-host-stage0/probes/scanner_escapes.glorious"
readonly stream_probe="$root/self-host-stage0/probes/scanner_stream.glorious"
readonly identity="$root/self-host-stage0/src/identity/identity.glorious"
readonly source_module="$root/self-host-stage0/src/source/source.glorious"
readonly scanner="$root/self-host-stage0/src/scanner/scanner.glorious"
readonly library="$root/self-host-stage0/probes/scanner_library.glorious"

if [[ "${GRANDIOSE_STAGE0_ALREADY_BUILT:-0}" != 1 ]]; then
    cargo build -q -p grandiose-stage0 --bin grc-stage0
fi
run_probe() {
    "$compiler" \
        --root-package scanner-probe@0.1.0 \
        --source compiler_support@0.1.0 src/lib.glorious "$support" \
        --source scanner-library@0.1.0 src/lib.glorious "$library" \
        --source scanner-library@0.1.0 src/identity/identity.glorious "$identity" \
        --source scanner-library@0.1.0 src/source/source.glorious "$source_module" \
        --source scanner-library@0.1.0 src/scanner/scanner.glorious "$scanner" \
        --runtime-standard-library compiler_support@0.1.0 \
        --runtime-leaf branch-bool crate branch_bool \
        --runtime-leaf blake3 crate __g1_blake3 \
        --runtime-leaf text-as-bytes crate __g1_text_as_bytes \
        --runtime-leaf bytes-len crate __g1_bytes_len \
        --runtime-leaf bytes-get crate __g1_bytes_get \
        --runtime-leaf bytes-slice crate __g1_bytes_slice --runtime-leaf bytes-concat crate __g1_bytes_concat --runtime-leaf bytes-from-array-move crate __g1_bytes_from_array_move --runtime-leaf int-shr crate __g1_int_shr --runtime-leaf int-convert-wrapping-to-u32 crate __g1_int_convert_wrapping_to_u32 --runtime-leaf int-convert-wrapping-to-u64 crate __g1_int_convert_wrapping_to_u64 --runtime-leaf int-convert-wrapping-to-u8 crate __g1_int_convert_wrapping_to_u8 --runtime-leaf int-convert-checked-to-i64 crate __g1_int_convert_checked_to_i64 \
        --runtime-leaf int-wrapping-add crate __g1_int_wrapping_add --runtime-leaf int-wrapping-sub crate __g1_int_wrapping_sub --runtime-leaf int-wrapping-mul crate __g1_int_wrapping_mul --runtime-leaf int-checked-div crate __g1_int_checked_div \
        run "$1"
}

result="$(run_probe "$probe")"
escape_result="$(run_probe "$escape_probe")"
stream_result="$(run_probe "$stream_probe")"
[[ "$result" == "2001140331687" ]] || {
    echo "self-host scanner check: expected digest-admitted lexical classes, numeric literals, checked cursor and token matching, strings, characters, operators, punctuation, identifier starts, and comment trivia, got $result" >&2
    exit 1
}
[[ "$escape_result" == "110" ]] || {
    echo "self-host scanner check: expected escaped-string token and boundary, got $escape_result" >&2
    exit 1
}
[[ "$stream_result" == "10702" ]] || {
    echo "self-host scanner check: expected complete token-stream admission, malformed literal rejection, and digest rejection, got $stream_result" >&2
    exit 1
}
printf '%s\n' "$result"
