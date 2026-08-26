#!/usr/bin/env bash
# Compile the complete declared self-host source world as one package. The
# isolated module probes catch local behavior; this gate catches a module that
# only works when packaged in a synthetic test library.
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
readonly compiler="$root/target/debug/grc-stage0"
readonly sources="$root/self-host-stage0/sources.tsv"
readonly root_source="$root/self-host-stage0/src/main.glorious"
readonly maximum_seconds="${GRANDIOSE_STAGE0_CANONICAL_TIMEOUT_SECONDS:-300}"

if ! [[ "$maximum_seconds" =~ ^[1-9][0-9]*$ ]] || (( maximum_seconds > 300 )); then
    echo "self-host canonical world check: timeout must be an integer from 1 to 300 seconds" >&2
    exit 2
fi

if [[ "${GRANDIOSE_STAGE0_ALREADY_BUILT:-0}" != 1 ]]; then
    cargo build -q -p grandiose-stage0 --bin grc-stage0
fi

args=()
while IFS=$'\t' read -r package logical physical _; do
    [[ "$package" == "package" || "$logical" == "src/main.glorious" ]] && continue
    args+=(--source "$package" "$logical" "$root/$physical")
done < "$sources"

output="$(timeout --kill-after=5s --preserve-status "${maximum_seconds}s" "$compiler" --root-package self-host-stage0@0.1.0 "${args[@]}" \
    --runtime-standard-library compiler_support@0.1.0 \
    --runtime-leaf branch-bool crate branch_bool \
    --runtime-leaf blake3 crate __g1_blake3 \
    --runtime-leaf text-as-bytes crate __g1_text_as_bytes \
    --runtime-leaf text-eq crate __g1_text_eq \
    --runtime-leaf bytes-len crate __g1_bytes_len \
    --runtime-leaf bytes-get crate __g1_bytes_get \
    --runtime-leaf bytes-slice crate __g1_bytes_slice --runtime-leaf bytes-concat crate __g1_bytes_concat --runtime-leaf bytes-from-array-move crate __g1_bytes_from_array_move --runtime-leaf int-shr crate __g1_int_shr --runtime-leaf int-convert-wrapping-to-u32 crate __g1_int_convert_wrapping_to_u32 --runtime-leaf int-convert-wrapping-to-u64 crate __g1_int_convert_wrapping_to_u64 --runtime-leaf int-convert-wrapping-to-u8 crate __g1_int_convert_wrapping_to_u8 --runtime-leaf int-convert-checked-to-i64 crate __g1_int_convert_checked_to_i64 \
    --runtime-leaf int-wrapping-add crate __g1_int_wrapping_add --runtime-leaf int-wrapping-sub crate __g1_int_wrapping_sub --runtime-leaf int-wrapping-mul crate __g1_int_wrapping_mul --runtime-leaf int-checked-div crate __g1_int_checked_div \
    --runtime-leaf array-empty crate __g1_array_empty --runtime-leaf array-len crate __g1_array_len --runtime-leaf array-get-move crate __g1_array_get_move \
    --runtime-leaf array-pop-move crate __g1_array_pop_move \
    run "$root_source")"
[[ "$output" == "149" ]] || {
    echo "self-host canonical world check: expected bootstrap, verifier-backed source artifacts including literal branch selection, bound i64/Bool parameter execution/conditionals, body-to-VM pipeline, cache-and-keyed query-service, guarded publication, CLI options, diagnostic provenance, source identity, checked scanner and header admission, invocation, and cross-module result 149, got $output" >&2
    exit 1
}
printf '%s\n' "$output"
