#!/usr/bin/env bash
# Exercises M06's explicit host-backed publication boundary in a private
# directory. The source module chooses eligibility and bytes; the host has
# only the manifest-bound file_write_atomic capability.
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
readonly compiler="$root/target/debug/grc-stage0"
readonly support="$root/self-host-stage0/runtime/compiler_support.glorious"
readonly probe="$root/self-host-stage0/probes/output_write.glorious"
readonly failure_probe="$root/self-host-stage0/probes/output_write_failure.glorious"
readonly mismatch_probe="$root/self-host-stage0/probes/output_write_mismatch.glorious"
readonly missing_parent_probe="$root/self-host-stage0/probes/output_write_missing_parent.glorious"
readonly output_module="$root/self-host-stage0/src/output/output.glorious"
readonly library="$root/self-host-stage0/probes/output_library.glorious"

if [[ "${GRANDIOSE_STAGE0_ALREADY_BUILT:-0}" != 1 ]]; then
    cargo build -q -p grandiose-stage0 --bin grc-stage0
fi

temporary="$(mktemp -d)"
trap 'rm -rf "$temporary"' EXIT

run_probe() {
    local probe_path="$1"
    (cd "$temporary" && "$compiler" \
    --root-package output-write-probe@0.1.0 \
    --source compiler_support@0.1.0 src/lib.glorious "$support" \
    --source output-library@0.1.0 src/lib.glorious "$library" \
    --source output-library@0.1.0 src/output/output.glorious "$output_module" \
    --runtime-standard-library compiler_support@0.1.0 \
    --runtime-host file_write_atomic __g1_fs_write_atomic crate write_file_atomically \
    --capability file_write_atomic \
    --runtime-leaf branch-bool crate branch_bool \
    --runtime-leaf blake3 crate __g1_blake3 \
    --runtime-leaf text-as-bytes crate __g1_text_as_bytes \
    --runtime-leaf text-eq crate __g1_text_eq \
    --runtime-leaf bytes-len crate __g1_bytes_len \
    --runtime-leaf bytes-get crate __g1_bytes_get \
    --runtime-leaf bytes-slice crate __g1_bytes_slice --runtime-leaf bytes-concat crate __g1_bytes_concat --runtime-leaf bytes-from-array-move crate __g1_bytes_from_array_move --runtime-leaf int-shr crate __g1_int_shr --runtime-leaf int-convert-wrapping-to-u32 crate __g1_int_convert_wrapping_to_u32 --runtime-leaf int-convert-wrapping-to-u64 crate __g1_int_convert_wrapping_to_u64 --runtime-leaf int-convert-wrapping-to-u8 crate __g1_int_convert_wrapping_to_u8 --runtime-leaf int-convert-checked-to-i64 crate __g1_int_convert_checked_to_i64 \
    --runtime-leaf int-wrapping-add crate __g1_int_wrapping_add --runtime-leaf int-wrapping-sub crate __g1_int_wrapping_sub --runtime-leaf int-wrapping-mul crate __g1_int_wrapping_mul --runtime-leaf int-checked-div crate __g1_int_checked_div \
    run "$probe_path")
}

result="$(run_probe "$probe")"

[[ "$result" == "65" ]] || {
    echo "self-host output write check: expected source-owned publication success, got $result" >&2
    exit 1
}
[[ "$(<"$temporary/publication.grbc")" == "verified bytes" ]] || {
    echo "self-host output write check: publication bytes differ from the staged source value" >&2
    exit 1
}

mkdir "$temporary/rejected-target.grbc"
printf '%s' 'old visible bytes' > "$temporary/rejected-target.grbc/sentinel"
if run_probe "$failure_probe" >"$temporary/failure.stdout" 2>"$temporary/failure.stderr"; then
    echo "self-host output write check: atomic replacement of a directory unexpectedly succeeded" >&2
    exit 1
fi
[[ "$(<"$temporary/rejected-target.grbc/sentinel")" == "old visible bytes" ]] || {
    echo "self-host output write check: failed publication changed the previous visible target" >&2
    exit 1
}
if find "$temporary" -name '*.tmp' -print -quit | grep -q .; then
    echo "self-host output write check: failed publication left a staging file" >&2
    exit 1
fi

printf '%s' 'old mismatch target' > "$temporary/mismatch-target.grbc"
[[ "$(run_probe "$mismatch_probe")" == "66" ]] || {
    echo "self-host output write check: source target mismatch was not rejected" >&2
    exit 1
}
[[ "$(<"$temporary/mismatch-target.grbc")" == "old mismatch target" ]] || {
    echo "self-host output write check: target mismatch reached the host write boundary" >&2
    exit 1
}

if run_probe "$missing_parent_probe" >"$temporary/missing-parent.stdout" 2>"$temporary/missing-parent.stderr"; then
    echo "self-host output write check: publication unexpectedly created a missing parent" >&2
    exit 1
fi
[[ ! -e "$temporary/missing-parent" ]] || {
    echo "self-host output write check: failed publication created its missing parent" >&2
    exit 1
}
printf '%s\n' "$result"
