#!/usr/bin/env bash
# Compile the canonical new self-host source world with the frozen Rust Stage0
# seed. The manifest gives every source a stable logical identity.
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
readonly manifest="$root/self-host-stage0/sources.tsv"
readonly compiler="$root/target/debug/grc-stage0"

[[ -f "$manifest" ]] || { echo "self-host check: source manifest is missing" >&2; exit 1; }

# Cargo's incremental no-op path is cheap; always invoke it so a previously
# built binary cannot silently lag behind the Stage0 sources under test.
if [[ "${GRANDIOSE_STAGE0_ALREADY_BUILT:-0}" != 1 ]]; then
    cargo build -q -p grandiose-stage0 --bin grc-stage0
fi

root_source=
root_package=
runtime_package=
arguments=()
while IFS=$'\t' read -r package logical_path physical_path role; do
    [[ "$package" == "package" ]] && continue
    [[ -n "$package" && -n "$logical_path" && -n "$physical_path" && -n "$role" ]] || {
        echo "self-host check: malformed source manifest row" >&2
        exit 1
    }
    [[ "$physical_path" != /* && "$physical_path" != *".."* && -f "$root/$physical_path" ]] || {
        echo "self-host check: invalid source path $physical_path" >&2
        exit 1
    }
    if [[ "$role" == "root" ]]; then
        [[ -z "$root_source" ]] || { echo "self-host check: multiple roots" >&2; exit 1; }
        root_source="$root/$physical_path"
        root_package="$package"
    elif [[ "$role" == "runtime-standard-library" ]]; then
        [[ -z "$runtime_package" ]] || { echo "self-host check: multiple runtime libraries" >&2; exit 1; }
        runtime_package="$package"
        arguments+=(--source "$package" "$logical_path" "$root/$physical_path")
    else
        arguments+=(--source "$package" "$logical_path" "$root/$physical_path")
    fi
done < "$manifest"

[[ -n "$root_source" ]] || { echo "self-host check: source manifest has no root" >&2; exit 1; }
[[ -n "$runtime_package" ]] || { echo "self-host check: missing runtime library" >&2; exit 1; }
output="$("$compiler" --root-package "$root_package" "${arguments[@]}" \
    --runtime-standard-library "$runtime_package" \
    --runtime-leaf branch-bool crate branch_bool \
    --runtime-leaf blake3 crate __g1_blake3 \
    --runtime-leaf text-as-bytes crate __g1_text_as_bytes \
    --runtime-leaf bytes-len crate __g1_bytes_len \
    --runtime-leaf bytes-get crate __g1_bytes_get \
    --runtime-leaf bytes-slice crate __g1_bytes_slice --runtime-leaf bytes-concat crate __g1_bytes_concat --runtime-leaf bytes-from-array-move crate __g1_bytes_from_array_move --runtime-leaf int-shr crate __g1_int_shr --runtime-leaf int-convert-wrapping-to-u32 crate __g1_int_convert_wrapping_to_u32 --runtime-leaf int-convert-wrapping-to-u64 crate __g1_int_convert_wrapping_to_u64 --runtime-leaf int-convert-wrapping-to-u8 crate __g1_int_convert_wrapping_to_u8 --runtime-leaf int-convert-checked-to-i64 crate __g1_int_convert_checked_to_i64 \
    --runtime-leaf int-wrapping-add crate __g1_int_wrapping_add --runtime-leaf int-wrapping-sub crate __g1_int_wrapping_sub --runtime-leaf int-wrapping-mul crate __g1_int_wrapping_mul --runtime-leaf int-checked-div crate __g1_int_checked_div \
    --runtime-leaf text-eq crate __g1_text_eq \
    --runtime-leaf array-empty crate __g1_array_empty --runtime-leaf array-len crate __g1_array_len --runtime-leaf array-get-move crate __g1_array_get_move \
    --runtime-leaf array-pop-move crate __g1_array_pop_move \
    run "$root_source")"
[[ "$output" == "149" ]] || {
    echo "self-host check: expected canonical bootstrap, verifier-backed source artifacts including literal branch selection, bound i64/Bool parameter execution/conditionals, body-to-VM pipeline, cache-and-keyed service, guarded publication, CLI options, diagnostic provenance, source identity, checked scanner and header admission, invocation, and cross-module result 149, got $output" >&2
    exit 1
}
printf '%s\n' "$output"
