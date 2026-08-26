#!/usr/bin/env bash
# Emit the declared self-host source world as a bootstrap artifact, then make
# the independent Stage0 verifier and interpreter consume the resulting bytes.
# This is not a self-hosted compiler claim yet; it is the seed-to-executable
# artifact leg required before fixed-point stages can exist.
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
readonly compiler="$root/target/debug/grc-stage0"
readonly grvm="$root/target/debug/grvm"
readonly sources="$root/self-host-stage0/sources.tsv"

if [[ "${GRANDIOSE_STAGE0_ALREADY_BUILT:-0}" != 1 ]]; then
    cargo build -q -p grandiose-stage0 --bin grc-stage0
fi
if [[ "${GRANDIOSE_GRVM_ALREADY_BUILT:-0}" != 1 ]]; then
    cargo build -q -p grandiose-vm --bin grvm
fi

temporary="$(mktemp -d)"
trap 'rm -rf "$temporary"' EXIT
readonly artifact="$temporary/self-host-stage1.gvm"
readonly manifest="$temporary/self-host-stage1.manifest"
readonly repeated_artifact="$temporary/self-host-stage1-repeat.gvm"
readonly repeated_manifest="$temporary/self-host-stage1-repeat.manifest"

root_source=
root_package=
runtime_package=
args=()
while IFS=$'\t' read -r package logical physical role; do
    [[ "$package" == "package" ]] && continue
    [[ "$physical" != /* && "$physical" != *".."* && -f "$root/$physical" ]] || {
        echo "self-host bootstrap artifact check: invalid source path $physical" >&2
        exit 1
    }
    if [[ "$role" == "root" ]]; then
        root_source="$root/$physical"
        root_package="$package"
    else
        args+=(--source "$package" "$logical" "$root/$physical")
        [[ "$role" == "runtime-standard-library" ]] && runtime_package="$package"
    fi
done < "$sources"

[[ -n "$root_source" && -n "$root_package" && -n "$runtime_package" ]] || {
    echo "self-host bootstrap artifact check: incomplete source manifest" >&2
    exit 1
}

"$compiler" --root-package "$root_package" "${args[@]}" \
    --runtime-standard-library "$runtime_package" \
    --runtime-leaf branch-bool crate branch_bool \
    --runtime-leaf blake3 crate __g1_blake3 \
    --runtime-leaf text-as-bytes crate __g1_text_as_bytes \
    --runtime-leaf text-eq crate __g1_text_eq \
    --runtime-leaf bytes-len crate __g1_bytes_len \
    --runtime-leaf bytes-get crate __g1_bytes_get \
    --runtime-leaf bytes-slice crate __g1_bytes_slice --runtime-leaf bytes-concat crate __g1_bytes_concat --runtime-leaf bytes-from-array-move crate __g1_bytes_from_array_move --runtime-leaf int-shr crate __g1_int_shr --runtime-leaf int-convert-wrapping-to-u32 crate __g1_int_convert_wrapping_to_u32 --runtime-leaf int-convert-wrapping-to-u64 crate __g1_int_convert_wrapping_to_u64 --runtime-leaf int-convert-wrapping-to-u8 crate __g1_int_convert_wrapping_to_u8 --runtime-leaf int-convert-checked-to-i64 crate __g1_int_convert_checked_to_i64 \
    --runtime-leaf int-wrapping-add crate __g1_int_wrapping_add \
    --runtime-leaf int-wrapping-sub crate __g1_int_wrapping_sub \
    --runtime-leaf int-wrapping-mul crate __g1_int_wrapping_mul \
    --runtime-leaf int-checked-div crate __g1_int_checked_div \
    --runtime-leaf array-empty crate __g1_array_empty --runtime-leaf array-len crate __g1_array_len --runtime-leaf array-get-move crate __g1_array_get_move \
    --runtime-leaf array-pop-move crate __g1_array_pop_move \
    --runtime-host process_args __g1_process_args_get crate process_args_get --capability process_args \
    --runtime-host file_read __g1_fs_read crate read_file --capability file_read \
    --runtime-host file_write_atomic __g1_fs_write_atomic crate write_file_atomically --capability file_write_atomic \
    --runtime-host diagnostic_write __g1_diagnostic_write crate write_diagnostic --capability diagnostic_write \
    emit-bootstrap-vm "$root_source" "$artifact" "$manifest"

"$compiler" --root-package "$root_package" "${args[@]}" \
    --runtime-standard-library "$runtime_package" \
    --runtime-leaf branch-bool crate branch_bool \
    --runtime-leaf blake3 crate __g1_blake3 \
    --runtime-leaf text-as-bytes crate __g1_text_as_bytes \
    --runtime-leaf text-eq crate __g1_text_eq \
    --runtime-leaf bytes-len crate __g1_bytes_len \
    --runtime-leaf bytes-get crate __g1_bytes_get \
    --runtime-leaf bytes-slice crate __g1_bytes_slice --runtime-leaf bytes-concat crate __g1_bytes_concat --runtime-leaf bytes-from-array-move crate __g1_bytes_from_array_move --runtime-leaf int-shr crate __g1_int_shr --runtime-leaf int-convert-wrapping-to-u32 crate __g1_int_convert_wrapping_to_u32 --runtime-leaf int-convert-wrapping-to-u64 crate __g1_int_convert_wrapping_to_u64 --runtime-leaf int-convert-wrapping-to-u8 crate __g1_int_convert_wrapping_to_u8 --runtime-leaf int-convert-checked-to-i64 crate __g1_int_convert_checked_to_i64 \
    --runtime-leaf int-wrapping-add crate __g1_int_wrapping_add \
    --runtime-leaf int-wrapping-sub crate __g1_int_wrapping_sub \
    --runtime-leaf int-wrapping-mul crate __g1_int_wrapping_mul \
    --runtime-leaf int-checked-div crate __g1_int_checked_div \
    --runtime-leaf array-empty crate __g1_array_empty --runtime-leaf array-len crate __g1_array_len --runtime-leaf array-get-move crate __g1_array_get_move \
    --runtime-leaf array-pop-move crate __g1_array_pop_move \
    --runtime-host process_args __g1_process_args_get crate process_args_get --capability process_args \
    --runtime-host file_read __g1_fs_read crate read_file --capability file_read \
    --runtime-host file_write_atomic __g1_fs_write_atomic crate write_file_atomically --capability file_write_atomic \
    --runtime-host diagnostic_write __g1_diagnostic_write crate write_diagnostic --capability diagnostic_write \
    emit-bootstrap-vm "$root_source" "$repeated_artifact" "$repeated_manifest"

[[ -s "$artifact" && -s "$manifest" && -s "$repeated_artifact" && -s "$repeated_manifest" ]] || {
    echo "self-host bootstrap artifact check: seed emitted an empty artifact or manifest" >&2
    exit 1
}

# Cross the authoritative Rust-emitted seed manifest into the source-owned
# decoder before comparing repeatability. This is a wire-compatibility gate,
# not a claim that the source compiler can yet emit the normal compiler's
# verified-program fingerprint commitments.
source_manifest_decode="$(cd "$temporary" && GRANDIOSE_STAGE0_ALREADY_BUILT=1 GRANDIOSE_STAGE0_BOOTSTRAP_PROBE="$root/self-host-stage0/probes/bootstrap_rust_manifest.glorious" GRANDIOSE_STAGE0_BOOTSTRAP_EXPECTED=2 \
    "$root/tooling/self-host-stage0-bootstrap-check.sh" \
    --runtime-host file_read __g1_fs_read crate read_file --capability file_read)"
[[ "$source_manifest_decode" == "2" ]] || {
    echo "self-host bootstrap artifact check: source decoder rejected Rust-emitted seed manifest: $source_manifest_decode" >&2
    exit 1
}

mkdir "$temporary/corrupt-manifest"
cp "$manifest" "$temporary/corrupt-manifest/self-host-stage1.manifest"
printf '\0' | dd of="$temporary/corrupt-manifest/self-host-stage1.manifest" bs=1 count=1 conv=notrunc status=none
source_corrupt_manifest="$(cd "$temporary/corrupt-manifest" && GRANDIOSE_STAGE0_ALREADY_BUILT=1 GRANDIOSE_STAGE0_BOOTSTRAP_PROBE="$root/self-host-stage0/probes/bootstrap_rust_manifest.glorious" GRANDIOSE_STAGE0_BOOTSTRAP_EXPECTED=0 \
    "$root/tooling/self-host-stage0-bootstrap-check.sh" \
    --runtime-host file_read __g1_fs_read crate read_file --capability file_read)"
[[ "$source_corrupt_manifest" == "0" ]] || {
    echo "self-host bootstrap artifact check: source decoder accepted corrupted Rust manifest: $source_corrupt_manifest" >&2
    exit 1
}

cmp -s "$artifact" "$repeated_artifact" || {
    echo "self-host bootstrap artifact check: repeated seed emissions differ" >&2
    exit 1
}
cmp -s "$manifest" "$repeated_manifest" || {
    echo "self-host bootstrap artifact check: repeated seed manifests differ" >&2
    exit 1
}

fingerprint="$("$compiler" verify-vm "$artifact")"
[[ -n "$fingerprint" ]] || {
    echo "self-host bootstrap artifact check: independent verifier produced no fingerprint" >&2
    exit 1
}
stage_output="$("$compiler" run-vm "$artifact")"
[[ "$stage_output" == "148" ]] || {
    echo "self-host bootstrap artifact check: emitted stage did not execute the canonical source-world entrypoint: $stage_output" >&2
    exit 1
}
printf '%s\n' 'pub fn main() -> i64 { 40 + 2 }' > "$temporary/stage-input.glorious"
stage_driver_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 emit-vm "$temporary/stage-input.glorious" "$temporary/stage-output.grbc")"
[[ "$stage_driver_output" == "0" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not accept explicit guest argv: $stage_driver_output" >&2
    exit 1
}
[[ "$(wc -c < "$temporary/stage-output.grbc")" == "1280" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not publish the expected G1 arithmetic artifact" >&2
    exit 1
}
"$grvm" verify "$temporary/stage-output.grbc"
"$grvm" run "$temporary/stage-output.grbc"
printf '%s\n' 'pub fn main() -> i64 { return 40 + 2; }' > "$temporary/stage-return-input.glorious"
stage_return_run="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 run "$temporary/stage-return-input.glorious")"
[[ "$stage_return_run" == "42" ]] || {
    echo "self-host bootstrap artifact check: stage run did not evaluate explicit return arithmetic: $stage_return_run" >&2
    exit 1
}
stage_return_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 emit-vm "$temporary/stage-return-input.glorious" "$temporary/stage-return-output.grbc")"
[[ "$stage_return_output" == "0" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not accept explicit return arithmetic: $stage_return_output" >&2
    exit 1
}
[[ "$(wc -c < "$temporary/stage-return-output.grbc")" == "1280" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not preserve the explicit-return binary artifact" >&2
    exit 1
}
"$grvm" verify "$temporary/stage-return-output.grbc"
[[ "$("$grvm" run "$temporary/stage-return-output.grbc")" == "42" ]] || {
    echo "self-host bootstrap artifact check: stage driver's explicit-return artifact produced the wrong result" >&2
    exit 1
}
printf '%s\n' 'pub fn main() -> i64 { return if false { 7 } else { 42 }; }' > "$temporary/stage-return-select-input.glorious"
stage_return_select_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 emit-vm "$temporary/stage-return-select-input.glorious" "$temporary/stage-return-select-output.grbc")"
[[ "$stage_return_select_output" == "0" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not accept explicit-return conditional: $stage_return_select_output" >&2
    exit 1
}
[[ "$(wc -c < "$temporary/stage-return-select-output.grbc")" == "1168" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not preserve the explicit-return conditional artifact" >&2
    exit 1
}
"$grvm" verify "$temporary/stage-return-select-output.grbc"
[[ "$("$grvm" run "$temporary/stage-return-select-output.grbc")" == "42" ]] || {
    echo "self-host bootstrap artifact check: stage driver's explicit-return conditional artifact produced the wrong result" >&2
    exit 1
}
printf '%s\n' 'pub fn main() -> i64 { return if false { 7 } else { 42 } }' > "$temporary/stage-return-select-invalid-input.glorious"
stage_return_select_invalid_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 emit-vm "$temporary/stage-return-select-invalid-input.glorious" "$temporary/stage-return-select-invalid-output.grbc")"
[[ "$stage_return_select_invalid_output" == "1" ]] || {
    echo "self-host bootstrap artifact check: stage driver accepted unterminated explicit-return conditional: $stage_return_select_invalid_output" >&2
    exit 1
}
[[ ! -e "$temporary/stage-return-select-invalid-output.grbc" ]] || {
    echo "self-host bootstrap artifact check: unterminated explicit-return conditional published an artifact" >&2
    exit 1
}
check_stage_return_binary() {
    local name="$1"
    local body="$2"
    local expected="$3"
    local input="$temporary/stage-return-$name-input.glorious"
    local output="$temporary/stage-return-$name-output.grbc"
    printf 'pub fn main() -> i64 { return %s; }\n' "$body" > "$input"
    local driver_output
    driver_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 emit-vm "$input" "$output")"
    [[ "$driver_output" == "0" ]] || { echo "self-host bootstrap artifact check: stage driver rejected return $body: $driver_output" >&2; exit 1; }
    [[ "$(wc -c < "$output")" == "1280" ]] || { echo "self-host bootstrap artifact check: stage driver did not preserve return $body as a binary artifact" >&2; exit 1; }
    "$grvm" verify "$output"
    [[ "$("$grvm" run "$output")" == "$expected" ]] || { echo "self-host bootstrap artifact check: return $body produced the wrong result" >&2; exit 1; }
}
check_stage_return_binary subtract '44 - 2' 42
check_stage_return_binary multiply '6 * 7' 42
check_stage_return_binary divide '84 / 2' 42
printf '%s\n' 'pub fn main() -> i64 { return 42 / 0; }' > "$temporary/stage-return-divide-zero-input.glorious"
stage_return_divide_zero_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 emit-vm "$temporary/stage-return-divide-zero-input.glorious" "$temporary/stage-return-divide-zero-output.grbc")"
[[ "$stage_return_divide_zero_output" == "1" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not reject explicit-return division by zero: $stage_return_divide_zero_output" >&2
    exit 1
}
[[ ! -e "$temporary/stage-return-divide-zero-output.grbc" ]] || {
    echo "self-host bootstrap artifact check: rejected explicit-return division by zero published an artifact" >&2
    exit 1
}
printf '%s\n' 'pub fn main() -> Unit { return (); }' > "$temporary/stage-unit-input.glorious"
stage_unit_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 emit-vm "$temporary/stage-unit-input.glorious" "$temporary/stage-unit-output.grbc")"
[[ "$stage_unit_output" == "0" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not emit a canonical Unit entry: $stage_unit_output" >&2
    exit 1
}
stage_verify_unit_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 verify-vm "$temporary/stage-unit-output.grbc")"
[[ "$stage_verify_unit_output" == "0" ]] || {
    echo "self-host bootstrap artifact check: source verifier rejected its canonical Unit artifact: $stage_verify_unit_output" >&2
    exit 1
}
printf '%s\n' 'pub fn main() -> i64 { 42 }' > "$temporary/stage-scalar-input.glorious"
stage_scalar_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 emit-vm "$temporary/stage-scalar-input.glorious" "$temporary/stage-scalar-output.grbc")"
[[ "$stage_scalar_output" == "0" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not emit a canonical scalar entry: $stage_scalar_output" >&2
    exit 1
}
stage_verify_scalar_entry_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 verify-vm "$temporary/stage-scalar-output.grbc")"
[[ "$stage_verify_scalar_entry_output" == "0" ]] || {
    echo "self-host bootstrap artifact check: source verifier rejected its canonical scalar artifact: $stage_verify_scalar_entry_output" >&2
    exit 1
}
cp "$temporary/stage-scalar-output.grbc" "$temporary/stage-corrupt-scalar-output.grbc"
printf '\0' | dd of="$temporary/stage-corrupt-scalar-output.grbc" bs=1 seek=0 conv=notrunc status=none
stage_verify_corrupt_scalar_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 verify-vm "$temporary/stage-corrupt-scalar-output.grbc" 2>"$temporary/stage-verify-corrupt-scalar.stderr")"
[[ "$stage_verify_corrupt_scalar_output" == "1" ]] || {
    echo "self-host bootstrap artifact check: source verifier accepted a corrupted scalar artifact: $stage_verify_corrupt_scalar_output" >&2
    exit 1
}
grep -Fq 'self-host verify-vm rejected' "$temporary/stage-verify-corrupt-scalar.stderr" || {
    echo "self-host bootstrap artifact check: corrupted scalar rejection lacked a source-owned diagnostic" >&2
    exit 1
}
stage_verify_binary_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 verify-vm "$temporary/stage-output.grbc")"
[[ "$stage_verify_binary_output" == "0" ]] || {
    echo "self-host bootstrap artifact check: source verifier rejected its canonical binary artifact: $stage_verify_binary_output" >&2
    exit 1
}
cp "$temporary/stage-output.grbc" "$temporary/stage-corrupt-binary-output.grbc"
printf '\0' | dd of="$temporary/stage-corrupt-binary-output.grbc" bs=1 seek=1084 conv=notrunc status=none
stage_verify_corrupt_binary_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 verify-vm "$temporary/stage-corrupt-binary-output.grbc" 2>"$temporary/stage-verify-corrupt-binary.stderr")"
[[ "$stage_verify_corrupt_binary_output" == "1" ]] || {
    echo "self-host bootstrap artifact check: source verifier accepted a corrupted binary opcode: $stage_verify_corrupt_binary_output" >&2
    exit 1
}
grep -Fq 'self-host verify-vm rejected' "$temporary/stage-verify-corrupt-binary.stderr" || {
    echo "self-host bootstrap artifact check: corrupted binary rejection lacked a source-owned diagnostic" >&2
    exit 1
}
printf '%s\n' 'pub fn main() -> i64 { 44 - 2 }' > "$temporary/stage-subtract-input.glorious"
stage_subtract_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 emit-vm "$temporary/stage-subtract-input.glorious" "$temporary/stage-subtract-output.grbc")"
[[ "$stage_subtract_output" == "0" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not accept source subtraction: $stage_subtract_output" >&2
    exit 1
}
"$grvm" verify "$temporary/stage-subtract-output.grbc"
[[ "$("$grvm" run "$temporary/stage-subtract-output.grbc")" == "42" ]] || {
    echo "self-host bootstrap artifact check: emitted subtraction artifact returned the wrong value" >&2
    exit 1
}
[[ "$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 verify-vm "$temporary/stage-subtract-output.grbc")" == "0" ]] || {
    echo "self-host bootstrap artifact check: source verifier rejected its subtraction artifact" >&2
    exit 1
}
printf '%s\n' 'pub fn main() -> i64 { 6 * 7 }' > "$temporary/stage-multiply-input.glorious"
stage_multiply_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 emit-vm "$temporary/stage-multiply-input.glorious" "$temporary/stage-multiply-output.grbc")"
[[ "$stage_multiply_output" == "0" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not accept source multiplication: $stage_multiply_output" >&2
    exit 1
}
"$grvm" verify "$temporary/stage-multiply-output.grbc"
[[ "$("$grvm" run "$temporary/stage-multiply-output.grbc")" == "42" ]] || {
    echo "self-host bootstrap artifact check: emitted multiplication artifact returned the wrong value" >&2
    exit 1
}
[[ "$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 verify-vm "$temporary/stage-multiply-output.grbc")" == "0" ]] || {
    echo "self-host bootstrap artifact check: source verifier rejected its multiplication artifact" >&2
    exit 1
}
printf '%s\n' 'pub fn main() -> i64 { 84 / 2 }' > "$temporary/stage-divide-input.glorious"
stage_divide_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 emit-vm "$temporary/stage-divide-input.glorious" "$temporary/stage-divide-output.grbc")"
[[ "$stage_divide_output" == "0" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not accept source division: $stage_divide_output" >&2
    exit 1
}
"$grvm" verify "$temporary/stage-divide-output.grbc"
[[ "$("$grvm" run "$temporary/stage-divide-output.grbc")" == "42" ]] || {
    echo "self-host bootstrap artifact check: emitted division artifact returned the wrong value" >&2
    exit 1
}
[[ "$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 verify-vm "$temporary/stage-divide-output.grbc")" == "0" ]] || {
    echo "self-host bootstrap artifact check: source verifier rejected its division artifact" >&2
    exit 1
}
printf '%s\n' 'pub fn main() -> i64 { 21 + 21 }' > "$temporary/stage-duplicate-input.glorious"
stage_duplicate_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 emit-vm "$temporary/stage-duplicate-input.glorious" "$temporary/stage-duplicate-output.grbc")"
[[ "$stage_duplicate_output" == "0" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not emit a duplicate-constant binary artifact: $stage_duplicate_output" >&2
    exit 1
}
[[ "$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 verify-vm "$temporary/stage-duplicate-output.grbc")" == "0" ]] || {
    echo "self-host bootstrap artifact check: source verifier rejected its duplicate-constant binary artifact" >&2
    exit 1
}
[[ "$("$grvm" run "$temporary/stage-duplicate-output.grbc")" == "42" ]] || {
    echo "self-host bootstrap artifact check: emitted duplicate-constant artifact returned the wrong value" >&2
    exit 1
}
printf '%s\n' 'pub fn main() -> i64 { 42 / 0 }' > "$temporary/stage-zero-divide-input.glorious"
stage_zero_divide_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 emit-vm "$temporary/stage-zero-divide-input.glorious" "$temporary/stage-zero-divide-output.grbc" 2>"$temporary/stage-zero-divide.stderr")"
[[ "$stage_zero_divide_output" == "1" ]] || {
    echo "self-host bootstrap artifact check: stage driver accepted source division by zero: $stage_zero_divide_output" >&2
    exit 1
}
grep -Fq 'self-host emit-vm rejected' "$temporary/stage-zero-divide.stderr" || {
    echo "self-host bootstrap artifact check: source division by zero lacked a source-owned rejection" >&2
    exit 1
}
[[ ! -e "$temporary/stage-zero-divide-output.grbc" ]] || {
    echo "self-host bootstrap artifact check: source division by zero published an artifact" >&2
    exit 1
}
printf '%s\n' 'pub fn main() -> i64 { if false { 7 } else { 9 } }' > "$temporary/stage-select-input.glorious"
stage_select_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 emit-vm "$temporary/stage-select-input.glorious" "$temporary/stage-select-output.grbc")"
[[ "$stage_select_output" == "0" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not accept the literal conditional form: $stage_select_output" >&2
    exit 1
}
[[ "$(wc -c < "$temporary/stage-select-output.grbc")" == "1168" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not publish the expected G1 conditional artifact" >&2
    exit 1
}
"$grvm" verify "$temporary/stage-select-output.grbc"
"$grvm" run "$temporary/stage-select-output.grbc"
stage_check_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 check "$temporary/stage-input.glorious")"
[[ "$stage_check_output" == "0" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not accept the file-backed check request: $stage_check_output" >&2
    exit 1
}
printf '%s\n' "pub fn helper() -> i64 { 42 } '" > "$temporary/stage-invalid-check-input.glorious"
stage_invalid_check_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 check "$temporary/stage-invalid-check-input.glorious" 2>"$temporary/stage-invalid-check.stderr")"
[[ "$stage_invalid_check_output" == "1" ]] || {
    echo "self-host bootstrap artifact check: check accepted trailing malformed source: $stage_invalid_check_output" >&2
    exit 1
}
grep -Fq 'self-host check rejected' "$temporary/stage-invalid-check.stderr" || {
    echo "self-host bootstrap artifact check: malformed check input lacked a source-owned diagnostic" >&2
    exit 1
}
printf '%s\n' 'pub fn main() -> i64 { 42 }' > "$temporary/stage-run-input.glorious"
stage_run_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 run "$temporary/stage-run-input.glorious")"
[[ "$stage_run_output" == "42" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not execute the file-backed i64 function: $stage_run_output" >&2
    exit 1
}
printf '%s\n' 'pub fn main() -> u32 { return 4294967295 - 0; }' > "$temporary/stage-u32-maximum-run-input.glorious"
stage_u32_maximum_run_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 run "$temporary/stage-u32-maximum-run-input.glorious")"
[[ "$stage_u32_maximum_run_output" == "4294967295" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not preserve u32::MAX through its explicit i64 result protocol: $stage_u32_maximum_run_output" >&2
    exit 1
}
printf '%s\n' 'pub fn main() -> u32 { return 42; }' > "$temporary/stage-u32-literal-run-input.glorious"
stage_u32_literal_run_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 run "$temporary/stage-u32-literal-run-input.glorious")"
[[ "$stage_u32_literal_run_output" == "42" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not execute a u32 literal return: $stage_u32_literal_run_output" >&2
    exit 1
}
printf '%s\n' 'pub fn main() -> u32 { return 85 % 43; }' > "$temporary/stage-u32-remainder-run-input.glorious"
stage_u32_remainder_run_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 run "$temporary/stage-u32-remainder-run-input.glorious")"
[[ "$stage_u32_remainder_run_output" == "42" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not execute checked u32 remainder: $stage_u32_remainder_run_output" >&2
    exit 1
}
printf '%s\n' 'pub fn main() -> i64 { 2 + -5 }' > "$temporary/stage-negative-run-input.glorious"
stage_negative_run_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 run "$temporary/stage-negative-run-input.glorious")"
[[ "$stage_negative_run_output" == "-3" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not execute a signed i64 literal: $stage_negative_run_output" >&2
    exit 1
}
stage_negative_emit_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 emit-vm "$temporary/stage-negative-run-input.glorious" "$temporary/stage-negative-output.grbc")"
[[ "$stage_negative_emit_output" == "0" && "$(wc -c < "$temporary/stage-negative-output.grbc")" == "1280" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not retain signed operands in a G1 binary artifact" >&2
    exit 1
}
[[ "$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 verify-vm "$temporary/stage-negative-output.grbc")" == "0" ]] || {
    echo "self-host bootstrap artifact check: source verifier rejected its signed binary artifact" >&2
    exit 1
}
printf '%s\n' 'pub fn main() -> i64 { -9223372036854775808 }' > "$temporary/stage-i64-minimum-run-input.glorious"
stage_i64_minimum_run_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 run "$temporary/stage-i64-minimum-run-input.glorious")"
[[ "$stage_i64_minimum_run_output" == "-9223372036854775808" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not preserve i64::MIN: $stage_i64_minimum_run_output" >&2
    exit 1
}
printf '%s\n' 'pub fn main() -> i64 { -9223372036854775809 }' > "$temporary/stage-i64-overflow-run-input.glorious"
stage_i64_overflow_run_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 run "$temporary/stage-i64-overflow-run-input.glorious" 2>"$temporary/stage-i64-overflow-run.stderr")"
[[ "$stage_i64_overflow_run_output" == "1" ]] || {
    echo "self-host bootstrap artifact check: stage driver accepted signed i64 overflow: $stage_i64_overflow_run_output" >&2
    exit 1
}
grep -Fq 'self-host run rejected' "$temporary/stage-i64-overflow-run.stderr" || {
    echo "self-host bootstrap artifact check: signed i64 overflow lacked a source-owned rejection" >&2
    exit 1
}
printf '%s\n' 'pub fn helper() -> i64 { 42 }' > "$temporary/stage-non-entry-input.glorious"
stage_non_entry_run_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 run "$temporary/stage-non-entry-input.glorious" 2>"$temporary/stage-non-entry-run.stderr")"
[[ "$stage_non_entry_run_output" == "1" ]] || {
    echo "self-host bootstrap artifact check: run accepted a non-main declaration: $stage_non_entry_run_output" >&2
    exit 1
}
grep -Fq 'self-host run rejected' "$temporary/stage-non-entry-run.stderr" || {
    echo "self-host bootstrap artifact check: non-main run did not produce a source-owned rejection" >&2
    exit 1
}
stage_non_entry_emit_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 emit-vm "$temporary/stage-non-entry-input.glorious" "$temporary/stage-non-entry-output.grbc" 2>"$temporary/stage-non-entry-emit.stderr")"
[[ "$stage_non_entry_emit_output" == "1" ]] || {
    echo "self-host bootstrap artifact check: emit-vm accepted a non-main declaration: $stage_non_entry_emit_output" >&2
    exit 1
}
grep -Fq 'self-host emit-vm rejected' "$temporary/stage-non-entry-emit.stderr" || {
    echo "self-host bootstrap artifact check: non-main emit-vm did not produce a source-owned rejection" >&2
    exit 1
}
[[ ! -e "$temporary/stage-non-entry-output.grbc" ]] || {
    echo "self-host bootstrap artifact check: non-main declaration published an artifact" >&2
    exit 1
}
stage_select_run_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 run "$temporary/stage-select-input.glorious")"
[[ "$stage_select_run_output" == "9" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not execute the file-backed conditional function: $stage_select_run_output" >&2
    exit 1
}
printf '%s\n' 'pub fn main() -> i64 { if true { -7 } else { 9 } }' > "$temporary/stage-signed-select-run-input.glorious"
stage_signed_select_run_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 run "$temporary/stage-signed-select-run-input.glorious")"
[[ "$stage_signed_select_run_output" == "-7" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not execute signed conditional branches: $stage_signed_select_run_output" >&2
    exit 1
}
printf '%s\n' 'pub fn main() -> Bool { -7 < 3 }' > "$temporary/stage-signed-comparison-run-input.glorious"
stage_signed_comparison_run_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 run "$temporary/stage-signed-comparison-run-input.glorious")"
[[ "$stage_signed_comparison_run_output" == "1" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not execute signed comparison literals: $stage_signed_comparison_run_output" >&2
    exit 1
}
printf '%s\n' 'pub fn main() -> Bool { false }' > "$temporary/stage-bool-run-input.glorious"
stage_bool_run_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 run "$temporary/stage-bool-run-input.glorious")"
[[ "$stage_bool_run_output" == "0" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not execute the strict file-backed Bool function: $stage_bool_run_output" >&2
    exit 1
}
printf '%s\n' 'pub fn main() -> Bool { !false }' > "$temporary/stage-bool-not-run-input.glorious"
stage_bool_not_run_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 run "$temporary/stage-bool-not-run-input.glorious")"
[[ "$stage_bool_not_run_output" == "1" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not execute strict file-backed Bool negation: $stage_bool_not_run_output" >&2
    exit 1
}
printf '%s\n' 'pub fn main() -> Bool { !true }' > "$temporary/stage-bool-not-true-run-input.glorious"
stage_bool_not_true_run_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 run "$temporary/stage-bool-not-true-run-input.glorious")"
[[ "$stage_bool_not_true_run_output" == "0" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not preserve strict Bool negation truth value: $stage_bool_not_true_run_output" >&2
    exit 1
}
printf '%s\n' 'pub fn main() -> Bool { 7 > 3 }' > "$temporary/stage-comparison-run-input.glorious"
stage_comparison_run_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 run "$temporary/stage-comparison-run-input.glorious")"
[[ "$stage_comparison_run_output" == "1" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not execute strict file-backed i64 comparison: $stage_comparison_run_output" >&2
    exit 1
}
printf '%s\n' 'pub fn main() -> Bool { 7 < 3 }' > "$temporary/stage-comparison-false-run-input.glorious"
stage_comparison_false_run_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 run "$temporary/stage-comparison-false-run-input.glorious")"
[[ "$stage_comparison_false_run_output" == "0" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not preserve strict i64 comparison truth value: $stage_comparison_false_run_output" >&2
    exit 1
}
printf '%s\n' 'pub fn main() -> Bool { 7 > }' > "$temporary/stage-comparison-invalid-run-input.glorious"
stage_comparison_invalid_run_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 run "$temporary/stage-comparison-invalid-run-input.glorious" 2>"$temporary/stage-comparison-invalid-run.stderr")"
[[ "$stage_comparison_invalid_run_output" == "1" ]] || {
    echo "self-host bootstrap artifact check: malformed i64 comparison was accepted: $stage_comparison_invalid_run_output" >&2
    exit 1
}
grep -Fq 'self-host run rejected' "$temporary/stage-comparison-invalid-run.stderr" || {
    echo "self-host bootstrap artifact check: malformed i64 comparison did not produce a source-owned rejection" >&2
    exit 1
}
printf '%s\n' 'pub fn main() -> i64 { 40 + }' > "$temporary/stage-invalid-input.glorious"
stage_invalid_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 emit-vm "$temporary/stage-invalid-input.glorious" "$temporary/stage-invalid-output.grbc" 2>"$temporary/stage-invalid.stderr")"
[[ "$stage_invalid_output" == "1" ]] || {
    echo "self-host bootstrap artifact check: stage driver did not report rejected input: $stage_invalid_output" >&2
    exit 1
}
grep -Fq 'self-host emit-vm rejected' "$temporary/stage-invalid.stderr" || {
    echo "self-host bootstrap artifact check: stage driver did not emit its source-owned rejection diagnostic" >&2
    exit 1
}
[[ ! -e "$temporary/stage-invalid-output.grbc" ]] || {
    echo "self-host bootstrap artifact check: rejected stage input published an artifact" >&2
    exit 1
}
stage_invalid_package_output="$("$compiler" run-vm "$artifact" -- --root-package 9lives@0.1.0 emit-vm "$temporary/stage-input.glorious" "$temporary/stage-invalid-package-output.grbc" 2>"$temporary/stage-invalid-package.stderr")"
[[ "$stage_invalid_package_output" == "1" ]] || {
    echo "self-host bootstrap artifact check: invalid package alias was accepted: $stage_invalid_package_output" >&2
    exit 1
}
grep -Fq 'self-host emit-vm rejected' "$temporary/stage-invalid-package.stderr" || {
    echo "self-host bootstrap artifact check: invalid package alias did not produce a source-owned rejection" >&2
    exit 1
}
[[ ! -e "$temporary/stage-invalid-package-output.grbc" ]] || {
    echo "self-host bootstrap artifact check: invalid package alias published an artifact" >&2
    exit 1
}
stage_invalid_package_check_output="$("$compiler" run-vm "$artifact" -- --root-package 9lives@0.1.0 check "$temporary/stage-input.glorious" 2>"$temporary/stage-invalid-package-check.stderr")"
[[ "$stage_invalid_package_check_output" == "1" ]] || {
    echo "self-host bootstrap artifact check: invalid package alias was accepted by check: $stage_invalid_package_check_output" >&2
    exit 1
}
grep -Fq 'self-host check rejected' "$temporary/stage-invalid-package-check.stderr" || {
    echo "self-host bootstrap artifact check: invalid package alias check did not produce a source-owned rejection" >&2
    exit 1
}
stage_invalid_package_run_output="$("$compiler" run-vm "$artifact" -- --root-package 9lives@0.1.0 run "$temporary/stage-run-input.glorious" 2>"$temporary/stage-invalid-package-run.stderr")"
[[ "$stage_invalid_package_run_output" == "1" ]] || {
    echo "self-host bootstrap artifact check: invalid package alias was accepted by run: $stage_invalid_package_run_output" >&2
    exit 1
}
grep -Fq 'self-host run rejected' "$temporary/stage-invalid-package-run.stderr" || {
    echo "self-host bootstrap artifact check: invalid package alias run did not produce a source-owned rejection" >&2
    exit 1
}
printf '%s\n' 'pub fn main() -> Bool { false } trailing' > "$temporary/stage-unsupported-bool-run.glorious"
stage_unsupported_bool_output="$("$compiler" run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 run "$temporary/stage-unsupported-bool-run.glorious" 2>"$temporary/stage-unsupported-bool.stderr")"
[[ "$stage_unsupported_bool_output" == "1" ]] || {
    echo "self-host bootstrap artifact check: unsupported Bool run was accepted: $stage_unsupported_bool_output" >&2
    exit 1
}
grep -Fq 'self-host run rejected' "$temporary/stage-unsupported-bool.stderr" || {
    echo "self-host bootstrap artifact check: unsupported Bool run did not report its source-owned diagnostic" >&2
    exit 1
}
stage_unsupported_command_output="$("$compiler" run-vm "$artifact" -- verify-vm "$temporary/stage-output.grbc" 2>"$temporary/stage-unsupported-command.stderr")"
[[ "$stage_unsupported_command_output" == "1" ]] || {
    echo "self-host bootstrap artifact check: unsupported command was accepted: $stage_unsupported_command_output" >&2
    exit 1
}
grep -Fq 'self-host command not implemented' "$temporary/stage-unsupported-command.stderr" || {
    echo "self-host bootstrap artifact check: unsupported command did not report its source-owned diagnostic" >&2
    exit 1
}
printf '%s\n' "$fingerprint"
