#!/usr/bin/env bash
# Turn retained native stage-1 evidence into the native stage-2 compiler.
#
# This is the bridge between self-host-native-stage1.sh and the convergence
# checker.  It accepts only the immutable stage-1 evidence directory, lowers
# its exact verified stage2.grbc through the fail-closed AOT boundary, then
# writes provenance which binds the resulting executable back to those bytes.
# It never executes stage-two bytecode.
set -euo pipefail

usage() {
    cat >&2 <<'USAGE'
usage: tooling/self-host-native-stage2.sh run --stage1-dir DIR [--output-dir DIR]

Consumes the retained output of self-host-native-stage1.sh.  It verifies the
recorded source and stage2 artifact hashes, lowers that exact artifact with
release grvm/grc through grbc-native.sh, and retains a native executable plus
stage-2 provenance.  Output directories are never overwritten.
USAGE
    exit 2
}

readonly script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
readonly repo_root="$(cd -- "$script_dir/.." && pwd -P)"
readonly grbc_native="$repo_root/tooling/grbc-native.sh"
readonly write_provenance="$repo_root/tooling/write-native-stage-provenance.sh"
readonly grvm="$repo_root/target/release/grvm"
readonly grc="$repo_root/target/release/grc"

command=${1:-}
[[ "$command" == run ]] || usage
shift
stage1_dir=
output_dir=
while (($#)); do
    case "$1" in
        --stage1-dir) stage1_dir=${2:?missing value}; shift 2 ;;
        --output-dir) output_dir=${2:?missing value}; shift 2 ;;
        -h|--help) usage ;;
        *) usage ;;
    esac
done
[[ -n "$stage1_dir" ]] || usage
[[ -d "$stage1_dir" ]] || { echo "native-stage2: stage-1 evidence directory is missing: $stage1_dir" >&2; exit 2; }
[[ -x "$grbc_native" && -x "$write_provenance" ]] || {
    echo "native-stage2: required tooling is not executable" >&2
    exit 2
}
[[ -x "$grvm" ]] || { echo "native-stage2: release grvm is missing: $grvm" >&2; exit 2; }
[[ -x "$grc" ]] || { echo "native-stage2: release grc is missing: $grc" >&2; exit 2; }

if [[ -z "$output_dir" ]]; then
    mkdir -p "$repo_root/target/self-host-native-stage2"
    output_dir="$(mktemp -d "$repo_root/target/self-host-native-stage2/run.XXXXXX")"
elif [[ -e "$output_dir" || -L "$output_dir" ]]; then
    echo "native-stage2: refusing to overwrite retained evidence: $output_dir" >&2
    exit 2
else
    mkdir -p "$output_dir"
fi
readonly output_dir
readonly source="$stage1_dir/canonical-source.glorious"
readonly stage1_metadata="$stage1_dir/metadata.tsv"
readonly stage1_provenance="$stage1_dir/stage1-provenance.tsv"
readonly stage2_artifact="$stage1_dir/stage2.grbc"
readonly native="$output_dir/stage2-native"
readonly provenance="$output_dir/stage2-provenance.tsv"
readonly metadata="$output_dir/metadata.tsv"

printf 'artifacts\t%s\n' "$output_dir" >&2

manifest_value() {
    local manifest=$1 key=$2 value
    value=$(awk -F '\t' -v key="$key" '$1 == key { if (++found > 1) exit 2; print $2 } END { exit(found == 1 ? 0 : 1) }' "$manifest") || return 1
    [[ -n "$value" ]] || return 1
    printf '%s\n' "$value"
}

record_failure() {
    local phase=$1 status=$2
    printf 'schema\t1\nphase\t%s\nexit\t%s\nresult\tfailed\n' "$phase" "$status" > "$metadata"
    echo "native-stage2: $phase failed; retained evidence: $output_dir" >&2
    exit "$status"
}

run_logged() {
    local phase=$1
    shift
    set +e
    LC_ALL=C TZ=UTC "$@" >"$output_dir/$phase.log" 2>&1
    local status=$?
    set -e
    [[ $status -eq 0 ]] || record_failure "$phase" "$status"
}

[[ -s "$source" && -s "$stage1_metadata" && -s "$stage1_provenance" && -s "$stage2_artifact" ]] || record_failure input 1
schema=$(manifest_value "$stage1_metadata" schema) || record_failure input 1
stage1_exit=$(manifest_value "$stage1_metadata" stage1-exit) || record_failure input 1
result=$(manifest_value "$stage1_metadata" result) || record_failure input 1
recorded_source=$(manifest_value "$stage1_metadata" source-sha256) || record_failure input 1
recorded_stage2=$(manifest_value "$stage1_metadata" stage2-sha256) || record_failure input 1
[[ "$schema" == 1 && "$stage1_exit" == 0 && "$result" == emitted ]] || record_failure input 1
[[ "$recorded_source" == "$(sha256sum "$source" | awk '{print $1}')" ]] || record_failure input 1
[[ "$recorded_stage2" == "$(sha256sum "$stage2_artifact" | awk '{print $1}')" ]] || record_failure input 1

# Recheck the stage-1 manifest before using it as the provenance root.  The
# stage-1 runner already validated the native file, but this makes a copied or
# hand-edited retained directory unable to silently become stage-2 input.
provenance_schema=$(manifest_value "$stage1_provenance" schema) || record_failure input 1
provenance_stage=$(manifest_value "$stage1_provenance" stage) || record_failure input 1
provenance_optimization=$(manifest_value "$stage1_provenance" optimization) || record_failure input 1
provenance_linker=$(manifest_value "$stage1_provenance" linker) || record_failure input 1
provenance_source=$(manifest_value "$stage1_provenance" source-sha256) || record_failure input 1
[[ "$provenance_schema" == 1 && "$provenance_stage" == 1 && "$provenance_optimization" == O3 && "$provenance_linker" == wild ]] || record_failure input 1
[[ "$provenance_source" == "$recorded_source" ]] || record_failure input 1

# grbc-native.sh is the only .grbc -> native boundary.  It uses native-preflight
# (not VM execution), lowers via release grc, and invokes clang at O3/Wild.
run_logged lower "$grbc_native" --artifact "$stage2_artifact" --output "$native" --grvm "$grvm" --grc "$grc"
[[ -x "$native" ]] || record_failure lower 1
run_logged provenance "$write_provenance" --stage 2 --native "$native" --source "$source" \
    --compiler-bytecode "$stage2_artifact" --output "$provenance"
[[ -s "$provenance" ]] || record_failure provenance 1

printf 'schema\t1\n' > "$metadata"
printf 'stage1-dir\t%s\nsource-sha256\t%s\nstage2-artifact\t%s\nstage2-sha256\t%s\n' \
    "$stage1_dir" "$recorded_source" "$stage2_artifact" "$recorded_stage2" >> "$metadata"
printf 'stage2-native\t%s\nstage2-native-sha256\t%s\nstage2-provenance\t%s\nresult\tnative\n' \
    "$native" "$(sha256sum "$native" | awk '{print $1}')" "$provenance" >> "$metadata"
printf 'STAGE2_NATIVE\tstage2=%s\tnative=%s\tartifacts=%s\n' "$recorded_stage2" "$native" "$output_dir"
