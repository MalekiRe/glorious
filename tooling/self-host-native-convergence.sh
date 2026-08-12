#!/usr/bin/env bash
# Verify one native self-host bootstrap step reaches a byte-identical fixed point.
#
# The two compiler stages are deliberately supplied as executables.  This tool
# never starts grvm (or accepts a .grbc file as a runnable compiler): callers
# must first produce native, Wild-linked O3 hosts for both stages.  That keeps a
# failed native bootstrap from being accidentally reported as VM convergence.
set -euo pipefail

usage() {
    cat >&2 <<'USAGE'
usage: tooling/self-host-native-convergence.sh \
  --stage1-native FILE --stage1-provenance FILE \
  --stage2-native FILE --stage2-provenance FILE \
  --source FILE [--output-dir DIR]

Runs the stage-1 native compiler on SOURCE to produce stage2.grbc, verifies
that this exact artifact is the bytecode recorded for the supplied stage-2
native compiler, then runs stage 2 to produce stage3.grbc. Both native hosts
must have a checked provenance manifest binding the executable SHA-256,
optimization=O3, and linker=wild. The output directory is retained on success
and failure and contains hashes, logs, and a bounded first-difference report.
USAGE
    exit 2
}

readonly script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
readonly repo_root="$(cd -- "$script_dir/.." && pwd -P)"

stage1_native=
stage1_provenance=
stage2_native=
stage2_provenance=
source_file=
output_dir=

while (($#)); do
    case "$1" in
        --stage1-native) stage1_native=${2:?missing value}; shift 2 ;;
        --stage1-provenance) stage1_provenance=${2:?missing value}; shift 2 ;;
        --stage2-native) stage2_native=${2:?missing value}; shift 2 ;;
        --stage2-provenance) stage2_provenance=${2:?missing value}; shift 2 ;;
        --source) source_file=${2:?missing value}; shift 2 ;;
        --output-dir) output_dir=${2:?missing value}; shift 2 ;;
        -h|--help) usage ;;
        *) usage ;;
    esac
done

[[ -n "$stage1_native" && -n "$stage1_provenance" && -n "$stage2_native" && -n "$stage2_provenance" && -n "$source_file" ]] || usage
[[ -x "$stage1_native" ]] || { echo "native-convergence: stage 1 is not executable: $stage1_native" >&2; exit 2; }
[[ -x "$stage2_native" ]] || { echo "native-convergence: stage 2 is not executable: $stage2_native" >&2; exit 2; }
[[ -f "$source_file" ]] || { echo "native-convergence: source does not exist: $source_file" >&2; exit 2; }

if [[ -z "$output_dir" ]]; then
    mkdir -p "$repo_root/target/self-host-native-convergence"
    output_dir="$(mktemp -d "$repo_root/target/self-host-native-convergence/run.XXXXXX")"
elif [[ -e "$output_dir" ]]; then
    [[ -d "$output_dir" ]] || { echo "native-convergence: output path is not a directory: $output_dir" >&2; exit 2; }
    [[ -z "$(find "$output_dir" -mindepth 1 -maxdepth 1 -print -quit)" ]] || {
        echo "native-convergence: refusing to overwrite retained evidence in: $output_dir" >&2
        exit 2
    }
else
    mkdir -p "$output_dir"
fi
readonly output_dir
readonly metadata="$output_dir/metadata.tsv"
readonly stage2_artifact="$output_dir/stage2.grbc"
readonly stage3_artifact="$output_dir/stage3.grbc"

printf 'schema\t1\nsource-sha256\t%s\n' "$(sha256sum "$source_file" | awk '{print $1}')" > "$metadata"
printf 'artifacts\t%s\n' "$output_dir" >&2

manifest_value() {
    local manifest=$1 key=$2 value
    value=$(awk -F '\t' -v key="$key" '$1 == key { if (++found > 1) exit 2; print $2 } END { exit(found == 1 ? 0 : 1) }' "$manifest") || return 1
    [[ -n "$value" ]] || return 1
    printf '%s\n' "$value"
}

validate_native_stage() {
    local label=$1 executable=$2 manifest=$3 expected_stage=$4 expected_bytecode=${5:-}
    [[ -f "$manifest" ]] || { echo "native-convergence: $label provenance is missing: $manifest" >&2; return 1; }
    local schema stage optimization linker recorded_native recorded_source recorded_bytecode
    schema=$(manifest_value "$manifest" schema) || { echo "native-convergence: $label provenance lacks schema" >&2; return 1; }
    stage=$(manifest_value "$manifest" stage) || { echo "native-convergence: $label provenance lacks stage" >&2; return 1; }
    optimization=$(manifest_value "$manifest" optimization) || { echo "native-convergence: $label provenance lacks optimization" >&2; return 1; }
    linker=$(manifest_value "$manifest" linker) || { echo "native-convergence: $label provenance lacks linker" >&2; return 1; }
    recorded_native=$(manifest_value "$manifest" native-sha256) || { echo "native-convergence: $label provenance lacks native-sha256" >&2; return 1; }
    recorded_source=$(manifest_value "$manifest" source-sha256) || { echo "native-convergence: $label provenance lacks source-sha256" >&2; return 1; }
    [[ "$schema" == 1 && "$stage" == "$expected_stage" && "$optimization" == O3 && "$linker" == wild ]] || {
        echo "native-convergence: $label provenance must bind schema=1, stage=$expected_stage, optimization=O3, linker=wild" >&2
        return 1
    }
    [[ "$recorded_native" == "$(sha256sum "$executable" | awk '{print $1}')" ]] || {
        echo "native-convergence: $label executable does not match its provenance hash" >&2
        return 1
    }
    [[ "$recorded_source" == "$(sha256sum "$source_file" | awk '{print $1}')" ]] || {
        echo "native-convergence: $label provenance was built for different source bytes" >&2
        return 1
    }
    readelf -p .comment "$executable" 2>/dev/null | grep -Eqi 'wild' || {
        echo "native-convergence: $label executable lacks a Wild linker marker in .comment" >&2
        return 1
    }
    if [[ -n "$expected_bytecode" ]]; then
        recorded_bytecode=$(manifest_value "$manifest" compiler-bytecode-sha256) || {
            echo "native-convergence: stage 2 provenance lacks compiler-bytecode-sha256" >&2
            return 1
        }
        [[ "$recorded_bytecode" == "$expected_bytecode" ]] || {
            echo "native-convergence: stage 2 native compiler is not derived from the emitted stage2 artifact" >&2
            return 1
        }
    fi
    printf '%s-native-sha256\t%s\n%s-provenance\t%s\n' "$label" "$recorded_native" "$label" "$manifest" >> "$metadata"
}

validate_native_stage stage1 "$stage1_native" "$stage1_provenance" 1
validate_native_stage stage2 "$stage2_native" "$stage2_provenance" 2

run_stage() {
    local label=$1 executable=$2 artifact=$3
    local log="$output_dir/$label.log"
    set +e
    LC_ALL=C TZ=UTC "$executable" "$artifact" "$source_file" >"$log" 2>&1
    local status=$?
    set -e
    printf '%s-exit\t%s\n' "$label" "$status" >> "$metadata"
    [[ $status -eq 0 ]] || { echo "native-convergence: $label compiler failed; see $log" >&2; return 1; }
    [[ -s "$artifact" ]] || { echo "native-convergence: $label compiler emitted no artifact" >&2; return 1; }
}

run_stage stage1 "$stage1_native" "$stage2_artifact"
stage2_hash=$(sha256sum "$stage2_artifact" | awk '{print $1}')
printf 'stage2-sha256\t%s\nstage2-bytes\t%s\n' "$stage2_hash" "$(wc -c < "$stage2_artifact")" >> "$metadata"
validate_native_stage stage2 "$stage2_native" "$stage2_provenance" 2 "$stage2_hash"
run_stage stage2 "$stage2_native" "$stage3_artifact"
stage3_hash=$(sha256sum "$stage3_artifact" | awk '{print $1}')
printf 'stage3-sha256\t%s\nstage3-bytes\t%s\n' "$stage3_hash" "$(wc -c < "$stage3_artifact")" >> "$metadata"

if cmp -s "$stage2_artifact" "$stage3_artifact"; then
    printf 'result\tbyte-identical\n' >> "$metadata"
    printf 'CONVERGED\tstage2=%s\tstage3=%s\tartifacts=%s\n' "$stage2_hash" "$stage3_hash" "$output_dir"
    exit 0
fi

readonly difference="$output_dir/stage2-stage3.diff"
{
    printf 'stage2-sha256 %s\nstage3-sha256 %s\n' "$stage2_hash" "$stage3_hash"
    printf 'stage2-bytes %s\nstage3-bytes %s\n' "$(wc -c < "$stage2_artifact")" "$(wc -c < "$stage3_artifact")"
    printf '\nfirst differing byte offsets (decimal; stage2-octal stage3-octal):\n'
    set +e
    cmp -l "$stage2_artifact" "$stage3_artifact" | awk 'NR <= 64 { print } NR == 64 { exit }'
    set -e
} > "$difference"
printf 'result\tnot-byte-identical\ndifference\t%s\n' "$difference" >> "$metadata"
echo "native-convergence: stage2 and stage3 differ; hashes and first offsets: $difference" >&2
exit 1
