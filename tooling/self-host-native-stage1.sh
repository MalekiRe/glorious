#!/usr/bin/env bash
# Produce retained evidence for the native stage-1 -> stage-2 bytecode step.
#
# This is intentionally narrower than self-host-native-convergence.sh: stage 2
# does not have a native host yet.  It prepares the exact, provenance-bound
# stage2.grbc that such a host must later be lowered from.  It never invokes
# grvm and never treats a .grbc artifact as an executable.
set -euo pipefail

usage() {
    cat >&2 <<'USAGE'
usage: tooling/self-host-native-stage1.sh run [--output-dir DIR]

Materializes the canonical production self-host source, creates immutable O3 /
Wild stage-1 provenance, and runs that exact native executable to emit
stage2.grbc.  DIR, when supplied, must not already exist.  Every result,
including a compiler failure, retains source, provenance, logs, and metadata.
USAGE
    exit 2
}

readonly script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
readonly repo_root="$(cd -- "$script_dir/.." && pwd -P)"
readonly native_tool="$repo_root/tooling/self-host-native.sh"
readonly grvm="$repo_root/target/release/grvm"

command=${1:-}
[[ "$command" == run ]] || usage
shift
output_dir=
while (($#)); do
    case "$1" in
        --output-dir) output_dir=${2:?missing value}; shift 2 ;;
        -h|--help) usage ;;
        *) usage ;;
    esac
done

[[ -x "$native_tool" ]] || { echo "native-stage1: native tool is not executable: $native_tool" >&2; exit 2; }
if [[ -z "$output_dir" ]]; then
    mkdir -p "$repo_root/target/self-host-native-stage1"
    output_dir="$(mktemp -d "$repo_root/target/self-host-native-stage1/run.XXXXXX")"
elif [[ -e "$output_dir" ]]; then
    echo "native-stage1: refusing to overwrite retained evidence: $output_dir" >&2
    exit 2
else
    mkdir -p "$output_dir"
fi
readonly output_dir
readonly source="$output_dir/canonical-source.glorious"
readonly provenance="$output_dir/stage1-provenance.tsv"
readonly stage2="$output_dir/stage2.grbc"
readonly metadata="$output_dir/metadata.tsv"

printf 'artifacts\t%s\n' "$output_dir" >&2

clean_head() {
    local phase=$1 head status
    head=$(git -C "$repo_root" rev-parse --verify HEAD 2>/dev/null) || {
        echo "native-stage1: $phase requires a Git checkout with HEAD" >&2
        return 1
    }
    # Byte hashes bind the source and native executable themselves.  Requiring
    # a clean tracked tree in addition prevents this retained run from claiming
    # a committed source/executable relationship while either was produced
    # from uncommitted tracked edits.  Deliberately ignore untracked evidence
    # files below target/.
    git -C "$repo_root" diff --quiet --ignore-submodules -- || {
        status=$?
        [[ $status -eq 1 ]] || return "$status"
        echo "native-stage1: $phase refuses a checkout with unstaged tracked edits" >&2
        return 1
    }
    git -C "$repo_root" diff --cached --quiet --ignore-submodules -- || {
        status=$?
        [[ $status -eq 1 ]] || return "$status"
        echo "native-stage1: $phase refuses a checkout with staged tracked edits" >&2
        return 1
    }
    printf '%s\n' "$head"
}

snapshot_head() {
    local head status
    head=$(git -C "$snapshot_dir" rev-parse --verify HEAD 2>/dev/null) || {
        echo "native-stage1: snapshot requires a Git checkout with HEAD" >&2
        return 1
    }
    git -C "$snapshot_dir" diff --quiet --ignore-submodules -- || {
        status=$?
        [[ $status -eq 1 ]] || return "$status"
        echo "native-stage1: snapshot has unstaged tracked edits" >&2
        return 1
    }
    git -C "$snapshot_dir" diff --cached --quiet --ignore-submodules -- || {
        status=$?
        [[ $status -eq 1 ]] || return "$status"
        echo "native-stage1: snapshot has staged tracked edits" >&2
        return 1
    }
    printf '%s\n' "$head"
}

manifest_value() {
    local manifest=$1 key=$2 value
    value=$(awk -F '\t' -v key="$key" '$1 == key { if (++found > 1) exit 2; print $2 } END { exit(found == 1 ? 0 : 1) }' "$manifest") || return 1
    [[ -n "$value" ]] || return 1
    printf '%s\n' "$value"
}

record_failure() {
    local phase=$1 status=$2
    printf 'schema\t1\nphase\t%s\nexit\t%s\n' "$phase" "$status" > "$metadata"
    salvage_snapshot_native_cache
    printf 'result\tfailed\n' >> "$metadata"
    echo "native-stage1: $phase failed; retained evidence: $output_dir" >&2
    exit "$status"
}

# A failed disposable snapshot may already contain durable Clang objects. Keep
# only complete, self-describing cache pairs as retained retry input. The
# snapshot cache is never modified, and this deliberately does not make the
# retained directory a live/shared cache: a later retry must copy it into its
# own private route before invoking `grc`, whose native cache revalidates the
# BLAKE3 object digest before reuse.
salvage_snapshot_native_cache() {
    local source_objects retry_root retry_objects stage object manifest key
    local schema digest object_blake abi copied count=0
    [[ -n "${snapshot_dir:-}" ]] || return 0
    source_objects="$snapshot_dir/target/self-host-native-cache/objects"
    [[ -d "$source_objects" ]] || return 0
    retry_root="$output_dir/native-cache-retry-seed"
    retry_objects="$retry_root/objects"
    [[ ! -e "$retry_root" ]] || return 0
    stage=$(mktemp -d "$output_dir/.native-cache-salvage.XXXXXX") || return 0
    mkdir -p "$stage/objects"
    shopt -s nullglob
    for object in "$source_objects"/*.o; do
        key=${object##*/}
        key=${key%.o}
        manifest="$source_objects/$key.manifest"
        [[ "$key" =~ ^[0-9a-f]{64}$ && -f "$manifest" ]] || continue
        schema=$(sed -n '1p' "$manifest")
        digest=$(sed -n '2p' "$manifest")
        object_blake=$(sed -n '3p' "$manifest")
        abi=$(sed -n '4p' "$manifest")
        [[ "$schema" == schema=1 && "$digest" == "digest=$key" ]] || continue
        [[ "$object_blake" =~ ^object-blake3=[0-9a-f]{64}$ && "$abi" == abi=* ]] || continue
        # Durable cache consumers are the cryptographic authority; retain only
        # an intact object/manifest pair here and copy it byte-for-byte. The
        # retry receives a private seed, never a mutable alias of this cache.
        cp -- "$object" "$stage/objects/$key.o" || continue
        cp -- "$manifest" "$stage/objects/$key.manifest" || {
            rm -f -- "$stage/objects/$key.o"
            continue
        }
        copied=$(sha256sum "$stage/objects/$key.o" | awk '{print $1}')
        [[ -n "$copied" ]] || continue
        count=$((count + 1))
    done
    shopt -u nullglob
    if ((count == 0)); then
        rm -rf -- "$stage"
        return 0
    fi
    mkdir -- "$retry_root" || {
        rm -rf -- "$stage"
        return 0
    }
    mv -- "$stage/objects" "$retry_objects" || {
        rm -rf -- "$stage"
        return 0
    }
    rmdir -- "$stage"
    {
        printf 'native-cache-retry-seed\t%s\n' "$retry_root"
        printf 'native-cache-retry-objects\t%s\n' "$count"
    } >> "$metadata"
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

run_head=$(clean_head preflight) || record_failure preflight 1
# A long O3 build must never silently slide onto files merged into the live
# checkout after preflight.  Keep the exact committed checkout as retained
# evidence, and run every source/native/provenance step from that immutable
# worktree. Git does not permit a linked worktree inside the live worktree, so
# the temporary checkout lives beside it; the copied source and executable
# below are the retained stage-1 snapshot inputs.
snapshot_dir=$(mktemp -d "${TMPDIR:-/tmp}/grandiose-stage1-snapshot.XXXXXX")
rmdir "$snapshot_dir"
readonly snapshot_dir
cleanup_snapshot() {
    git -C "$repo_root" worktree remove --force "$snapshot_dir" >/dev/null 2>&1 || true
}
trap cleanup_snapshot EXIT
run_logged snapshot git -C "$repo_root" worktree add --detach "$snapshot_dir" "$run_head"
[[ "$(snapshot_head)" == "$run_head" ]] || record_failure snapshot 1
readonly snapshot_native_tool="$snapshot_dir/tooling/self-host-native.sh"
[[ -x "$snapshot_native_tool" ]] || record_failure snapshot 1
run_logged canonical-source "$snapshot_native_tool" canonical-source "$source"
[[ -s "$source" ]] || record_failure canonical-source 1
[[ "$(snapshot_head)" == "$run_head" ]] || record_failure canonical-source 1
run_logged provenance "$snapshot_native_tool" provenance "$source" "$provenance"
[[ -s "$provenance" ]] || record_failure provenance 1
[[ "$(snapshot_head)" == "$run_head" ]] || record_failure provenance 1

# `build` is called after provenance solely to obtain the exact cached native
# path.  The hash check below proves it is the executable the immutable
# provenance describes, rather than merely a similarly named compiler.
run_logged build "$snapshot_native_tool" build
snapshot_native=$(tail -n 1 "$output_dir/build.log")
[[ -x "$snapshot_native" ]] || record_failure build 1
[[ "$(snapshot_head)" == "$run_head" ]] || record_failure build 1
readonly native="$output_dir/stage1-native"
run_logged snapshot-native cp -- "$snapshot_native" "$native"
[[ -x "$native" ]] || record_failure snapshot-native 1
schema=$(manifest_value "$provenance" schema) || record_failure provenance 1
stage=$(manifest_value "$provenance" stage) || record_failure provenance 1
optimization=$(manifest_value "$provenance" optimization) || record_failure provenance 1
linker=$(manifest_value "$provenance" linker) || record_failure provenance 1
recorded_native=$(manifest_value "$provenance" native-sha256) || record_failure provenance 1
recorded_source=$(manifest_value "$provenance" source-sha256) || record_failure provenance 1
[[ "$schema" == 1 && "$stage" == 1 && "$optimization" == O3 && "$linker" == wild ]] || record_failure provenance 1
[[ "$recorded_native" == "$(sha256sum "$native" | awk '{print $1}')" ]] || record_failure provenance 1
[[ "$recorded_source" == "$(sha256sum "$source" | awk '{print $1}')" ]] || record_failure provenance 1
readelf -p .comment "$native" 2>/dev/null | grep -Eqi 'wild' || record_failure provenance 1
[[ "$(snapshot_head)" == "$run_head" ]] || record_failure stage1 1

set +e
LC_ALL=C TZ=UTC "$native" "$stage2" "$source" >"$output_dir/stage1.log" 2>&1
stage1_status=$?
set -e
{
    printf 'schema\t1\n'
    printf 'stage1-native\t%s\n' "$native"
    printf 'stage1-native-sha256\t%s\n' "$recorded_native"
    printf 'stage1-provenance\t%s\n' "$provenance"
    printf 'source-sha256\t%s\n' "$recorded_source"
    printf 'snapshot-head\t%s\n' "$run_head"
    printf 'repository-head\t%s\n' "$run_head"
    printf 'stage1-exit\t%s\n' "$stage1_status"
} > "$metadata"
if [[ $stage1_status -ne 0 ]]; then
    printf 'result\tfailed\n' >> "$metadata"
    echo "native-stage1: compiler failed; retained evidence: $output_dir" >&2
    exit "$stage1_status"
fi
if [[ ! -s "$stage2" ]]; then
    printf 'result\tfailed\n' >> "$metadata"
    echo "native-stage1: compiler emitted no stage2 artifact; retained evidence: $output_dir" >&2
    exit 1
fi
if [[ ! -x "$grvm" ]]; then
    run_logged verify-build "$repo_root/tooling/ram-gate.sh" \
        cargo build --release -p grandiose --bin grvm
fi
[[ -x "$grvm" ]] || record_failure verify-build 1
# A nonempty file is not stage-two evidence.  Decode and verify the exact
# emitted bytes before recording the run as usable bootstrap input.  This is a
# verifier-only preflight: it must never execute the bytecode in the VM.
run_logged verify-stage2 "$grvm" native-preflight "$stage2"
printf 'stage2-sha256\t%s\nstage2-bytes\t%s\nresult\temitted\n' \
    "$(sha256sum "$stage2" | awk '{print $1}')" "$(wc -c < "$stage2")" >> "$metadata"
printf 'STAGE1_EMITTED\tstage2=%s\tartifacts=%s\n' \
    "$(sha256sum "$stage2" | awk '{print $1}')" "$output_dir"
