#!/usr/bin/env bash
# Manual/ignored benchmark for the durable O3 native object cache.
#
# This is deliberately not a CI gate: a cold full-self-host native build is
# expensive and absolute wall-clock times are machine dependent.  It records
# the cold, warm, and ABI-preserving one-function-body-edit builds along with
# cache manifests so an investigator can inspect reuse rather than infer it
# from elapsed time alone.
set -euo pipefail

usage() {
    cat >&2 <<'USAGE'
usage: tooling/tests/native-one-function-cache-benchmark.sh [--keep]

Copies self-host/src into a new private target/ scratch directory, compiles the
production closure three times with release grc at O3/Wild, and edits only the
copied compiler::usize_from_u32 body between the warm and edited builds.

The script never writes project source or uses a pre-existing native cache.
By default it removes its scratch directory when it finishes; --keep retains
the directory and prints its path for log/object-manifest inspection.
USAGE
    exit 2
}

keep=0
case "${1:-}" in
    '') ;;
    --keep) keep=1 ;;
    -h|--help) usage ;;
    *) usage ;;
esac

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)
grc="$repo_root/target/release/grc"
source_root="$repo_root/self-host/src"
[[ -x "$grc" ]] || {
    echo "native-one-function-cache: release grc is required; run tooling/ram-gate.sh cargo build --release -p grandiose --bin grc" >&2
    exit 2
}

mkdir -p "$repo_root/target"
scratch=$(mktemp -d "$repo_root/target/native-one-function-cache.XXXXXX")
cleanup() {
    if ((keep == 0)); then
        rm -rf -- "$scratch"
    else
        printf 'native-one-function-cache: retained evidence: %s\n' "$scratch" >&2
    fi
}
trap cleanup EXIT

copied_source="$scratch/src"
cache="$scratch/private-cache"
# The CLI writes durable object and manifest entries directly into the
# directory passed to --native-incremental-cache.
objects="$cache"
mkdir -p "$cache"
cp -a -- "$source_root/." "$copied_source/"

mapfile -t production_inputs < <(
    "$repo_root/tooling/self-host-production-source.sh" inputs
)
inputs=()
for original in "${production_inputs[@]}"; do
    relative=${original#"$source_root/"}
    [[ "$relative" != "$original" ]] || {
        echo "native-one-function-cache: production input escapes source root: $original" >&2
        exit 1
    }
    inputs+=("$copied_source/$relative")
done

time_bin=${TIME_BIN:-/usr/bin/time}
[[ -x "$time_bin" ]] || {
    echo "native-one-function-cache: time binary is not executable: $time_bin" >&2
    exit 2
}

build() {
    local label=$1 output="$scratch/$1-native" log="$scratch/$1.log" timing="$scratch/$1.time"
    G1_NATIVE_OBJECT_WORKERS="${G1_NATIVE_OBJECT_WORKERS:-1}" \
        "$time_bin" -o "$timing" -f '%e real-seconds %M max-rss-kib' \
        "$grc" -O3 --emit executable --native-incremental-cache "$cache" \
        --native-allocation-limit 536870912 -o "$output" "${inputs[@]}" \
        >"$log" 2>&1
    [[ -x "$output" ]] || {
        echo "native-one-function-cache: $label build emitted no executable; see $log" >&2
        exit 1
    }
    printf '%s\t%s\n' "$label" "$(<"$timing")" | tee -a "$scratch/timings.tsv"
}

snapshot_manifests() {
    local destination=$1
    [[ -d "$objects" ]] || {
        echo "native-one-function-cache: expected durable object directory was not created: $objects" >&2
        exit 1
    }
    find "$objects" -maxdepth 1 -type f -name '*.manifest' -printf '%f\n' | LC_ALL=C sort > "$destination"
}

build cold
build warm
snapshot_manifests "$scratch/manifests-before-edit.txt"

# The edit changes exactly one reachable compiler-function body while retaining
# its `u32 -> usize` ABI.  It is made only in the copied source tree.  Unlike a
# comment or `+ 0`, this branch survives source-level optimization decisions
# and gives the function unit a meaningfully different body.
edited="$copied_source/compiler/compiler.glorious"
perl -0pi -e '
    my $count = s{usize_from_u32\(value: u32\) -> usize \{\n    wrapping_convert_to_usize\(value\)\n\}}
        {usize_from_u32(value: u32) -> usize {\n    if(value == 0) { 0 } else { wrapping_convert_to_usize(value) }\n}};
    die "expected exactly one usize_from_u32 body\n" unless $count == 1;
' "$edited"

build body-edit
snapshot_manifests "$scratch/manifests-after-edit.txt"
comm -13 "$scratch/manifests-before-edit.txt" "$scratch/manifests-after-edit.txt" \
    > "$scratch/new-manifests-after-edit.txt"

{
    printf 'new-manifests-after-body-edit\n'
    while IFS= read -r manifest; do
        [[ -n "$manifest" ]] || continue
        printf '%s\t' "$manifest"
        sed -n '4p' "$objects/$manifest"
    done < "$scratch/new-manifests-after-edit.txt"
} | tee "$scratch/object-reuse-evidence.tsv"

printf 'native-one-function-cache: cold/warm/body-edit timings and manifest evidence: %s\n' "$scratch" >&2
