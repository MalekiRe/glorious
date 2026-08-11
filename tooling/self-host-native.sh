#!/usr/bin/env bash
# Build and run the self-host compiler as a Wild-linked native executable.
#
# This is deliberately a per-worktree development route.  Its cache is rooted
# in this checkout, never in /tmp or a shared user cache.  `init` is the only
# command permitted to seed a baseline artifact, and copies it once into this
# worktree before any native build is produced.
set -euo pipefail

usage() {
    cat >&2 <<'USAGE'
usage:
  tooling/self-host-native.sh init [baseline-cache-dir]
  tooling/self-host-native.sh build
  tooling/self-host-native.sh run <output.grbc> <input.glorious>
  tooling/self-host-native.sh smoke
  tooling/self-host-native.sh canonical-source <output.glorious>
  tooling/self-host-native.sh provenance <canonical-source.glorious> <stage1.tsv>

`init` creates this worktree's private cache and copies the verified baseline
compiler artifact, fingerprint, and any checksummed partitioned `objects/`
intermediates into it once (or uses the optional explicit baseline). Every
copy remains private to this worktree; ABI/IR validation safely cold-builds
stale or absent objects. The baseline is never modified; every build writes
only to this worktree.
`build` emits an O3 Wild-linked native self-host
compiler using durable partition objects below this worktree's private cache;
objects copied from a seed are never required and missing/invalid intermediates
begin cold. `run` executes it; `smoke` compiles a tiny source program through
that native compiler. `provenance` builds (or reuses) the canonical native
stage-1 compiler and writes an immutable O3/Wild provenance manifest for it.
`canonical-source` materializes the exact monolithic source closure used by
that compiler; `provenance` refuses a source file that differs from it.
USAGE
    exit 2
}

readonly route_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
readonly route_cache="$route_root/target/self-host-native-cache"
readonly route_manifest="$route_cache/native-route.manifest"
readonly route_binary="$route_cache/grandiose-self-host-native"
readonly route_fingerprint="$route_cache/build.fingerprint"
readonly route_objects="$route_cache/objects"
readonly route_grc="$route_root/target/release/grc"

inside_worktree() {
    case "$1" in "$route_root"/*) return 0 ;; *) return 1 ;; esac
}

initialize() {
    local seed="${1:-}"
    if [[ -f "$route_manifest" ]]; then
        [[ -f "$route_manifest" ]] || {
            echo "self-host-native: refusing cache without manifest: $route_cache" >&2
            exit 1
        }
        [[ -z "$seed" ]] || {
            echo "self-host-native: cache is already initialized; baseline seeding is one-time" >&2
            exit 1
        }
        return
    fi
    # The shared Git-common-dir baseline is read-only. Its checksummed native
    # compiler artifacts and durable partition objects are copied once into
    # this worktree; no object path is shared. ABI/IR validation remains the
    # authority for reuse, so absent or stale entries cold-build safely. All
    # later writes stay below this worktree root.
    if [[ -n "$seed" ]]; then
        "$route_root/tooling/seed-native-selfhost-cache.sh" \
            --worktree "$route_root" --baseline "$seed"
    else
        local common default_seed
        common="$(git -C "$route_root" rev-parse --git-common-dir)"
        [[ "$common" = /* ]] || common="$route_root/$common"
        default_seed="$common/grandiose-native-selfhost-baseline"
        if [[ -d "$default_seed" ]]; then
            "$route_root/tooling/seed-native-selfhost-cache.sh" \
                --worktree "$route_root" --baseline "$default_seed"
        fi
    fi
    mkdir -p "$route_cache"
    local head
    head="$(git -C "$route_root" rev-parse HEAD)"
    {
        echo "schema=1"
        echo "worktree=$route_root"
        echo "created-head=$head"
        echo "optimization=O3"
    } > "$route_manifest"
}

production_inputs() {
    "$route_root/tooling/self-host-production-source.sh" inputs
}

native_fingerprint() {
    {
        sha256sum "$route_grc"
        sha256sum "$route_root/tooling/self-host-native.sh"
        sha256sum "$route_root/tooling/self-host-production-source.sh"
        production_inputs | xargs -r sha256sum
        printf '%s\n' 'optimization=O3;linker=wild-only;cache-schema=2'
    } | sha256sum | awk '{print $1}'
}

materialize_canonical_source() {
    local output=$1
    [[ ! -e "$output" ]] || {
        echo "self-host-native: refusing to overwrite canonical source: $output" >&2
        exit 2
    }
    # Keep this byte-for-byte aligned with the native build's production
    # closure.  The closure belongs to self-host-production-source.sh; do not
    # reimplement it here (and, in particular, do not accidentally include
    # test-only probe modules).
    "$route_root/tooling/self-host-production-source.sh" materialize \
        --output "$output" --grc "$route_grc"
    [[ -s "$output" ]] || {
        echo "self-host-native: canonical-source emission produced no source" >&2
        exit 1
    }
}

verify_canonical_source() {
    local supplied=$1 generated_dir generated
    generated_dir=$(mktemp -d "$route_cache/.canonical-source.XXXXXX")
    generated="$generated_dir/source.glorious"
    materialize_canonical_source "$generated"
    if ! cmp -s "$supplied" "$generated"; then
        rm -rf -- "$generated_dir"
        echo "self-host-native: provenance source is not the canonical production source closure; run canonical-source and use that exact file" >&2
        exit 2
    fi
    rm -rf -- "$generated_dir"
}

build_native() {
    initialize
    command -v wild >/dev/null || { echo "self-host-native: Wild linker is required" >&2; exit 1; }
    # This tool can be invoked from a parent stage runner whose working
    # directory is a different checkout.  Cargo selects its target directory
    # from the working directory, so run it explicitly from this route's
    # immutable worktree.  In particular, a detached stage-one snapshot must
    # never accidentally build its bootstrap compiler into the live checkout
    # and then look for it below the snapshot.
    (
        cd -- "$route_root"
        "$route_root/tooling/ram-gate.sh" cargo build --release -p grandiose --bin grc
    )
    local fingerprint
    fingerprint="$(native_fingerprint)"
    if [[ -x "$route_binary" && -f "$route_fingerprint" ]] && \
        [[ "$(cat "$route_fingerprint")" == "$fingerprint" ]]; then
        printf '%s\n' "$route_binary"
        return
    fi
    mapfile -t inputs < <(production_inputs)
    # The compiler itself legitimately needs larger compiler-internal tables
    # than the 64 MiB ceiling retained for ordinary native programs. Keep the
    # override explicit, bounded, and confined to this private self-host route.
    "$route_grc" -O3 --emit executable --native-incremental-cache "$route_objects" --native-allocation-limit 536870912 -o "$route_binary" "${inputs[@]}"
    [[ -x "$route_binary" ]] || { echo "self-host-native: native compiler was not emitted" >&2; exit 1; }
    printf '%s\n' "$fingerprint" > "$route_fingerprint"
    printf '%s\n' "$route_binary"
}

case "${1:-}" in
    init)
        shift
        (($# <= 1)) || usage
        initialize "${1:-}"
        ;;
    build)
        shift
        (($# == 0)) || usage
        build_native
        ;;
    run)
        shift
        (($# == 2)) || usage
        binary="$(build_native)"
        "$binary" "$1" "$2"
        ;;
    smoke)
        shift
        (($# == 0)) || usage
        binary="$(build_native)"
        smoke_dir="$route_cache/smoke"
        mkdir -p "$smoke_dir"
        printf '%s\n' 'native_smoke(value: i64) -> i64 { value } main() { () }' > "$smoke_dir/input.glorious"
        "$binary" "$smoke_dir/output.grbc" "$smoke_dir/input.glorious"
        [[ -s "$smoke_dir/output.grbc" ]] || { echo "self-host-native: native smoke emitted no artifact" >&2; exit 1; }
        ;;
    canonical-source)
        shift
        (($# == 1)) || usage
        initialize
        materialize_canonical_source "$1"
        ;;
    provenance)
        shift
        (($# == 2)) || usage
        [[ -f "$1" ]] || { echo "self-host-native: canonical source does not exist: $1" >&2; exit 2; }
        binary="$(build_native)"
        verify_canonical_source "$1"
        exec "$route_root/tooling/write-native-stage-provenance.sh" \
            --stage 1 --native "$binary" --source "$1" --output "$2"
        ;;
    *) usage ;;
esac
