#!/usr/bin/env bash
# Run bootstrap compiler corpus sources through the O3/Wild native self-host
# executable.  This intentionally delegates construction of that executable to
# self-host-native.sh so cache seeding, the production source closure, and the
# no-fallback policy have exactly one owner.
set -euo pipefail

usage() {
    cat >&2 <<'USAGE'
usage:
  tooling/self-host-native-tests.sh list [--manifest FILE] [--case ID]...
  tooling/self-host-native-tests.sh run  [--manifest FILE] [--case ID]... [--keep-artifacts]

The manifest is a tab-separated file with one case per line:
  case-id<TAB>accept|reject<TAB>repository-relative-primary-source-path<TAB>[additional-source-path...]

`run` first builds the O3, Wild-linked native self-host compiler through
tooling/self-host-native.sh, then invokes that one executable with every
ordered source path for each selected case. `accept` requires a nonempty
bytecode artifact; `reject` requires a non-zero native compiler status.
Results are ordered by case id. No VM execution or lower-optimization compiler
fallback is used.
USAGE
    exit 2
}

readonly script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
readonly repo_root="$(cd -- "$script_dir/.." && pwd -P)"
manifest="$repo_root/tooling/self-host-native-corpus.tsv"
runner="${G1_SELF_HOST_NATIVE_RUNNER:-$repo_root/tooling/self-host-native.sh}"
command_name="${1:-}"
[[ -n "$command_name" ]] || usage
shift || true

declare -a requested_cases=()
keep_artifacts=0
while (($#)); do
    case "$1" in
        --manifest)
            (($# >= 2)) || usage
            manifest="$2"
            shift 2
            ;;
        --case)
            (($# >= 2)) || usage
            requested_cases+=("$2")
            shift 2
            ;;
        --keep-artifacts)
            [[ "$command_name" == run ]] || usage
            keep_artifacts=1
            shift
            ;;
        *) usage ;;
    esac
done

[[ "$command_name" == list || "$command_name" == run ]] || usage
[[ -f "$manifest" ]] || { echo "self-host-native-tests: manifest does not exist: $manifest" >&2; exit 2; }

case_selected() {
    local id=$1
    ((${#requested_cases[@]} == 0)) && return 0
    local requested
    for requested in "${requested_cases[@]}"; do
        [[ "$requested" == "$id" ]] && return 0
    done
    return 1
}

# Validate before printing or running anything.  That prevents an incomplete
# manifest from looking like a partially successful corpus invocation.
declare -A seen=()
declare -a cases=()
while IFS= read -r line; do
    [[ -z "$line" || "$line" == \#* ]] && continue
    IFS=$'\t' read -r -a fields <<< "$line"
    ((${#fields[@]} >= 3)) || { echo "self-host-native-tests: malformed manifest line: $line" >&2; exit 2; }
    id="${fields[0]}"
    expectation="${fields[1]}"
    source_paths=("${fields[@]:2}")
    [[ "$id" =~ ^[A-Za-z0-9][A-Za-z0-9._-]*$ ]] || { echo "self-host-native-tests: invalid case id: $id" >&2; exit 2; }
    [[ "$expectation" == accept || "$expectation" == reject ]] || { echo "self-host-native-tests: $id must expect accept or reject" >&2; exit 2; }
    for source in "${source_paths[@]}"; do
        [[ -n "$source" && "$source" != /* && "$source" != *".."* ]] || { echo "self-host-native-tests: $id has unsafe source path: $source" >&2; exit 2; }
        [[ -f "$repo_root/$source" ]] || { echo "self-host-native-tests: $id source does not exist: $source" >&2; exit 2; }
    done
    [[ -z "${seen[$id]:-}" ]] || { echo "self-host-native-tests: duplicate case id: $id" >&2; exit 2; }
    seen[$id]=1
    case_selected "$id" && cases+=("$id"$'\t'"$expectation"$'\t'"$(IFS=$'\t'; printf '%s' "${source_paths[*]}")")
done < "$manifest"

for requested in "${requested_cases[@]}"; do
    [[ -n "${seen[$requested]:-}" ]] || { echo "self-host-native-tests: requested case is absent: $requested" >&2; exit 2; }
done

IFS=$'\n' cases=( $(printf '%s\n' "${cases[@]}" | LC_ALL=C sort) )
unset IFS
((${#cases[@]})) || { echo "self-host-native-tests: selection is empty" >&2; exit 2; }

if [[ "$command_name" == list ]]; then
    printf '%s\n' "${cases[@]}"
    exit 0
fi

[[ -x "$runner" ]] || { echo "self-host-native-tests: native runner is not executable: $runner" >&2; exit 2; }
native_binary="$($runner build)"
[[ -x "$native_binary" ]] || { echo "self-host-native-tests: runner did not return an executable: $native_binary" >&2; exit 1; }

run_root="$repo_root/target/self-host-native-cache/test-corpus"
mkdir -p "$run_root"
run_dir="$(mktemp -d "$run_root/run.XXXXXX")"
trap '[[ $keep_artifacts -eq 1 ]] || rm -rf -- "$run_dir"' EXIT
printf 'self-host-native-tests: native=%s cases=%d artifacts=%s\n' "$native_binary" "${#cases[@]}" "$run_dir"

passed=0
failed=0
for entry in "${cases[@]}"; do
    IFS=$'\t' read -r -a fields <<< "$entry"
    id="${fields[0]}"
    expectation="${fields[1]}"
    source_paths=("${fields[@]:2}")
    source_label="$(IFS=,; printf '%s' "${source_paths[*]}")"
    output="$run_dir/$id.grbc"
    log="$run_dir/$id.log"
    set +e
    "$native_binary" "$output" "${source_paths[@]/#/$repo_root/}" >"$log" 2>&1
    status=$?
    set -e
    if [[ "$expectation" == accept ]]; then
        if [[ $status -eq 0 && -s "$output" ]]; then
            printf 'PASS\t%s\taccept\t%s\n' "$id" "$source_label"
            ((passed += 1))
            continue
        fi
        reason="expected accept, native compiler exited $status"
        [[ -s "$output" ]] || reason+=" and emitted no artifact"
    else
        if [[ $status -ne 0 ]]; then
            printf 'PASS\t%s\treject\t%s\n' "$id" "$source_label"
            ((passed += 1))
            continue
        fi
        reason="expected reject, native compiler accepted the source"
    fi
    printf 'FAIL\t%s\t%s\t%s\n' "$id" "$reason" "$source_label" >&2
    printf '%s\n' "--- native diagnostic: $id ($log) ---" >&2
    sed -n '1,160p' "$log" >&2
    ((failed += 1))
done

printf 'self-host-native-tests: passed=%d failed=%d\n' "$passed" "$failed"
((failed == 0))
