#!/usr/bin/env bash
# Validate the native self-host corpus's declared outcomes against the release
# bootstrap compiler.  This is deliberately a source-level oracle: it neither
# builds nor executes the O3/Wild self-host executable, and it cannot take a
# VM or lower-optimization fallback path.
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)
compiler="$repo_root/target/release/grc"
manifest="$repo_root/tooling/self-host-native-corpus.tsv"

if [[ ! -x "$compiler" ]]; then
    "$repo_root/tooling/ram-gate.sh" cargo build --release -p grandiose --bin grc
fi

# Reuse the native driver's strict manifest parser and deterministic ordering
# without invoking its native runner.
mapfile -t cases < <("$repo_root/tooling/self-host-native-tests.sh" list --manifest "$manifest")
(( ${#cases[@]} > 0 )) || { echo "bootstrap corpus: empty selection" >&2; exit 1; }

accepted=0
rejected=0
failed=0
for entry in "${cases[@]}"; do
    IFS=$'\t' read -r id expectation source <<< "$entry"
    set +e
    "$compiler" -O3 --check "$repo_root/$source" >"$repo_root/target/self-host-native-bootstrap-$id.log" 2>&1
    status=$?
    set -e
    rm -f -- "$repo_root/target/self-host-native-bootstrap-$id.log"

    if [[ "$expectation" == accept && $status -eq 0 ]]; then
        ((accepted += 1))
        continue
    fi
    if [[ "$expectation" == reject && $status -ne 0 ]]; then
        ((rejected += 1))
        continue
    fi
    printf 'bootstrap corpus mismatch: %s expected %s, bootstrap -O3 --check exited %d (%s)\n' \
        "$id" "$expectation" "$status" "$source" >&2
    ((failed += 1))
done

printf 'bootstrap corpus: accepted=%d rejected=%d failed=%d\n' "$accepted" "$rejected" "$failed"
((failed == 0))
