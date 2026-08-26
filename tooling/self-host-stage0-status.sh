#!/usr/bin/env bash
# Compact, machine-readable progress report for the self-hosting plan.
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
readonly ledger="$root/docs/self-host-stage0/module-ledger.tsv"
readonly baseline="$root/docs/self-host-stage0/baseline.toml"

[[ -f "$ledger" && -f "$baseline" ]] || {
    echo "self-host status: missing ledger or baseline" >&2
    exit 1
}

baseline_commit="$(awk -F ' = ' '$1 == "stage0_baseline" { gsub("\"", "", $2); print $2 }' "$baseline")"
frozen_tests="$(awk -F ' = ' '$1 == "test_inventory_records" { print $2 }' "$baseline")"
current_tests="$($root/tooling/self-host-stage0-test-inventory.sh | wc -l | tr -d ' ')"
module_count="$(awk 'END { print NR - 1 }' "$ledger")"

if (( module_count != 36 )); then
    echo "self-host status: expected exactly 36 module ledger rows, got $module_count" >&2
    exit 1
fi

if ! awk -F '\t' '
    NR > 1 && $4 !~ /^(missing|scaffolded|structural-parity|behavioral-parity|complete)$/ { exit 1 }
' "$ledger"; then
    echo "self-host status: ledger contains an unknown module status" >&2
    exit 1
fi

printf 'stage0_baseline\t%s\n' "$baseline_commit"
printf 'test_budget_seconds\t%s\n' "${GRANDIOSE_TEST_TIMEOUT_SECONDS:-590}"
printf 'frozen_test_inventory\t%s\n' "$frozen_tests"
printf 'current_test_inventory\t%s\n' "$current_tests"
printf 'module_total\t%s\n' "$module_count"
awk -F '\t' '
    NR > 1 { count[$4]++ }
    END {
        for (status in count) print "module_" status "\t" count[status]
    }
' "$ledger" | LC_ALL=C sort
