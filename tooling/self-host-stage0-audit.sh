#!/usr/bin/env bash
# Checks the phase-A self-host inventory without running a compiler probe.
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
readonly ledger="$root/docs/self-host-stage0/module-ledger.tsv"
readonly stdlib_ledger="$root/docs/self-host-stage0/bootstrap-stdlib-ledger.tsv"
readonly baseline="$root/docs/self-host-stage0/baseline.toml"
readonly stage0_lib="$root/crates/grandiose-stage0/src/lib.rs"
readonly api_inventory="$root/tooling/self-host-stage0-api-inventory.sh"
readonly test_inventory="$root/tooling/self-host-stage0-test-inventory.sh"
readonly test_owners="$root/docs/self-host-stage0/test-owner-rules.tsv"
readonly parity_evidence="$root/docs/self-host-stage0/parity-evidence"
readonly current_delta="$root/docs/self-host-stage0/current-baseline-delta.tsv"

[[ -f "$ledger" && -f "$stdlib_ledger" && -f "$baseline" && -f "$stage0_lib" ]] || {
    echo "self-host audit: missing baseline inventory input" >&2
    exit 1
}
[[ -f "$test_owners" ]] || {
    echo "self-host audit: missing test-owner rules" >&2
    exit 1
}
[[ -f "$current_delta" ]] || {
    echo "self-host audit: missing current baseline delta ledger" >&2
    exit 1
}

baseline_commit="$(awk -F ' = ' '$1 == "stage0_baseline" { gsub("\"", "", $2); print $2 }' "$baseline")"
translation_plan="$(awk -F ' = ' '$1 == "translation_plan" { gsub("\"", "", $2); print $2 }' "$baseline")"
[[ "$baseline_commit" =~ ^[0-9a-f]{40}$ ]] || {
    echo "self-host audit: baseline commit must be a full SHA-1" >&2
    exit 1
}
[[ "$translation_plan" != /* && "$translation_plan" != *".."* && -f "$root/$translation_plan" ]] || {
    echo "self-host audit: canonical translation plan is missing" >&2
    exit 1
}
git -C "$root" cat-file -e "${baseline_commit}^{commit}" || {
    echo "self-host audit: baseline commit is unavailable" >&2
    exit 1
}

frozen_tree="$(mktemp -d)"
trap 'rm -rf "$frozen_tree"' EXIT
git -C "$root" archive "$baseline_commit" crates/grandiose-stage0 | tar -x -C "$frozen_tree"
readonly frozen_stage0="$frozen_tree/crates/grandiose-stage0"

expected_api_records="$(awk -F ' = ' '$1 == "public_api_inventory_records" { print $2 }' "$baseline")"
expected_api_digest="$(awk -F ' = ' '$1 == "public_api_inventory_sha256" { gsub("\"", "", $2); print $2 }' "$baseline")"
[[ "$expected_api_records" =~ ^[1-9][0-9]*$ && "$expected_api_digest" =~ ^[0-9a-f]{64}$ ]] || {
    echo "self-host audit: invalid public API inventory baseline" >&2
    exit 1
}
actual_api_records="$(STAGE0_INVENTORY_STAGE0_ROOT="$frozen_stage0" "$api_inventory" | wc -l | tr -d ' ')"
actual_api_digest="$(STAGE0_INVENTORY_STAGE0_ROOT="$frozen_stage0" "$api_inventory" | sha256sum | awk '{print $1}')"
[[ "$actual_api_records" == "$expected_api_records" && "$actual_api_digest" == "$expected_api_digest" ]] || {
    echo "self-host audit: public API inventory drifted; perform a baseline roll" >&2
    exit 1
}

expected_test_records="$(awk -F ' = ' '$1 == "test_inventory_records" { print $2 }' "$baseline")"
expected_test_digest="$(awk -F ' = ' '$1 == "test_inventory_sha256" { gsub("\"", "", $2); print $2 }' "$baseline")"
[[ "$expected_test_records" =~ ^[1-9][0-9]*$ && "$expected_test_digest" =~ ^[0-9a-f]{64}$ ]] || {
    echo "self-host audit: invalid test inventory baseline" >&2
    exit 1
}
actual_test_records="$(STAGE0_INVENTORY_STAGE0_ROOT="$frozen_stage0" "$test_inventory" | wc -l | tr -d ' ')"
actual_test_digest="$(STAGE0_INVENTORY_STAGE0_ROOT="$frozen_stage0" "$test_inventory" | sha256sum | awk '{print $1}')"
[[ "$actual_test_records" == "$expected_test_records" && "$actual_test_digest" == "$expected_test_digest" ]] || {
    echo "self-host audit: test inventory drifted; perform a baseline roll" >&2
    exit 1
}

# The working normal compiler may deliberately be ahead of the frozen parity
# baseline. Keep that difference explicit: every added test must appear once
# in the delta ledger and remain marked unported until a baseline roll carries
# its source-port evidence into the frozen corpus.
awk -F '\t' '
    NR == 1 { if ($1 != "test" || $2 != "module_owner" || $3 != "behavior" || $4 != "status") exit 1; next }
    NF != 4 || $1 !~ /^crates\/grandiose-stage0\// || $2 !~ /^M[0-9][0-9]$/ || $3 == "" || $4 != "unported" { exit 1 }
' "$current_delta" || {
    echo "self-host audit: malformed current baseline delta ledger" >&2
    exit 1
}
frozen_inventory="$frozen_tree/frozen-test-inventory"
current_inventory="$frozen_tree/current-test-inventory"
STAGE0_INVENTORY_STAGE0_ROOT="$frozen_stage0" "$test_inventory" | cut -f1 | LC_ALL=C sort > "$frozen_inventory"
"$test_inventory" | cut -f1 | LC_ALL=C sort > "$current_inventory"
diff -u \
    <(comm -13 "$frozen_inventory" "$current_inventory") \
    <(awk -F '\t' 'NR > 1 { print $1 }' "$current_delta" | LC_ALL=C sort) || {
    echo "self-host audit: current normal-compiler test delta is not fully ledgered" >&2
    exit 1
}

mapfile -t expected_modules < <(
    {
        sed -n 's/^pub mod \([a-z_][a-z_]*\);$/\1/p' "$stage0_lib"
        printf '%s\n' lib main
    } | LC_ALL=C sort
)
mapfile -t ledger_modules < <(
    awk -F '\t' 'NR > 1 { print $2 }' "$ledger" | LC_ALL=C sort
)

[[ "${#expected_modules[@]}" -eq 36 ]] || {
    echo "self-host audit: expected 36 Stage0 modules, found ${#expected_modules[@]}" >&2
    exit 1
}
[[ "${#ledger_modules[@]}" -eq 36 ]] || {
    echo "self-host audit: module ledger must contain exactly 36 rows" >&2
    exit 1
}
diff -u <(printf '%s\n' "${expected_modules[@]}") <(printf '%s\n' "${ledger_modules[@]}")

awk -F '\t' '
    NR == 1 {
        if ($1 != "id" || $2 != "stage0_module" || $4 != "status") exit 1
        next
    }
    NF != 6 { printf "self-host audit: malformed ledger row %d\n", NR > "/dev/stderr"; exit 1 }
    $4 !~ /^(missing|scaffolded|structural-parity|behavioral-parity|complete)$/ {
        printf "self-host audit: invalid status on row %d\n", NR > "/dev/stderr"; exit 1
    }
    $4 == "complete" && ($5 == "-" || $6 == "-") {
        printf "self-host audit: complete row %s lacks mapped tests or snapshot\n", $1 > "/dev/stderr"; exit 1
    }
' "$ledger"

while IFS=$'\t' read -r id _ self_host_module status _ _; do
    [[ "$id" == "id" || "$status" == "missing" ]] && continue
    matches="$(find "$root/self-host-stage0/src" -type f -name "$self_host_module" | wc -l | tr -d ' ')"
    [[ "$matches" == 1 ]] || {
        echo "self-host audit: $id is $status but resolves to $matches source files named $self_host_module" >&2
        exit 1
    }
done < "$ledger"

# Scaffolds may carry local smoke probes, but a parity status is evidence
# about the frozen Stage0 corpus.  Require both an owner assignment and a
# checked-in, per-module evidence file before a row can advance beyond that
# development state.  The evidence file is deliberately line-based so CI can
# later compare every frozen test record without accepting a prose summary.
while IFS=$'\t' read -r id _ _ status _ snapshot; do
    [[ "$id" == "id" || "$status" == "missing" || "$status" == "scaffolded" ]] && continue
    awk -F '\t' -v id="$id" 'NR > 1 { n = split($2, owners, ","); for (i = 1; i <= n; i++) if (owners[i] == id) found = 1 } END { exit !found }' "$test_owners" || {
        echo "self-host audit: $id is $status but owns no frozen test source" >&2
        exit 1
    }
    [[ "$snapshot" != "-" ]] || {
        echo "self-host audit: $id is $status but has no boundary snapshot" >&2
        exit 1
    }
    evidence="$parity_evidence/$id.tsv"
    [[ -s "$evidence" ]] || {
        echo "self-host audit: $id is $status but lacks frozen-corpus evidence $evidence" >&2
        exit 1
    }
    awk -F '\t' 'NF != 3 || $1 !~ /^crates\/grandiose-stage0\// || $2 !~ /^(pass|expected-failure)$/ || $3 == "" { exit 1 }' "$evidence" || {
        echo "self-host audit: malformed parity evidence for $id" >&2
        exit 1
    }
done < "$ledger"

awk -F '\t' '
    NR == 1 { if ($1 != "layer" || $3 != "status") exit 1; next }
    NF != 5 { printf "self-host audit: malformed bootstrap ledger row %d\n", NR > "/dev/stderr"; exit 1 }
    $1 !~ /^L[1-7]$/ || $3 !~ /^(missing|scaffolded|structural-parity|behavioral-parity|complete)$/ {
        printf "self-host audit: invalid bootstrap ledger row %d\n", NR > "/dev/stderr"; exit 1
    }
' "$stdlib_ledger"
