#!/usr/bin/env bash
# Regression: the native O3 self-host compiler must accept the bootstrap
# `match(subject) { Variant => body }` spelling.  This is deliberately an
# executable-only route: it exercises the production source closure through
# Wild, rather than falling back to the component VM probes.
set -euo pipefail

repository=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)
temporary=$(mktemp -d)
cleanup() { rm -rf "$temporary"; }
trap cleanup EXIT

input="$temporary/match.glorious"
bootstrap_output="$temporary/bootstrap.grbc"
self_host_output="$temporary/self-host.grbc"

printf '%s\n' \
    'enum MatchChoice { Empty, Number(i64) }' \
    '' \
    'match_score(choice: MatchChoice) -> i64 {' \
    '    match(choice) {' \
    '        MatchChoice::Empty => 0,' \
    '        MatchChoice::Number(value) => value' \
    '    }' \
    '}' \
    '' \
    'main() { () }' >"$input"

# Confirm the source remains in the bootstrap corpus first.  Both compilers
# run at O3; the self-host route below additionally requires Wild.
"$repository/tooling/ram-gate.sh" \
    cargo build --release -p grandiose --bin grc
"$repository/tooling/ram-gate.sh" \
    "$repository/target/release/grc" -O3 --emit bytecode -o "$bootstrap_output" "$input"
[[ -s "$bootstrap_output" ]]

"$repository/tooling/self-host-native.sh" run "$self_host_output" "$input"
[[ -s "$self_host_output" ]]
