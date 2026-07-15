#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

normalize() {
  sed -E \
    -e $'s/\\x1B\\[[0-9;]*[mK]//g' \
    -e "s#${root}#<repo>#g" \
    -e "s#${tmp}#<tmp>#g"
}

set +e
"$root/compiler/grc" \
  "$root/compiler/tests/cases/invalid-integer.gr" \
  "$tmp/invalid.ll" >"$tmp/invalid.raw" 2>&1
invalid_status=$?
set -e
test "$invalid_status" -ne 0
normalize <"$tmp/invalid.raw" >"$tmp/invalid.stderr"
diff -u "$root/compiler/tests/golden/invalid-integer.stderr" "$tmp/invalid.stderr"

for case_name in invalid-character unknown-string-escape missing-arrow division-by-zero unknown-callable wrong-arity \
  type-mismatch unknown-type cyclic-type-alias missing-struct-field \
  unknown-projected-field unknown-enum-variant duplicate-local \
  wrong-generic-arity non-exhaustive-handler \
  non-exhaustive-terminal-payload unknown-effect-row \
  terminal-effect-quantity unpropagated-effect resumptive-missing-binding \
  unpropagated-callback-effect \
  underused-owned-value overused-owned-value underused-pattern-binding \
  destroyed-twice \
  shadowed-destroy \
  drop-non-nominal effectful-drop duplicate-drop drop-without-single-use \
  partial-move-from-drop partial-pattern-move-from-drop \
  drop-hook-name-collision \
  borrowed-temporary dereference-non-reference \
  overlapping-borrows \
  access-during-unique-borrow \
  nested-unique-borrow-access \
  whole-and-field-borrow \
  unique-reborrow-from-shared \
  parent-reference-during-reborrow \
  escaping-local-borrow \
  nested-borrow-escape \
  escaping-parameter-borrow \
  escaping-call-result-borrow \
  underused-generic-use widened-structural-use unavailable-to-unit \
  zst-is-not-available forged-available \
  runs-in-without-fn \
  incompatible-post-environments \
  resumption-quantity runs-in-callback-quantity \
  runs-in-transitive-callback-quantity \
  runs-in-recursive-callback-quantity \
  runs-in-correlated-alternatives \
  non-exhaustive-resumptive-handler; do
  set +e
  "$root/compiler/grc" \
    "$root/compiler/tests/cases/${case_name}.gr" \
    "$tmp/${case_name}.ll" >"$tmp/${case_name}.raw" 2>&1
  case_status=$?
  set -e
  test "$case_status" -ne 0
  normalize <"$tmp/${case_name}.raw" >"$tmp/${case_name}.stderr"
  diff -u \
    "$root/compiler/tests/golden/${case_name}.stderr" \
    "$tmp/${case_name}.stderr"
done

"$root/compiler/grc" \
  "$root/compiler/tests/cases/truncated-exit.gr" \
  "$tmp/truncated.ll" >"$tmp/warning.raw" 2>&1
normalize <"$tmp/warning.raw" >"$tmp/warning.stderr"
diff -u "$root/compiler/tests/golden/truncated-exit.stderr" "$tmp/warning.stderr"
llvm-as "$tmp/truncated.ll" -o "$tmp/truncated.bc"

echo "compiler diagnostic snapshots passed"
