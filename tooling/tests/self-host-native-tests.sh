#!/usr/bin/env bash
# Regression coverage for the manifest parser, deterministic selection, and
# failure transparency of tooling/self-host-native-tests.sh.  A fake runner is
# used so this remains a fast tooling test; production invocations always use
# the O3/Wild runner by default.
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)
mkdir -p "$repo_root/target"
scratch=$(mktemp -d "$repo_root/target/self-host-native-tests.XXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
mkdir -p "$scratch/corpus"
printf 'accept\n' > "$scratch/corpus/a.glorious"
printf 'reject\n' > "$scratch/corpus/b.glorious"
printf 'z-reject\treject\ttarget/%s/corpus/b.glorious\n' "$(basename "$scratch")" > "$scratch/corpus.tsv"
printf 'a-accept\taccept\ttarget/%s/corpus/a.glorious\n' "$(basename "$scratch")" >> "$scratch/corpus.tsv"

cat > "$scratch/fake-native" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
output=$1
shift
input=$1
if (($#)) && grep -qx accept "$@"; then
    printf artifact > "$output"
    exit 0
fi
printf 'synthetic rejection for %s\n' "$input" >&2
exit 17
EOF
chmod +x "$scratch/fake-native"
cat > "$scratch/fake-runner" <<EOF
#!/usr/bin/env bash
set -euo pipefail
[[ \$1 == build ]]
printf '%s\\n' '$scratch/fake-native'
EOF
chmod +x "$scratch/fake-runner"

listed=$(G1_SELF_HOST_NATIVE_RUNNER="$scratch/fake-runner" "$repo_root/tooling/self-host-native-tests.sh" list --manifest "$scratch/corpus.tsv")
[[ $listed == $'a-accept\taccept\ttarget/'* ]] || { echo "list was not id-sorted: $listed" >&2; exit 1; }
run_output=$(G1_SELF_HOST_NATIVE_RUNNER="$scratch/fake-runner" "$repo_root/tooling/self-host-native-tests.sh" run --manifest "$scratch/corpus.tsv" 2>&1)
[[ $run_output == *$'PASS\ta-accept\taccept'* ]] || { echo "$run_output" >&2; exit 1; }
[[ $run_output == *$'PASS\tz-reject\treject'* ]] || { echo "$run_output" >&2; exit 1; }
[[ $run_output == *'passed=2 failed=0'* ]] || { echo "$run_output" >&2; exit 1; }

printf 'wrong\taccept\ttarget/%s/corpus/b.glorious\n' "$(basename "$scratch")" > "$scratch/wrong.tsv"
if G1_SELF_HOST_NATIVE_RUNNER="$scratch/fake-runner" "$repo_root/tooling/self-host-native-tests.sh" run --manifest "$scratch/wrong.tsv" >"$scratch/wrong.out" 2>&1; then
    echo "incorrect expectation unexpectedly passed" >&2
    exit 1
fi
rg -q 'expected accept, native compiler exited 17' "$scratch/wrong.out"
rg -q 'synthetic rejection' "$scratch/wrong.out"

printf 'accept\n' > "$scratch/corpus/extra.glorious"
printf 'bundle-accept\taccept\ttarget/%s/corpus/a.glorious\ttarget/%s/corpus/extra.glorious\n' \
    "$(basename "$scratch")" "$(basename "$scratch")" > "$scratch/bundle.tsv"
bundle_output=$(G1_SELF_HOST_NATIVE_RUNNER="$scratch/fake-runner" "$repo_root/tooling/self-host-native-tests.sh" run --manifest "$scratch/bundle.tsv" 2>&1)
[[ $bundle_output == *$'PASS\tbundle-accept\taccept\t'*'extra.glorious'* ]] || { echo "$bundle_output" >&2; exit 1; }
[[ $bundle_output == *'passed=1 failed=0'* ]] || { echo "$bundle_output" >&2; exit 1; }

# Corpus runs are normally ephemeral, but a caller diagnosing native-host
# behavior needs the bytecode and diagnostic for every case to survive.  The
# driver must report the retained directory and leave both artifacts there.
retained_output=$(G1_SELF_HOST_NATIVE_RUNNER="$scratch/fake-runner" "$repo_root/tooling/self-host-native-tests.sh" \
    run --manifest "$scratch/corpus.tsv" --keep-artifacts 2>&1)
retained_dir=$(sed -n 's/^self-host-native-tests: native=.* artifacts=//p' <<<"$retained_output")
[[ -n "$retained_dir" && "$retained_dir" != *$'\n'* ]] || { echo "$retained_output" >&2; exit 1; }
case "$retained_dir" in
    "$repo_root"/target/self-host-native-cache/test-corpus/run.*) ;;
    *) echo "unexpected retained artifact directory: $retained_dir" >&2; exit 1 ;;
esac
[[ -s "$retained_dir/a-accept.grbc" ]] || { echo "retained bytecode is missing" >&2; exit 1; }
[[ -f "$retained_dir/a-accept.log" ]] || { echo "retained accept diagnostic is missing" >&2; exit 1; }
[[ -s "$retained_dir/z-reject.log" ]] || { echo "retained reject diagnostic is missing" >&2; exit 1; }
rm -rf -- "$retained_dir"

# The checked-in corpus is deliberately larger than the original four module
# fixtures and must retain both successful and failing single-source cases.
default_list=$("$repo_root/tooling/self-host-native-tests.sh" list)
[[ $(wc -l <<< "$default_list") -eq 25 ]] || { echo "unexpected native corpus size" >&2; exit 1; }
[[ $default_list == *$'arithmetic-calls\taccept\t'* ]] || { echo "missing arithmetic accept" >&2; exit 1; }
[[ $default_list == *$'invalid-return-type\treject\t'* ]] || { echo "missing type rejection" >&2; exit 1; }
[[ $default_list == *$'ordered-bundle\taccept\t'*$'ordered-bundle/library.glorious'* ]] || { echo "missing ordered source bundle" >&2; exit 1; }
