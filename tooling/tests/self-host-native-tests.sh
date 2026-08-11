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
input=$2
if grep -qx accept "$input"; then
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

# The checked-in corpus is deliberately larger than the original four module
# fixtures and must retain both successful and failing single-source cases.
default_list=$("$repo_root/tooling/self-host-native-tests.sh" list)
[[ $(wc -l <<< "$default_list") -eq 19 ]] || { echo "unexpected native corpus size" >&2; exit 1; }
[[ $default_list == *$'arithmetic-calls\taccept\t'* ]] || { echo "missing arithmetic accept" >&2; exit 1; }
[[ $default_list == *$'invalid-return-type\treject\t'* ]] || { echo "missing type rejection" >&2; exit 1; }
