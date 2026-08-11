#!/usr/bin/env bash
set -euo pipefail

readonly script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
readonly repo_root="$(cd -- "$script_dir/../.." && pwd -P)"
mkdir -p "$repo_root/target"
scratch=$(mktemp -d "$repo_root/target/grbc-native-test.XXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
mkdir -p "$scratch/bin"

artifact="$scratch/stage2.grbc"
output="$scratch/stage2-native"
printf 'verified-fixture\n' > "$artifact"

cat > "$scratch/grvm" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
[[ "$1" == native-preflight && "$2" == "$GRBC_NATIVE_TEST_ARTIFACT" ]]
printf '%s\n' "$*" > "$GRBC_NATIVE_TEST_LOG"
EOF
chmod +x "$scratch/grvm"
cat > "$scratch/grc" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
[[ "$1" == --artifact-llvm-ir && "$2" == "$GRBC_NATIVE_TEST_ARTIFACT" && "$3" == -o && "$4" == "$GRBC_NATIVE_TEST_TMPDIR"/grbc-native.*.ll ]]
[[ -z "${GRBC_NATIVE_TEST_LOWERING_FAIL:-}" ]] || exit 1
printf '%s\n' "$*" > "$GRBC_NATIVE_TEST_GRC_LOG"
printf 'define i32 @main() { ret i32 0 }\n' > "$4"
EOF
chmod +x "$scratch/grc"
cat > "$scratch/bin/clang" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
printf '%s\n' "$*" > "$GRBC_NATIVE_TEST_CLANG_LOG"
[[ "$1" == -x && "$2" == ir && "$3" == -O3 && "$4" == --ld-path=wild && "$5" == "$GRBC_NATIVE_TEST_TMPDIR"/grbc-native.*.ll && "$6" == -o && "$7" == "$GRBC_NATIVE_TEST_OUTPUT" ]]
printf 'native fixture\n' > "$7"
chmod +x "$7"
EOF
chmod +x "$scratch/bin/clang"
cat > "$scratch/bin/wild" <<'EOF'
#!/usr/bin/env bash
exit 0
EOF
chmod +x "$scratch/bin/wild"

if ! GRBC_NATIVE_TEST_ARTIFACT="$artifact" GRBC_NATIVE_TEST_LOG="$scratch/log" \
    GRBC_NATIVE_TEST_GRC_LOG="$scratch/grc.log" GRBC_NATIVE_TEST_CLANG_LOG="$scratch/clang.log" \
    GRBC_NATIVE_TEST_TMPDIR="$scratch" GRBC_NATIVE_TEST_OUTPUT="$output" TMPDIR="$scratch" PATH="$scratch/bin:$PATH" \
    "$repo_root/tooling/grbc-native.sh" --artifact "$artifact" --output "$output" --grvm "$scratch/grvm" --grc "$scratch/grc" \
    >"$scratch/stdout" 2>"$scratch/stderr"; then
    echo "expected supported artifact lowering to succeed" >&2
    cat "$scratch/stderr" >&2
    exit 1
fi
[[ "$(cat "$scratch/log")" == "native-preflight $artifact" ]]
[[ "$(cat "$output")" == "native fixture" ]]
grep -Fq -- '--artifact-llvm-ir' "$scratch/grc.log"
grep -Fq -- '-O3 --ld-path=wild' "$scratch/clang.log"

# A dangling output symlink must be treated as occupied. `test -e` alone
# misses it, but clang follows it when opening its output and could create the
# link target outside this driver-owned output path.
dangling_output="$scratch/dangling-native"
dangling_target="$scratch/dangling-target"
ln -s "$dangling_target" "$dangling_output"
if GRBC_NATIVE_TEST_ARTIFACT="$artifact" GRBC_NATIVE_TEST_LOG="$scratch/dangling-preflight.log" \
    GRBC_NATIVE_TEST_GRC_LOG="$scratch/dangling-grc.log" GRBC_NATIVE_TEST_CLANG_LOG="$scratch/dangling-clang.log" \
    GRBC_NATIVE_TEST_TMPDIR="$scratch" GRBC_NATIVE_TEST_OUTPUT="$dangling_output" TMPDIR="$scratch" PATH="$scratch/bin:$PATH" \
    "$repo_root/tooling/grbc-native.sh" --artifact "$artifact" --output "$dangling_output" --grvm "$scratch/grvm" --grc "$scratch/grc" \
    >"$scratch/dangling.stdout" 2>"$scratch/dangling.stderr"; then
    echo "expected dangling output symlink to be rejected" >&2
    exit 1
fi
[[ ! -e "$dangling_target" ]]
[[ ! -e "$scratch/dangling-preflight.log" ]]
[[ ! -e "$scratch/dangling-grc.log" ]]
[[ ! -e "$scratch/dangling-clang.log" ]]

failed_output="$scratch/unsupported-native"
if GRBC_NATIVE_TEST_ARTIFACT="$artifact" GRBC_NATIVE_TEST_LOG="$scratch/failure-preflight.log" \
    GRBC_NATIVE_TEST_GRC_LOG="$scratch/failure-grc.log" GRBC_NATIVE_TEST_CLANG_LOG="$scratch/failure-clang.log" \
    GRBC_NATIVE_TEST_TMPDIR="$scratch" GRBC_NATIVE_TEST_OUTPUT="$failed_output" GRBC_NATIVE_TEST_LOWERING_FAIL=1 \
    TMPDIR="$scratch" PATH="$scratch/bin:$PATH" \
    "$repo_root/tooling/grbc-native.sh" --artifact "$artifact" --output "$failed_output" --grvm "$scratch/grvm" --grc "$scratch/grc" \
    >"$scratch/failure.stdout" 2>"$scratch/failure.stderr"; then
    echo "expected unsupported artifact lowering to fail closed" >&2
    exit 1
fi
[[ ! -e "$failed_output" ]]
[[ ! -e "$scratch/failure-clang.log" ]]
