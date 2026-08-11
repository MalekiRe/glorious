#!/usr/bin/env bash
set -euo pipefail

readonly script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
readonly repo_root="$(cd -- "$script_dir/../.." && pwd -P)"
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
for tool in clang wild; do
    cat > "$scratch/bin/$tool" <<'EOF'
#!/usr/bin/env bash
exit 0
EOF
    chmod +x "$scratch/bin/$tool"
done

if GRBC_NATIVE_TEST_ARTIFACT="$artifact" GRBC_NATIVE_TEST_LOG="$scratch/log" PATH="$scratch/bin:$PATH" \
    "$repo_root/tooling/grbc-native.sh" --artifact "$artifact" --output "$output" --grvm "$scratch/grvm" \
    >"$scratch/stdout" 2>"$scratch/stderr"; then
    echo "expected unavailable artifact lowering to fail" >&2
    exit 1
fi
[[ "$(cat "$scratch/log")" == "native-preflight $artifact" ]]
[[ ! -e "$output" ]]
grep -Fq 'verified artifact-to-native lowering is not implemented' "$scratch/stderr"
