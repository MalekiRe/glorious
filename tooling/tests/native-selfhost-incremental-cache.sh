#!/usr/bin/env bash
# Fast contract test for the developer native-selfhost runner. It uses a fake
# O3 compiler, so it checks private cache routing without compiling self-host.
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)
mkdir -p "$repo_root/target"
scratch=$(mktemp -d "$repo_root/target/native-selfhost-incremental-cache.XXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
mkdir -p "$scratch/bin"

input="$scratch/input.glorious"
output="$scratch/output.grbc"
cache="$scratch/private-cache"
printf 'main() { () }\n' > "$input"

cat > "$scratch/grc" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
printf '%s\n' "$*" >> "$G1_NATIVE_SELFHOST_TEST_LOG"
args=("$@")
output=''
for ((index = 0; index < ${#args[@]}; index++)); do
    if [[ ${args[index]} == -o ]]; then
        output=${args[index + 1]}
        break
    fi
done
[[ -n $output ]]
printf '#!/usr/bin/env bash\nexit 0\n' > "$output"
chmod +x "$output"
EOF
chmod +x "$scratch/grc"
cat > "$scratch/bin/wild" <<'EOF'
#!/usr/bin/env bash
exit 0
EOF
chmod +x "$scratch/bin/wild"

run=("$repo_root/tooling/native-selfhost.sh" "$output" "$input")
G1_NATIVE_SELFHOST_CACHE_DIR="$cache" G1_NATIVE_SELFHOST_TEST_LOG="$scratch/grc.log" \
    G1_GRC_BIN="$scratch/grc" PATH="$scratch/bin:$PATH" "${run[@]}"

line=$(<"$scratch/grc.log")
[[ $line == *'--emit executable '* ]] || {
    echo "native-selfhost did not route through its private incremental cache: $line" >&2
    exit 1
}

# A matching second invocation must reuse the executable and avoid compilation.
G1_NATIVE_SELFHOST_CACHE_DIR="$cache" G1_NATIVE_SELFHOST_TEST_LOG="$scratch/grc.log" \
    G1_GRC_BIN="$scratch/grc" PATH="$scratch/bin:$PATH" "${run[@]}"
[[ $(wc -l < "$scratch/grc.log") -eq 1 ]]
[[ -f "$cache/.private-cache" && -f "$cache/manifest" && -x "$cache/grandiose-self-host" ]]

bash -n "$repo_root/tooling/native-selfhost.sh"
