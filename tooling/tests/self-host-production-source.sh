#!/usr/bin/env bash
# Contract test for the canonical self-host production source materializer.
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)
mkdir -p "$repo_root/target"
scratch=$(mktemp -d "$repo_root/target/self-host-production-source-test.XXXXXX")
trap 'rm -rf -- "$scratch"' EXIT

mapfile -t inputs < <("$repo_root/tooling/self-host-production-source.sh" inputs)
[[ ${#inputs[@]} -eq 18 ]]
[[ "${inputs[0]}" == "$repo_root/self-host/src/main.glorious" ]]
for input in "${inputs[@]}"; do
    [[ -f "$input" ]]
    [[ "$input" != "$repo_root/self-host/src/probe/"* ]]
done

fake_grc="$scratch/grc"
cat > "$fake_grc" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
[[ "$1" == -O3 && "$2" == --emit && "$3" == monolithic-source && "$4" == -o ]]
output=$5
shift 5
[[ $# -eq 18 ]]
printf 'canonical source\n' > "$output"
EOF
chmod +x "$fake_grc"

output="$scratch/canonical.glorious"
"$repo_root/tooling/self-host-production-source.sh" materialize --grc "$fake_grc" --output "$output" > "$scratch/result"
[[ "$(<"$scratch/result")" == "$output" ]]
[[ "$(<"$output")" == 'canonical source' ]]
