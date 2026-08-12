#!/usr/bin/env bash
# Contract test for native-only stage convergence evidence and failure retention.
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)
mkdir -p "$repo_root/target"
scratch=$(mktemp -d "$repo_root/target/self-host-native-convergence-test.XXXXXX")
trap 'rm -rf -- "$scratch"' EXIT

mkdir -p "$scratch/bin"
cat > "$scratch/bin/readelf" <<'EOF'
#!/usr/bin/env bash
printf 'String dump of section .comment:\n  [ 0] Wild test marker\n'
EOF
cat > "$scratch/stage1" <<'EOF'
#!/usr/bin/env bash
printf 'stage-two-bytes' > "$1"
EOF
cat > "$scratch/stage2-equal" <<'EOF'
#!/usr/bin/env bash
printf 'stage-two-bytes' > "$1"
EOF
cat > "$scratch/stage2-different" <<'EOF'
#!/usr/bin/env bash
printf 'stage-three-bytes' > "$1"
EOF
chmod +x "$scratch/bin/readelf" "$scratch/stage1" "$scratch/stage2-equal" "$scratch/stage2-different"
printf 'compiler source\n' > "$scratch/input.glorious"

write_manifest() {
    local path=$1 stage=$2 executable=$3 bytecode=${4:-}
    {
        printf 'schema\t1\nstage\t%s\noptimization\tO3\nlinker\twild\n' "$stage"
        printf 'native-sha256\t%s\n' "$(sha256sum "$executable" | awk '{print $1}')"
        printf 'source-sha256\t%s\n' "$(sha256sum "$scratch/input.glorious" | awk '{print $1}')"
        [[ -z "$bytecode" ]] || printf 'compiler-bytecode-sha256\t%s\n' "$bytecode"
    } > "$path"
}

stage2_hash=$(printf 'stage-two-bytes' | sha256sum | awk '{print $1}')
write_manifest "$scratch/stage1.tsv" 1 "$scratch/stage1"
write_manifest "$scratch/stage2-equal.tsv" 2 "$scratch/stage2-equal" "$stage2_hash"
PATH="$scratch/bin:$PATH" "$repo_root/tooling/self-host-native-convergence.sh" \
    --stage1-native "$scratch/stage1" --stage1-provenance "$scratch/stage1.tsv" \
    --stage2-native "$scratch/stage2-equal" --stage2-provenance "$scratch/stage2-equal.tsv" \
    --source "$scratch/input.glorious" --output-dir "$scratch/equal" > "$scratch/equal.out"
rg -q '^CONVERGED' "$scratch/equal.out"
rg -q $'^result\tbyte-identical$' "$scratch/equal/metadata.tsv"

write_manifest "$scratch/stage2-different.tsv" 2 "$scratch/stage2-different" "$stage2_hash"
if PATH="$scratch/bin:$PATH" "$repo_root/tooling/self-host-native-convergence.sh" \
    --stage1-native "$scratch/stage1" --stage1-provenance "$scratch/stage1.tsv" \
    --stage2-native "$scratch/stage2-different" --stage2-provenance "$scratch/stage2-different.tsv" \
    --source "$scratch/input.glorious" --output-dir "$scratch/different" > "$scratch/different.out" 2> "$scratch/different.err"; then
    echo 'expected differing stages to fail' >&2
    exit 1
fi
rg -q $'^result\tnot-byte-identical$' "$scratch/different/metadata.tsv"
rg -q 'stage2-sha256' "$scratch/different/stage2-stage3.diff"
rg -q 'first differing byte offsets' "$scratch/different/stage2-stage3.diff"
