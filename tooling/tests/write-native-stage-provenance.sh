#!/usr/bin/env bash
# Contract test for immutable O3/Wild stage provenance generation.
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)
mkdir -p "$repo_root/target"
scratch=$(mktemp -d "$repo_root/target/native-stage-provenance-test.XXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
mkdir -p "$scratch/bin"
cat > "$scratch/bin/readelf" <<'EOF'
#!/usr/bin/env bash
printf 'String dump of section .comment:\n  [ 0] Wild test marker\n'
EOF
cat > "$scratch/native" <<'EOF'
#!/usr/bin/env bash
exit 0
EOF
chmod +x "$scratch/bin/readelf" "$scratch/native"
printf 'canonical source\n' > "$scratch/source.glorious"
printf 'GRBC stage two\n' > "$scratch/stage2.grbc"

PATH="$scratch/bin:$PATH" "$repo_root/tooling/write-native-stage-provenance.sh" \
    --stage 1 --native "$scratch/native" --source "$scratch/source.glorious" --output "$scratch/stage1.tsv" > "$scratch/stage1.out"
rg -q $'^stage\t1$' "$scratch/stage1.tsv"
rg -q $'^optimization\tO3$' "$scratch/stage1.tsv"
rg -q $'^linker\twild$' "$scratch/stage1.tsv"
! rg -q '^compiler-bytecode-sha256' "$scratch/stage1.tsv"

PATH="$scratch/bin:$PATH" "$repo_root/tooling/write-native-stage-provenance.sh" \
    --stage 2 --native "$scratch/native" --source "$scratch/source.glorious" \
    --compiler-bytecode "$scratch/stage2.grbc" --output "$scratch/stage2.tsv" > "$scratch/stage2.out"
expected=$(sha256sum "$scratch/stage2.grbc" | awk '{print $1}')
rg -q "^compiler-bytecode-sha256[[:space:]]$expected$" "$scratch/stage2.tsv"

if PATH="$scratch/bin:$PATH" "$repo_root/tooling/write-native-stage-provenance.sh" \
    --stage 2 --native "$scratch/native" --source "$scratch/source.glorious" \
    --compiler-bytecode "$scratch/stage2.grbc" --output "$scratch/stage2.tsv" > "$scratch/overwrite.out" 2>&1; then
    echo 'expected existing provenance to be retained' >&2
    exit 1
fi
rg -q 'refusing to overwrite' "$scratch/overwrite.out"
