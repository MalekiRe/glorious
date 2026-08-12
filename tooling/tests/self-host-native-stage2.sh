#!/usr/bin/env bash
# Contract test for retained stage-1 -> native stage-2 preparation.
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)
mkdir -p "$repo_root/target"
scratch=$(mktemp -d "$repo_root/target/self-host-native-stage2-test.XXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
mkdir -p "$scratch/repo/tooling" "$scratch/repo/target/release" "$scratch/bin"
cp "$repo_root/tooling/self-host-native-stage2.sh" "$scratch/repo/tooling/"

cat > "$scratch/bin/readelf" <<'EOF'
#!/usr/bin/env bash
printf 'String dump of section .comment:\n  [ 0] Wild test marker\n'
EOF
chmod +x "$scratch/bin/readelf"

cat > "$scratch/repo/tooling/grbc-native.sh" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
[[ "$1" == --artifact && "$2" == "$STAGE2_TEST_STAGE2" ]]
[[ "$3" == --output && "$4" == "$STAGE2_TEST_OUTPUT" ]]
[[ "$5" == --grvm && "$6" == "$STAGE2_TEST_REPO/target/release/grvm" ]]
[[ "$7" == --grc && "$8" == "$STAGE2_TEST_REPO/target/release/grc" ]]
printf '%s\n' "$*" > "$STAGE2_TEST_LOWER_LOG"
printf '#!/usr/bin/env bash\nexit 0\n' > "$4"
chmod +x "$4"
EOF
cat > "$scratch/repo/tooling/write-native-stage-provenance.sh" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
[[ "$1" == --stage && "$2" == 2 && "$3" == --native && "$4" == "$STAGE2_TEST_OUTPUT" ]]
[[ "$5" == --source && "$6" == "$STAGE2_TEST_SOURCE" ]]
[[ "$7" == --compiler-bytecode && "$8" == "$STAGE2_TEST_STAGE2" ]]
[[ "$9" == --output && "${10}" == "$STAGE2_TEST_PROVENANCE" ]]
printf 'schema\t1\nstage\t2\n' > "${10}"
EOF
chmod +x "$scratch/repo/tooling/grbc-native.sh" "$scratch/repo/tooling/write-native-stage-provenance.sh"
for binary in grvm grc; do printf '#!/usr/bin/env bash\nexit 0\n' > "$scratch/repo/target/release/$binary"; chmod +x "$scratch/repo/target/release/$binary"; done

mkdir -p "$scratch/stage1"
printf 'canonical source\n' > "$scratch/stage1/canonical-source.glorious"
printf 'verified stage two\n' > "$scratch/stage1/stage2.grbc"
printf '#!/usr/bin/env bash\nexit 0\n' > "$scratch/stage1/stage1-native"
chmod +x "$scratch/stage1/stage1-native"
source_hash=$(sha256sum "$scratch/stage1/canonical-source.glorious" | awk '{print $1}')
stage1_native_hash=$(sha256sum "$scratch/stage1/stage1-native" | awk '{print $1}')
stage2_hash=$(sha256sum "$scratch/stage1/stage2.grbc" | awk '{print $1}')
{
    printf 'schema\t1\nstage1-exit\t0\nresult\temitted\n'
    printf 'source-sha256\t%s\nstage1-native-sha256\t%s\nstage2-sha256\t%s\n' "$source_hash" "$stage1_native_hash" "$stage2_hash"
} > "$scratch/stage1/metadata.tsv"
{
    printf 'schema\t1\nstage\t1\noptimization\tO3\nlinker\twild\nnative-sha256\t%s\nsource-sha256\t%s\n' "$stage1_native_hash" "$source_hash"
} > "$scratch/stage1/stage1-provenance.tsv"

stage2_output="$scratch/out/stage2-native"
STAGE2_TEST_STAGE2="$scratch/stage1/stage2.grbc" STAGE2_TEST_OUTPUT="$stage2_output" \
  STAGE2_TEST_REPO="$scratch/repo" STAGE2_TEST_LOWER_LOG="$scratch/lower.log" \
  STAGE2_TEST_SOURCE="$scratch/stage1/canonical-source.glorious" STAGE2_TEST_PROVENANCE="$scratch/out/stage2-provenance.tsv" \
  PATH="$scratch/bin:$PATH" "$scratch/repo/tooling/self-host-native-stage2.sh" run --stage1-dir "$scratch/stage1" --output-dir "$scratch/out" > "$scratch/out.log"
rg -q '^STAGE2_NATIVE' "$scratch/out.log"
[[ -x "$stage2_output" && -s "$scratch/out/stage2-provenance.tsv" ]]
rg -q $'^result\tnative$' "$scratch/out/metadata.tsv"
rg -q -- '--grvm .*/target/release/grvm --grc .*/target/release/grc' "$scratch/lower.log"

if PATH="$scratch/bin:$PATH" "$scratch/repo/tooling/self-host-native-stage2.sh" run --stage1-dir "$scratch/stage1" --output-dir "$scratch/out" > /dev/null 2> "$scratch/reuse.err"; then
    echo 'expected retained stage-2 output reuse to fail' >&2
    exit 1
fi
rg -q 'refusing to overwrite retained evidence' "$scratch/reuse.err"

# A copied evidence directory must still bind the stage-one executable bytes,
# rather than merely carrying an O3/Wild claim in a hand-edited manifest.
printf 'tampered native\n' >> "$scratch/stage1/stage1-native"
rm -f -- "$scratch/lower.log"
if PATH="$scratch/bin:$PATH" "$scratch/repo/tooling/self-host-native-stage2.sh" run --stage1-dir "$scratch/stage1" --output-dir "$scratch/native-tampered" > /dev/null 2> "$scratch/native-tampered.err"; then
  echo 'expected mismatched retained stage-one native hash to fail' >&2
  exit 1
fi
rg -q 'input failed' "$scratch/native-tampered.err"
[[ ! -e "$scratch/lower.log" ]]
printf '#!/usr/bin/env bash\nexit 0\n' > "$scratch/stage1/stage1-native"

printf 'tampered\n' > "$scratch/stage1/stage2.grbc"
rm -f -- "$scratch/lower.log"
if PATH="$scratch/bin:$PATH" "$scratch/repo/tooling/self-host-native-stage2.sh" run --stage1-dir "$scratch/stage1" --output-dir "$scratch/tampered" > /dev/null 2> "$scratch/tampered.err"; then
    echo 'expected mismatched retained stage-two hash to fail' >&2
    exit 1
fi
rg -q 'input failed' "$scratch/tampered.err"
[[ ! -e "$scratch/lower.log" ]]
