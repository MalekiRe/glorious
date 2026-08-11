#!/usr/bin/env bash
# Contract test: stage-1 evidence is native/provenance-bound and retained.
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)
mkdir -p "$repo_root/target"
scratch=$(mktemp -d "$repo_root/target/self-host-native-stage1-test.XXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
mkdir -p "$scratch/repo/tooling" "$scratch/bin"
cp "$repo_root/tooling/self-host-native-stage1.sh" "$scratch/repo/tooling/"
printf 'clean binding fixture\n' > "$scratch/repo/binding"
git -C "$scratch/repo" init -q
git -C "$scratch/repo" config user.email native-stage1-test@example.invalid
git -C "$scratch/repo" config user.name native-stage1-test
git -C "$scratch/repo" add tooling/self-host-native-stage1.sh
git -C "$scratch/repo" add binding
git -C "$scratch/repo" commit -qm 'stage1 runner fixture'

cat > "$scratch/native" <<'EOF'
#!/usr/bin/env bash
printf 'stage-two-bytes' > "$1"
EOF
chmod +x "$scratch/native"
cat > "$scratch/repo/tooling/self-host-native.sh" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
case "$1" in
  canonical-source) printf 'canonical self host\n' > "$2" ;;
  provenance)
    source=$2; output=$3
    {
      printf 'schema\t1\nstage\t1\noptimization\tO3\nlinker\twild\n'
      printf 'native-sha256\t%s\n' "$(sha256sum "$NATIVE_STAGE1_TEST_NATIVE" | awk '{print $1}')"
      printf 'source-sha256\t%s\n' "$(sha256sum "$source" | awk '{print $1}')"
    } > "$output"
    ;;
  build) printf '%s\n' "$NATIVE_STAGE1_TEST_NATIVE" ;;
  *) exit 2 ;;
esac
EOF
chmod +x "$scratch/repo/tooling/self-host-native.sh"
cat > "$scratch/bin/readelf" <<'EOF'
#!/usr/bin/env bash
printf 'Wild linker marker\n'
EOF
chmod +x "$scratch/bin/readelf"

NATIVE_STAGE1_TEST_NATIVE="$scratch/native" PATH="$scratch/bin:$PATH" \
  "$scratch/repo/tooling/self-host-native-stage1.sh" run --output-dir "$scratch/run" > "$scratch/out"
rg -q '^STAGE1_EMITTED' "$scratch/out"
[[ "$(cat "$scratch/run/stage2.grbc")" == stage-two-bytes ]]
rg -q $'^result\temitted$' "$scratch/run/metadata.tsv"
rg -q $'^repository-head\t[0-9a-f]{40}$' "$scratch/run/metadata.tsv"
[[ -s "$scratch/run/canonical-source.glorious" && -s "$scratch/run/stage1-provenance.tsv" ]]
for log in canonical-source provenance build stage1; do [[ -f "$scratch/run/$log.log" ]]; done

if NATIVE_STAGE1_TEST_NATIVE="$scratch/native" PATH="$scratch/bin:$PATH" \
  "$scratch/repo/tooling/self-host-native-stage1.sh" run --output-dir "$scratch/run" > /dev/null 2> "$scratch/reuse.err"; then
  echo 'expected retained output directory reuse to fail' >&2
  exit 1
fi
rg -q 'refusing to overwrite retained evidence' "$scratch/reuse.err"

# A retained claim must not bind a native executable to merely the last commit
# while tracked source state has since changed.
printf 'dirty binding fixture\n' > "$scratch/repo/binding"
if NATIVE_STAGE1_TEST_NATIVE="$scratch/native" PATH="$scratch/bin:$PATH" \
  "$scratch/repo/tooling/self-host-native-stage1.sh" run --output-dir "$scratch/dirty-run" > /dev/null 2> "$scratch/dirty.err"; then
  echo 'expected dirty tracked checkout to be rejected' >&2
  exit 1
fi
rg -q 'refuses a checkout with unstaged tracked edits' "$scratch/dirty.err"
