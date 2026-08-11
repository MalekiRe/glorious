#!/usr/bin/env bash
# Contract test: stage-1 evidence is native/provenance-bound and retained.
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)
mkdir -p "$repo_root/target"
scratch=$(mktemp -d "$repo_root/target/self-host-native-stage1-test.XXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
mkdir -p "$scratch/repo/tooling" "$scratch/repo/target/release" "$scratch/bin"
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
cat > "$scratch/repo/target/release/grvm" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
[[ "$1" == native-preflight && "$2" == "$NATIVE_STAGE1_TEST_STAGE2" ]]
printf '%s\n' "$*" > "$NATIVE_STAGE1_TEST_VERIFY_LOG"
[[ "${NATIVE_STAGE1_TEST_VERIFY_FAIL:-0}" != 1 ]]
EOF
chmod +x "$scratch/repo/target/release/grvm"
cat > "$scratch/repo/tooling/self-host-native.sh" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
route_root=$(cd -- "$(dirname -- "$0")/.." && pwd -P)
case "$1" in
  canonical-source) printf 'canonical self host\n' > "$2" ;;
  provenance)
    source=$2; output=$3
    if [[ "${NATIVE_STAGE1_TEST_SALVAGE_FAIL:-0}" == 1 ]]; then
      objects="$route_root/target/self-host-native-cache/objects"
      mkdir -p "$objects"
      key=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
      printf '\177ELF validated durable object\n' > "$objects/$key.o"
      printf 'schema=1\ndigest=%s\nobject-blake3=%s\nabi=test\n' \
        "$key" bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb > "$objects/$key.manifest"
      printf 'partial object\n' > "$objects/cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc.o"
      exit 28
    fi
    {
      printf 'schema\t1\nstage\t1\noptimization\tO3\nlinker\twild\n'
      printf 'native-sha256\t%s\n' "$(sha256sum "$NATIVE_STAGE1_TEST_NATIVE" | awk '{print $1}')"
      printf 'source-sha256\t%s\n' "$(sha256sum "$source" | awk '{print $1}')"
    } > "$output"
    ;;
  build)
    if [[ "${NATIVE_STAGE1_TEST_ADVANCE_HEAD:-0}" == 1 ]]; then
      git -C "$NATIVE_STAGE1_TEST_REPO" commit --allow-empty -qm 'advance live head during native build'
    fi
    printf '%s\n' "$NATIVE_STAGE1_TEST_NATIVE"
    ;;
  *) exit 2 ;;
esac
EOF
chmod +x "$scratch/repo/tooling/self-host-native.sh"
git -C "$scratch/repo" add tooling/self-host-native.sh
git -C "$scratch/repo" commit -qm 'native tool fixture'
initial_head=$(git -C "$scratch/repo" rev-parse HEAD)
cat > "$scratch/bin/readelf" <<'EOF'
#!/usr/bin/env bash
printf 'Wild linker marker\n'
EOF
chmod +x "$scratch/bin/readelf"

NATIVE_STAGE1_TEST_NATIVE="$scratch/native" NATIVE_STAGE1_TEST_STAGE2="$scratch/run/stage2.grbc" \
  NATIVE_STAGE1_TEST_VERIFY_LOG="$scratch/verify.log" PATH="$scratch/bin:$PATH" \
  "$scratch/repo/tooling/self-host-native-stage1.sh" run --output-dir "$scratch/run" > "$scratch/out"
rg -q '^STAGE1_EMITTED' "$scratch/out"
[[ "$(cat "$scratch/run/stage2.grbc")" == stage-two-bytes ]]
rg -q $'^result\temitted$' "$scratch/run/metadata.tsv"
rg -q $'^repository-head\t[0-9a-f]{40}$' "$scratch/run/metadata.tsv"
[[ -s "$scratch/run/canonical-source.glorious" && -s "$scratch/run/stage1-provenance.tsv" ]]
for log in canonical-source provenance build stage1; do [[ -f "$scratch/run/$log.log" ]]; done
[[ -f "$scratch/run/verify-stage2.log" ]]
[[ "$(cat "$scratch/verify.log")" == "native-preflight $scratch/run/stage2.grbc" ]]

# A native build can outlive ordinary integration commits. The retained run
# must continue from its clean preflight snapshot, rather than rejecting the
# now-advanced live checkout or mixing its later files into stage 1.
NATIVE_STAGE1_TEST_NATIVE="$scratch/native" NATIVE_STAGE1_TEST_STAGE2="$scratch/snapshot-run/stage2.grbc" \
  NATIVE_STAGE1_TEST_VERIFY_LOG="$scratch/snapshot-verify.log" NATIVE_STAGE1_TEST_REPO="$scratch/repo" \
  NATIVE_STAGE1_TEST_ADVANCE_HEAD=1 PATH="$scratch/bin:$PATH" \
  "$scratch/repo/tooling/self-host-native-stage1.sh" run --output-dir "$scratch/snapshot-run" > "$scratch/snapshot.out"
rg -q '^STAGE1_EMITTED' "$scratch/snapshot.out"
rg -q "^snapshot-head[[:space:]]$initial_head$" "$scratch/snapshot-run/metadata.tsv"
[[ "$(git -C "$scratch/repo" rev-parse HEAD)" != "$initial_head" ]]
[[ -x "$scratch/snapshot-run/stage1-native" ]]
[[ "$(cat "$scratch/snapshot-verify.log")" == "native-preflight $scratch/snapshot-run/stage2.grbc" ]]

if NATIVE_STAGE1_TEST_NATIVE="$scratch/native" NATIVE_STAGE1_TEST_STAGE2="$scratch/invalid-run/stage2.grbc" \
  NATIVE_STAGE1_TEST_VERIFY_LOG="$scratch/invalid-verify.log" NATIVE_STAGE1_TEST_VERIFY_FAIL=1 PATH="$scratch/bin:$PATH" \
  "$scratch/repo/tooling/self-host-native-stage1.sh" run --output-dir "$scratch/invalid-run" > /dev/null 2> "$scratch/invalid.err"; then
  echo 'expected an unverifiable stage-two artifact to be rejected' >&2
  exit 1
fi
rg -q 'verify-stage2 failed' "$scratch/invalid.err"
rg -q $'^phase\tverify-stage2$' "$scratch/invalid-run/metadata.tsv"
rg -q $'^result\tfailed$' "$scratch/invalid-run/metadata.tsv"

# Failure cleanup removes the disposable snapshot, but a complete durable
# object/manifest pair is retained as a private retry seed. A partial object
# never crosses that boundary.
if NATIVE_STAGE1_TEST_NATIVE="$scratch/native" NATIVE_STAGE1_TEST_SALVAGE_FAIL=1 PATH="$scratch/bin:$PATH" \
  "$scratch/repo/tooling/self-host-native-stage1.sh" run --output-dir "$scratch/salvage-run" > /dev/null 2> "$scratch/salvage.err"; then
  echo 'expected failing provenance build to retain a retry seed' >&2
  exit 1
fi
rg -q 'provenance failed' "$scratch/salvage.err"
salvage_key=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
salvage_objects="$scratch/salvage-run/native-cache-retry-seed/objects"
[[ -f "$salvage_objects/$salvage_key.o" ]]
[[ -f "$salvage_objects/$salvage_key.manifest" ]]
[[ ! -e "$salvage_objects/cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc.o" ]]
rg -q $'^native-cache-retry-objects\t1$' "$scratch/salvage-run/metadata.tsv"

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
