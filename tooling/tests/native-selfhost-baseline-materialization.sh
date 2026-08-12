#!/usr/bin/env bash
# Contract: a baseline is published once from a private O3/Wild cache and each
# consumer receives byte-identical private copies.  Neither direction permits
# an overwrite, so parallel /tmp worktrees cannot share mutable state.
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)
mkdir -p "$repo_root/target"
scratch=$(mktemp -d "$repo_root/target/native-selfhost-baseline-test.XXXXXX")
cleanup() { chmod -R u+w -- "$scratch" 2>/dev/null || true; rm -rf -- "$scratch"; }
trap cleanup EXIT

producer="$scratch/producer"
consumer="$scratch/consumer"
baseline="$scratch/baseline"
mkdir -p "$producer/target/self-host-native-cache" "$consumer"
git -C "$producer" init -q
git -C "$producer" config user.email baseline-test@example.invalid
git -C "$producer" config user.name baseline-test
touch "$producer/input"
git -C "$producer" add input
git -C "$producer" commit -qm fixture
git -C "$consumer" init -q

cache="$producer/target/self-host-native-cache"
printf 'native compiler bytes\n' > "$cache/grandiose-self-host-native"
chmod +x "$cache/grandiose-self-host-native"
printf 'exact-fingerprint;optimization=O3\n' > "$cache/build.fingerprint"
printf 'schema=1\nworktree=%s\ncreated-head=test\noptimization=O3\n' "$producer" > "$cache/native-route.manifest"
mkdir -p "$cache/objects"
printf '\177ELF private object bytes\n' > "$cache/objects/fixture.o"
printf 'schema=1\ndigest=fixture\nobject-blake3=test\nabi=test\n' > "$cache/objects/fixture.manifest"

mkdir -p "$scratch/bin"
cat > "$scratch/bin/readelf" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
[[ "$1" == -p && "$2" == .comment ]]
printf 'String dump of section .comment:\n  [     0]  wild\n'
SH
chmod +x "$scratch/bin/readelf"

PATH="$scratch/bin:$PATH" "$repo_root/tooling/publish-native-selfhost-baseline.sh" \
  --worktree "$producer" --output "$baseline" > "$scratch/published"
[[ "$(<"$scratch/published")" == "$baseline" ]]
[[ ! -w "$baseline/grandiose-self-host-native" ]]
[[ ! -w "$baseline/build.fingerprint" ]]
# The objects are part of the immutable baseline too.  The publisher used to
# protect just the top-level `objects/` directory while leaving its payloads
# writable, which made an accidental shared-cache mutation possible.
[[ ! -w "$baseline/objects/fixture.o" ]]
[[ ! -w "$baseline/objects/fixture.manifest" ]]
# The baseline contract includes both members of every durable object entry;
# a seed must never receive an object without the manifest that validates it.
grep -Fq $'file\tobjects/fixture.o\t' "$baseline/manifest.tsv"
grep -Fq $'file\tobjects/fixture.manifest\t' "$baseline/manifest.tsv"

"$repo_root/tooling/seed-native-selfhost-cache.sh" --worktree "$consumer" --baseline "$baseline" > "$scratch/seeded"
consumer_cache="$consumer/target/self-host-native-cache"
cmp "$baseline/grandiose-self-host-native" "$consumer_cache/grandiose-self-host-native"
cmp "$baseline/build.fingerprint" "$consumer_cache/build.fingerprint"
cmp "$baseline/objects/fixture.o" "$consumer_cache/objects/fixture.o"
cmp "$baseline/objects/fixture.manifest" "$consumer_cache/objects/fixture.manifest"
[[ -f "$consumer_cache/manifest.tsv" ]]

# A seed is deliberately a real private copy, never a hard-link or a shared
# writable cache.  A consumer must be free to replace its local artifact on a
# later O3 rebuild without changing what a concurrently-created worktree sees.
[[ "$(stat -c '%d:%i' "$baseline/grandiose-self-host-native")" != \
   "$(stat -c '%d:%i' "$consumer_cache/grandiose-self-host-native")" ]]
[[ "$(stat -c '%d:%i' "$baseline/objects/fixture.o")" != \
   "$(stat -c '%d:%i' "$consumer_cache/objects/fixture.o")" ]]
baseline_binary_sum=$(sha256sum "$baseline/grandiose-self-host-native" | awk '{print $1}')
chmod u+w "$consumer_cache/grandiose-self-host-native"
printf 'consumer-private rebuild\n' >> "$consumer_cache/grandiose-self-host-native"
[[ "$(sha256sum "$baseline/grandiose-self-host-native" | awk '{print $1}')" == "$baseline_binary_sum" ]]
! cmp -s "$baseline/grandiose-self-host-native" "$consumer_cache/grandiose-self-host-native"
object_sum=$(sha256sum "$baseline/objects/fixture.o" | awk '{print $1}')
printf 'consumer-private object mutation\n' >> "$consumer_cache/objects/fixture.o"
[[ "$(sha256sum "$baseline/objects/fixture.o" | awk '{print $1}')" == "$object_sum" ]]
! cmp -s "$baseline/objects/fixture.o" "$consumer_cache/objects/fixture.o"

if "$repo_root/tooling/seed-native-selfhost-cache.sh" --worktree "$consumer" --baseline "$baseline" > /dev/null 2> "$scratch/reseed.err"; then
  echo 'expected seeder to reject an existing private cache' >&2
  exit 1
fi
grep -Fq 'refusing to overwrite private cache' "$scratch/reseed.err"
if PATH="$scratch/bin:$PATH" "$repo_root/tooling/publish-native-selfhost-baseline.sh" \
  --worktree "$producer" --output "$baseline" > /dev/null 2> "$scratch/republish.err"; then
  echo 'expected publisher to reject baseline replacement' >&2
  exit 1
fi
grep -Fq 'refusing to replace baseline' "$scratch/republish.err"
