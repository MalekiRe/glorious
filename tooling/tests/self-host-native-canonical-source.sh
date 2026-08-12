#!/usr/bin/env bash
# Contract: canonical-source must delegate its input closure to the shared
# production-source helper.  This protects provenance from drifting from the
# native build and catches accidental references to a private module list.
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)
mkdir -p "$repo_root/target"
scratch=$(mktemp -d "$repo_root/target/self-host-native-canonical-source.XXXXXX")
cleanup() { rm -rf -- "$scratch"; }
trap cleanup EXIT

fake_repo="$scratch/repo"
mkdir -p "$fake_repo/tooling" "$fake_repo/target/release"
cp "$repo_root/tooling/self-host-native.sh" "$fake_repo/tooling/self-host-native.sh"
chmod +x "$fake_repo/tooling/self-host-native.sh"

cat >"$fake_repo/tooling/ram-gate.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
exit 99
SH
chmod +x "$fake_repo/tooling/ram-gate.sh"

cat >"$fake_repo/tooling/self-host-production-source.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
[[ "$1" == materialize ]]
shift
[[ "$1" == --output ]]
output=$2
shift 2
[[ "$1" == --grc ]]
[[ "$2" == "$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)/target/release/grc" ]]
printf '%s\n' 'canonical production source' >"$output"
printf '%s\n' "$output"
SH
chmod +x "$fake_repo/tooling/self-host-production-source.sh"

git -C "$fake_repo" init -q
git -C "$fake_repo" config user.email tooling-test@example.invalid
git -C "$fake_repo" config user.name tooling-test
touch "$fake_repo/.gitkeep"
git -C "$fake_repo" add .gitkeep
git -C "$fake_repo" commit -qm fixture

output="$scratch/canonical.glorious"
"$fake_repo/tooling/self-host-native.sh" canonical-source "$output" >"$scratch/out"
[[ -s "$output" ]]
[[ "$(<"$output")" == 'canonical production source' ]]
[[ "$(<"$scratch/out")" == "$output" ]]

if "$fake_repo/tooling/self-host-native.sh" canonical-source "$output" >"$scratch/repeated.out" 2>&1; then
    echo 'expected canonical-source to refuse overwriting evidence' >&2
    exit 1
fi
grep -Fq 'refusing to overwrite canonical source' "$scratch/repeated.out"
