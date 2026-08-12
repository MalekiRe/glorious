#!/usr/bin/env bash
# Contract: canonical-source builds a missing bootstrap compiler in the
# helper's checkout, even when an enclosing stage runner was launched from a
# different worktree.
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)
mkdir -p "$repo_root/target"
scratch=$(mktemp -d "$repo_root/target/self-host-production-source-worktree-test.XXXXXX")
trap 'rm -rf -- "$scratch"' EXIT

fixture="$scratch/snapshot"
caller="$scratch/live-caller"
mkdir -p "$fixture/tooling" "$fixture/self-host/src" "$caller" "$scratch/bin"
cp "$repo_root/tooling/self-host-production-source.sh" "$fixture/tooling/"
cp "$repo_root/tooling/ram-gate.sh" "$fixture/tooling/"

# Materialization validates the complete production closure before it asks
# Cargo for the bootstrap compiler.  Empty modules are sufficient because the
# fake grc below only witnesses the output handoff, not language compilation.
while IFS= read -r input; do
    relative=${input#"$repo_root/self-host/src/"}
    mkdir -p "$(dirname -- "$fixture/self-host/src/$relative")"
    : > "$fixture/self-host/src/$relative"
done < <("$repo_root/tooling/self-host-production-source.sh" inputs)

cat > "$scratch/bin/cargo" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
[[ "$1" == build ]]
mkdir -p target/release
cat > target/release/grc <<'GRC'
#!/usr/bin/env bash
set -euo pipefail
[[ "$1" == -O3 && "$2" == --emit && "$3" == monolithic-source && "$4" == -o ]]
printf 'canonical snapshot source\n' > "$5"
GRC
chmod +x target/release/grc
EOF
chmod +x "$scratch/bin/cargo"

(
    cd "$caller"
    PATH="$scratch/bin:$PATH" "$fixture/tooling/self-host-production-source.sh" \
        materialize --output "$scratch/canonical.glorious"
)

[[ -x "$fixture/target/release/grc" ]]
[[ ! -e "$caller/target/release/grc" ]]
[[ "$(cat "$scratch/canonical.glorious")" == 'canonical snapshot source' ]]
