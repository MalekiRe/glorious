#!/bin/sh
# Run every test program on every engine and say which differ from the
# interpreter running the bytecode as it was written, without the rewriting
# done when a program is loaded. Run from the repository's root after `lake build glorious` and
# `cargo build --release` in `vm`. Needs clang.
set -eu
root=$(pwd)
glorious="$root/.lake/build/bin/glorious"
vm="$root/vm/target/release/glorious-vm"
lib="$root/vm/target/release/libglorious_vm.a"
dir=$(mktemp -d)
trap 'rm -rf "$dir"' EXIT
"$glorious" cases "$dir" > /dev/null

one() {
    gbc=$1
    stem=${gbc%.gbc}
    input=$(cat "$stem.in")
    # shellcheck disable=SC2086
    want=$("$vm" --no-opt --backend=interp "$gbc" $input 2>&1; echo "exit $?")
    for backend in interp x86 mix; do
        # shellcheck disable=SC2086
        got=$("$vm" --backend=$backend "$gbc" $input 2>&1; echo "exit $?")
        [ "$got" = "$want" ] || echo "$gbc: $backend differs"
    done
    "$vm" --emit-llvm "$gbc" > "$stem.ll"
    if clang -O2 -Wno-override-module "$stem.ll" "$lib" -o "$stem.exe" -lpthread -ldl -lm 2> "$stem.err"; then
        for backend in llvm mix; do
            # shellcheck disable=SC2086
            got=$(GLORIOUS_BACKEND=$backend "$stem.exe" $input 2>&1; echo "exit $?")
            [ "$got" = "$want" ] || echo "$gbc: built with LLVM, $backend differs"
        done
    else
        echo "$gbc: clang failed"
    fi
}

export vm lib
count=0
for gbc in "$dir"/*.gbc; do
    one "$gbc" &
    count=$((count + 1))
    [ $((count % 16)) -eq 0 ] && wait
done
wait
echo "$count programs on the interpreter, x86-64, LLVM and mixtures of them"
