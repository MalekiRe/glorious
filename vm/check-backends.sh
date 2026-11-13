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
# A program that agreed on every engine is not run again while its bytecode,
# its input, the VM and the compiler are what they were: each is remembered
# by a hash of all of them. `GLORIOUS_BACKENDS_CACHE=` (empty) runs everything.
cache=${GLORIOUS_BACKENDS_CACHE-${XDG_CACHE_HOME:-$HOME/.cache}/glorious-backends}
[ -z "$cache" ] || mkdir -p "$cache"
engines=$( (sha256sum "$vm" "$lib"; clang --version) | sha256sum | cut -d' ' -f1)

one() {
    gbc=$1
    stem=${gbc%.gbc}
    input=$(cat "$stem.in")
    seen=
    if [ -n "$cache" ]; then
        seen=$cache/$( (echo "$engines"; sha256sum < "$gbc"; sha256sum < "$stem.in") | sha256sum | cut -d' ' -f1)
        [ -e "$seen" ] && return 0
    fi
    differs=$(one_run "$gbc" "$stem" "$input")
    if [ -n "$differs" ]; then echo "$differs"; elif [ -n "$seen" ]; then : > "$seen"; fi
}

one_run() {
    gbc=$1
    stem=$2
    input=$3
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

export vm lib cache engines
count=0
for gbc in "$dir"/*.gbc; do
    one "$gbc" &
    count=$((count + 1))
    [ $((count % 16)) -eq 0 ] && wait
done
wait
echo "$count programs on the interpreter, x86-64, LLVM and mixtures of them"
