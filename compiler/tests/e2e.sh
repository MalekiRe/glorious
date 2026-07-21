#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

runtime_library="$tmp/libgrandiose-native-runtime.so"
clang -shared -fPIC -O2 -o "$runtime_library" \
  "$root/compiler/runtime/native_entry.c"
lli() { command lli --dlopen="$runtime_library" "$@"; }

"$root/compiler/grc" \
  "$root/compiler/examples/arithmetic.gr" \
  "$tmp/arithmetic.ll"
llvm-as "$tmp/arithmetic.ll" -o "$tmp/arithmetic.bc"

grep -q '%t0 = mul i64 5, 8' "$tmp/arithmetic.ll"
grep -q '%t1 = add i64 2, %t0' "$tmp/arithmetic.ll"

set +e
lli "$tmp/arithmetic.bc"
exit_status=$?
set -e
test "$exit_status" -eq 42

echo "compiler arithmetic/LLVM end-to-end test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/extended-comparisons.gr" \
  "$tmp/extended-comparisons.ll"
llvm-as "$tmp/extended-comparisons.ll" -o "$tmp/extended-comparisons.bc"
grep -q 'icmp sge i64' "$tmp/extended-comparisons.ll"
grep -q 'icmp sle i64' "$tmp/extended-comparisons.ll"
grep -q 'icmp ne i64' "$tmp/extended-comparisons.ll"
set +e
lli "$tmp/extended-comparisons.bc"
extended_comparisons_status=$?
set -e
test "$extended_comparisons_status" -eq 42

echo "compiler extended comparison-operator LLVM test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/calls.gr" \
  "$tmp/calls.ll"
llvm-as "$tmp/calls.ll" -o "$tmp/calls.bc"
grep -q 'define i64 @grandiose_add(i64 %arg_lhs, i64 %arg_rhs)' "$tmp/calls.ll"
grep -q 'add i64 %arg_lhs, %arg_rhs' "$tmp/calls.ll"
grep -q 'call i64 @grandiose_add(i64 %arg_base, i64 2)' "$tmp/calls.ll"
grep -q 'call i64 @grandiose_answer(i64 40)' "$tmp/calls.ll"
set +e
lli "$tmp/calls.bc"
calls_status=$?
set -e
test "$calls_status" -eq 42

echo "compiler module/call end-to-end test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/i32.gr" \
  "$tmp/i32.ll"
llvm-as "$tmp/i32.ll" -o "$tmp/i32.bc"
grep -q 'define i32 @grandiose_add(i32 %arg_lhs, i32 %arg_rhs)' "$tmp/i32.ll"
grep -q 'call i32 @grandiose_add(i32 40, i32 2)' "$tmp/i32.ll"
grep -q 'ret i32 %result' "$tmp/i32.ll"
if grep -q 'trunc i64' "$tmp/i32.ll"; then
  echo "unexpected i64 truncation in native i32 module" >&2
  exit 1
fi
set +e
lli "$tmp/i32.bc"
i32_status=$?
set -e
test "$i32_status" -eq 42

echo "compiler i32 signature/type/LLVM end-to-end test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/type-alias.gr" \
  "$tmp/type-alias.ll"
llvm-as "$tmp/type-alias.ll" -o "$tmp/type-alias.bc"
grep -q 'define i32 @grandiose_add(i32 %arg_lhs, i32 %arg_rhs)' "$tmp/type-alias.ll"
grep -q 'call i32 @grandiose_add(i32 40, i32 2)' "$tmp/type-alias.ll"
set +e
lli "$tmp/type-alias.bc"
alias_status=$?
set -e
test "$alias_status" -eq 42

echo "compiler order-independent type-alias end-to-end test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/struct.gr" \
  "$tmp/struct.ll"
llvm-as "$tmp/struct.ll" -o "$tmp/struct.bc"
grep -q '%struct.Pair = type { i32, i32 }' "$tmp/struct.ll"
grep -q 'define %struct.Pair @grandiose_make_pair()' "$tmp/struct.ll"
grep -q 'insertvalue %struct.Pair undef, i32 40, 0' "$tmp/struct.ll"
grep -q 'insertvalue %struct.Pair %t0, i32 2, 1' "$tmp/struct.ll"
grep -q 'extractvalue %struct.Pair %arg_pair, 0' "$tmp/struct.ll"
grep -q 'extractvalue %struct.Pair %arg_pair, 1' "$tmp/struct.ll"
grep -q 'call i32 @grandiose_consume(%struct.Pair %t0)' "$tmp/struct.ll"
set +e
lli "$tmp/struct.bc"
struct_status=$?
set -e
test "$struct_status" -eq 42

echo "compiler nominal struct construction/LLVM end-to-end test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/enum.gr" \
  "$tmp/enum.ll"
llvm-as "$tmp/enum.ll" -o "$tmp/enum.bc"
grep -q '%enum.Message = type { i32, i32, i32, i64 }' "$tmp/enum.ll"
grep -q 'insertvalue %enum.Message undef, i32 1, 0' "$tmp/enum.ll"
grep -q 'insertvalue %enum.Message %t0, i32 40, 1' "$tmp/enum.ll"
grep -q 'insertvalue %enum.Message %t1, i32 2, 2' "$tmp/enum.ll"
grep -q 'call i32 @grandiose_consume(%enum.Message %t0)' "$tmp/enum.ll"
set +e
lli "$tmp/enum.bc"
enum_status=$?
set -e
test "$enum_status" -eq 42

echo "compiler payload enum construction/LLVM end-to-end test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/strings.gr" \
  "$tmp/strings.ll"
llvm-as "$tmp/strings.ll" -o "$tmp/strings.bc"
grep -q '@grandiose_string_.*private unnamed_addr constant.*\\0A\\22' \
  "$tmp/strings.ll"
grep -q 'define ptr @grandiose_identity(ptr %arg_value)' "$tmp/strings.ll"
set +e
lli "$tmp/strings.bc"
strings_status=$?
set -e
test "$strings_status" -eq 42

echo "compiler String literal/ABI LLVM test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/string-patterns.gr" \
  "$tmp/string-patterns.ll"
llvm-as "$tmp/string-patterns.ll" -o "$tmp/string-patterns.bc"
grep -q 'call i32 @strcmp' "$tmp/string-patterns.ll"
set +e
lli "$tmp/string-patterns.bc"
string_patterns_status=$?
set -e
test "$string_patterns_status" -eq 42

echo "compiler ordered String-literal pattern LLVM test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/lists.gr" \
  "$tmp/lists.ll"
llvm-as "$tmp/lists.ll" -o "$tmp/lists.bc"
grep -q '@grandiose_empty_list = private constant i64 0' "$tmp/lists.ll"
grep -q 'call void @llvm.memcpy.p0.p0.i64' "$tmp/lists.ll"
set +e
lli "$tmp/lists.bc"
lists_status=$?
set -e
test "$lists_status" -eq 42

echo "compiler persistent List literal/core-intrinsic LLVM test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/terminal-nested-patterns.gr" \
  "$tmp/terminal-nested-patterns.ll"
llvm-as "$tmp/terminal-nested-patterns.ll" \
  -o "$tmp/terminal-nested-patterns.bc"
grep -q 'icmp eq i32 .* 42' "$tmp/terminal-nested-patterns.ll"
grep -q '_case_1_pattern_1' "$tmp/terminal-nested-patterns.ll"
grep -q '_step_case_1_pattern_1' "$tmp/terminal-nested-patterns.ll"
set +e
lli "$tmp/terminal-nested-patterns.bc"
terminal_nested_patterns_status=$?
set -e
test "$terminal_nested_patterns_status" -eq 42

echo "compiler ordered nested terminal-pattern LLVM test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/locals.gr" \
  "$tmp/locals.ll"
llvm-as "$tmp/locals.ll" -o "$tmp/locals.bc"
grep -Eq '%local_pair[_0-9]* = select i1 true, %struct.Pair' "$tmp/locals.ll"
grep -Eq '%local_left[_0-9]* = select i1 true, i32' "$tmp/locals.ll"
grep -Eq 'extractvalue %struct.Pair %local_pair[_0-9]*, 0' "$tmp/locals.ll"
grep -Eq 'extractvalue %struct.Pair %local_pair[_0-9]*, 1' "$tmp/locals.ll"
set +e
lli "$tmp/locals.bc"
locals_status=$?
set -e
test "$locals_status" -eq 42

echo "compiler typed lexical block/SSA local end-to-end test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/inferred-locals.gr" \
  "$tmp/inferred-locals.ll"
llvm-as "$tmp/inferred-locals.ll" -o "$tmp/inferred-locals.bc"
grep -Eq '%local_base[_0-9]* = select i1 true, i64' "$tmp/inferred-locals.ll"
grep -Eq '%local_offset[_0-9]* = select i1 true, i64 2, i64 2' \
  "$tmp/inferred-locals.ll"
set +e
lli "$tmp/inferred-locals.bc"
inferred_locals_status=$?
set -e
test "$inferred_locals_status" -eq 42

echo "compiler inferred lexical-local end-to-end test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/generics.gr" \
  "$tmp/generics.ll"
llvm-as "$tmp/generics.ll" -o "$tmp/generics.bc"
grep -q '%enum.Result__i32__unit = type { i32, i32, {} }' "$tmp/generics.ll"
grep -q '%enum.Result__unit__unit = type { i32, {}, {} }' "$tmp/generics.ll"
grep -q 'define internal i32 @grandiose_identity__i32(i32 %arg_value)' "$tmp/generics.ll"
grep -q 'call i32 @grandiose_identity__i32(i32 40)' "$tmp/generics.ll"
grep -q 'icmp sgt i32 %arg_value, 0' "$tmp/generics.ll"
grep -q 'select i1 %t0, %enum.Result__unit__unit' "$tmp/generics.ll"
grep -q 'define internal i32 @grandiose_run__i32__fn0_value__i32({ ptr, ptr, ptr } %arg_body)' "$tmp/generics.ll"
grep -q '%closure_captures = load { i32 }, ptr %closure_env' "$tmp/generics.ll"
grep -q 'call i32 %t0(ptr %t1)' "$tmp/generics.ll"
grep -q 'call i32 @grandiose_run__i32__fn0_value__i32({ ptr, ptr, ptr }' "$tmp/generics.ll"
grep -q 'define internal %enum.Result__i32__unit @grandiose_if__unit__unit__i32__fn0_value__i32' "$tmp/generics.ll"
grep -q 'define internal i32 @grandiose_else__i32__unit__fn0_value__i32' "$tmp/generics.ll"
test "$(grep -c 'switch i32' "$tmp/generics.ll")" -eq 4
grep -q 'phi %enum.Result__i32__unit' "$tmp/generics.ll"
grep -q 'phi i32' "$tmp/generics.ll"
set +e
lli "$tmp/generics.bc"
generics_status=$?
set -e
test "$generics_status" -eq 42

echo "compiler generic Result/alias/monomorphization end-to-end test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/polymorphic-globals.gr" \
  "$tmp/polymorphic-globals.ll"
llvm-as "$tmp/polymorphic-globals.ll" -o "$tmp/polymorphic-globals.bc"
grep -q 'define internal %enum.Result__i64__unit @grandiose_\$grandiose.global\$None__i64()' \
  "$tmp/polymorphic-globals.ll"
grep -q 'call %enum.Result__i64__unit @grandiose_\$grandiose.global\$None__i64()' \
  "$tmp/polymorphic-globals.ll"
set +e
lli "$tmp/polymorphic-globals.bc"
polymorphic_globals_status=$?
set -e
test "$polymorphic_globals_status" -eq 42

echo "compiler polymorphic immutable-global end-to-end test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/effectful-callback.gr" \
  "$tmp/effectful-callback.ll"
llvm-as "$tmp/effectful-callback.ll" -o "$tmp/effectful-callback.bc"
grep -q 'define %grandiose.effect_step @grandiose_closure_.*_step__i32' \
  "$tmp/effectful-callback.ll"
grep -q 'define internal %grandiose.effect_step @grandiose_run__i32__fn0_step__i32' \
  "$tmp/effectful-callback.ll"
set +e
lli "$tmp/effectful-callback.bc"
effectful_callback_status=$?
set -e
test "$effectful_callback_status" -eq 42

echo "compiler effect-polymorphic Fn ABI end-to-end test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/direct-resumptive.gr" \
  "$tmp/direct-resumptive.ll"
llvm-as "$tmp/direct-resumptive.ll" -o "$tmp/direct-resumptive.bc"
if grep -q 'call %grandiose.effect_step @grandiose_ask' \
  "$tmp/direct-resumptive.ll"; then
  echo "statically handled [1,1] operation unexpectedly used the step ABI" >&2
  exit 1
fi
set +e
lli "$tmp/direct-resumptive.bc"
direct_resumptive_status=$?
set -e
test "$direct_resumptive_status" -eq 42

echo "compiler direct [1,1] resumption-evidence test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/direct-resumptive-transitive.gr" \
  "$tmp/direct-resumptive-transitive.ll"
llvm-as "$tmp/direct-resumptive-transitive.ll" \
  -o "$tmp/direct-resumptive-transitive.bc"
if sed -n '/define i32 @grandiose_main/,/^}/p' \
  "$tmp/direct-resumptive-transitive.ll" | \
  grep -q 'call %grandiose.effect_step'; then
  echo "transitive [1,1] evidence unexpectedly used the step ABI" >&2
  exit 1
fi
set +e
lli "$tmp/direct-resumptive-transitive.bc"
direct_resumptive_transitive_status=$?
set -e
test "$direct_resumptive_transitive_status" -eq 42

echo "compiler transitive [1,1] resumption-evidence test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/unused-effectful-callback.gr" \
  "$tmp/unused-effectful-callback.ll"
llvm-as "$tmp/unused-effectful-callback.ll" \
  -o "$tmp/unused-effectful-callback.bc"
grep -q 'define %grandiose.effect_step @grandiose_closure_.*_step__i32' \
  "$tmp/unused-effectful-callback.ll"
grep -q 'define internal i32 @grandiose_ignore__i32__fn0_step__i32' \
  "$tmp/unused-effectful-callback.ll"
set +e
lli "$tmp/unused-effectful-callback.bc"
unused_effectful_callback_status=$?
set -e
test "$unused_effectful_callback_status" -eq 42

echo "compiler unused delayed-effect evidence test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/effectful-if.gr" \
  "$tmp/effectful-if.ll"
llvm-as "$tmp/effectful-if.ll" -o "$tmp/effectful-if.bc"
grep -q 'define internal %grandiose.effect_step @grandiose_if_.*fn0_step__i32' \
  "$tmp/effectful-if.ll"
grep -q 'define internal i32 @grandiose_else_.*fn0_value__i32' \
  "$tmp/effectful-if.ll"
grep -q 'define internal %enum.Result__i32__unit @grandiose_if_.*fn0_value__i32' \
  "$tmp/effectful-if.ll"
grep -q 'define internal %grandiose.effect_step @grandiose_else_.*fn0_step__i32' \
  "$tmp/effectful-if.ll"
if grep -Eq 'call %grandiose.effect_step @grandiose_(if|else)_' \
  "$tmp/effectful-if.ll"; then
  echo "effectful lazy selector escaped the step inliner" >&2
  exit 1
fi
set +e
lli "$tmp/effectful-if.bc"
effectful_if_status=$?
set -e
test "$effectful_if_status" -eq 84

echo "compiler source-defined effectful if/else end-to-end test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/correlated-resumption-branches.gr" \
  "$tmp/correlated-resumption-branches.ll"
llvm-as "$tmp/correlated-resumption-branches.ll" \
  -o "$tmp/correlated-resumption-branches.bc"
test "$(grep -c 'define %grandiose.effect_step @grandiose_closure_.*_step__i32' \
  "$tmp/correlated-resumption-branches.ll")" -eq 2
grep -q 'call ptr @grandiose_new_resumption' \
  "$tmp/correlated-resumption-branches.ll"
grep -q 'define internal %grandiose.effect_step @grandiose_choose_.*fn0_step__i32' \
  "$tmp/correlated-resumption-branches.ll"
set +e
lli "$tmp/correlated-resumption-branches.bc"
correlated_resumption_branches_status=$?
set -e
test "$correlated_resumption_branches_status" -eq 83

echo "compiler correlated RunsIn post-environment test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/principal-use.gr" \
  "$tmp/principal-use.ll"
llvm-as "$tmp/principal-use.ll" -o "$tmp/principal-use.bc"
grep -q 'define i32 @grandiose_consume' "$tmp/principal-use.ll"
set +e
lli "$tmp/principal-use.bc"
principal_use_status=$?
set -e
test "$principal_use_status" -eq 42

echo "compiler principal Use interval test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/owned-correlated-branches.gr" \
  "$tmp/owned-correlated-branches.ll"
llvm-as "$tmp/owned-correlated-branches.ll" \
  -o "$tmp/owned-correlated-branches.bc"
test "$(grep -c 'define i32 @grandiose_closure_' \
  "$tmp/owned-correlated-branches.ll")" -eq 2
set +e
lli "$tmp/owned-correlated-branches.bc"
owned_correlated_branches_status=$?
set -e
test "$owned_correlated_branches_status" -eq 42

echo "compiler correlated owned-use branch test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/conditional-parameter-drop.gr" \
  "$tmp/conditional-parameter-drop.ll"
llvm-as "$tmp/conditional-parameter-drop.ll" \
  -o "$tmp/conditional-parameter-drop.bc"
grep -q '%drop_active_arg_resource_' \
  "$tmp/conditional-parameter-drop.ll"
grep -q 'call i1 @grandiose_claim_drop_state(ptr %drop_active_arg_resource_' \
  "$tmp/conditional-parameter-drop.ll"
grep -q 'call void @grandiose_release_drop_state(ptr %drop_active_arg_resource_' \
  "$tmp/conditional-parameter-drop.ll"
grep -q 'call void @free(ptr %closure_env)' \
  "$tmp/conditional-parameter-drop.ll"
set +e
lli "$tmp/conditional-parameter-drop.bc"
conditional_parameter_drop_status=$?
set -e
test "$conditional_parameter_drop_status" -eq 42

echo "compiler shared conditional parameter/capture drop-state test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/runs-in-environments.gr" \
  "$tmp/runs-in-environments.ll"
llvm-as "$tmp/runs-in-environments.ll" -o "$tmp/runs-in-environments.bc"
grep -q 'grandiose_choose__environment__incoming_choose_' \
  "$tmp/runs-in-environments.ll"
grep -q '__environment__after_choose_' \
  "$tmp/runs-in-environments.ll"
set +e
lli "$tmp/runs-in-environments.bc"
runs_in_environments_status=$?
set -e
test "$runs_in_environments_status" -eq 42

echo "compiler fresh RunsIn environment/post-environment test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/incremental-available.gr" \
  "$tmp/incremental-available.ll"
llvm-as "$tmp/incremental-available.ll" -o "$tmp/incremental-available.bc"
grep -q 'define internal {} @grandiose_defer_available__environment__incoming_defer_available_' \
  "$tmp/incremental-available.ll"
grep -q 'define internal i32 @grandiose_continue_available__environment__incoming_defer_available_' \
  "$tmp/incremental-available.ll"
set +e
lli "$tmp/incremental-available.bc"
incremental_available_status=$?
set -e
test "$incremental_available_status" -eq 42

echo "compiler incremental Available/RunsIn ownership-chain test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/explicit-destroy.gr" \
  "$tmp/explicit-destroy.ll"
llvm-as "$tmp/explicit-destroy.ll" -o "$tmp/explicit-destroy.bc"
grep -q 'define internal {} @grandiose_destroy__struct_Holder__fn0_value__i32' \
  "$tmp/explicit-destroy.ll"
grep -A8 'define internal {} @grandiose_destroy__struct_Holder__fn0_value__i32' \
  "$tmp/explicit-destroy.ll" | grep -q 'call void %t'
grep -q 'define internal {} @grandiose_destroy__enum_Resource__fn0_value__i32' \
  "$tmp/explicit-destroy.ll"
grep -A16 'define internal {} @grandiose_destroy__enum_Resource__fn0_value__i32' \
  "$tmp/explicit-destroy.ll" | grep -q 'switch i32'
grep -A20 'define internal {} @grandiose_destroy__enum_Resource__fn0_value__i32' \
  "$tmp/explicit-destroy.ll" | grep -q 'call void %t'
grep -A20 'define internal i32 @grandiose_make_and_ignore' \
  "$tmp/explicit-destroy.ll" | grep -q 'call void %t'
set +e
lli "$tmp/explicit-destroy.bc"
explicit_destroy_status=$?
set -e
test "$explicit_destroy_status" -eq 42

echo "compiler explicit reverse-structural/active-variant destruction test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/custom-drop.gr" \
  "$tmp/custom-drop.ll"
llvm-as "$tmp/custom-drop.ll" -o "$tmp/custom-drop.bc"
test "$(grep -c 'call {} @grandiose_drop_hook_struct_Outer' \
  "$tmp/custom-drop.ll")" -eq 2
test "$(grep -c 'call {} @grandiose_drop_hook_struct_Inner' \
  "$tmp/custom-drop.ll")" -eq 2
outer_hook_line="$(grep -n 'call {} @grandiose_drop_hook_struct_Outer' \
  "$tmp/custom-drop.ll" | head -1 | cut -d: -f1)"
inner_extract_line="$(grep -n 'extractvalue %struct.Outer' \
  "$tmp/custom-drop.ll" | head -1 | cut -d: -f1)"
inner_hook_line="$(grep -n 'call {} @grandiose_drop_hook_struct_Inner' \
  "$tmp/custom-drop.ll" | head -1 | cut -d: -f1)"
test "$outer_hook_line" -lt "$inner_extract_line"
test "$inner_extract_line" -lt "$inner_hook_line"
set +e
lli "$tmp/custom-drop.bc"
custom_drop_status=$?
set -e
test "$custom_drop_status" -eq 42

echo "compiler custom Drop hook-before-reverse-structural cleanup test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/handled-drop.gr" \
  "$tmp/handled-drop.ll"
llvm-as "$tmp/handled-drop.ll" -o "$tmp/handled-drop.bc"
grep -q 'define {} @grandiose_drop_hook_struct_Resource' \
  "$tmp/handled-drop.ll"
grep -A12 'define {} @grandiose_drop_hook_struct_Resource' \
  "$tmp/handled-drop.ll" | grep -q 'switch'
set +e
lli "$tmp/handled-drop.bc"
handled_drop_status=$?
set -e
test "$handled_drop_status" -eq 42

echo "compiler internally handled Drop-effect test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/references.gr" \
  "$tmp/references.ll"
llvm-as "$tmp/references.ll" -o "$tmp/references.bc"
grep -q 'define i32 @grandiose_read_shared(ptr %arg_value)' \
  "$tmp/references.ll"
grep -q 'define i32 @grandiose_read_unique(ptr %arg_value)' \
  "$tmp/references.ll"
grep -q 'alloca i32' "$tmp/references.ll"
grep -q 'load i32, ptr %arg_value' "$tmp/references.ll"
grep -q 'call ptr @grandiose_forward_shared' "$tmp/references.ll"
if grep -A8 'define i32 @grandiose_reborrow_shared' \
  "$tmp/references.ll" | grep -q 'alloca'; then
  echo "shared reborrow unexpectedly allocated snapshot storage" >&2
  exit 1
fi
if grep -A8 'define i32 @grandiose_reborrow_unique' \
  "$tmp/references.ll" | grep -q 'alloca'; then
  echo "unique reborrow unexpectedly allocated snapshot storage" >&2
  exit 1
fi
grep -A12 'define i32 @grandiose_reuse_parent_after_reborrow' \
  "$tmp/references.ll" | grep -Eq 'load i32, ptr %local_child[_0-9]*'
grep -A12 'define i32 @grandiose_reuse_parent_after_reborrow' \
  "$tmp/references.ll" | grep -Eq 'load i32, ptr %local_parent[_0-9]*'
set +e
lli "$tmp/references.bc"
references_status=$?
set -e
test "$references_status" -eq 42

echo "compiler shared/unique reference LLVM test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/available-to-unit.gr" \
  "$tmp/available-to-unit.ll"
llvm-as "$tmp/available-to-unit.ll" -o "$tmp/available-to-unit.bc"
grep -q 'define internal {} @grandiose_available_to_unit__struct_OptionalEnvironment' \
  "$tmp/available-to-unit.ll"
grep -q 'define {} @grandiose_close_available({}' \
  "$tmp/available-to-unit.ll"
set +e
lli "$tmp/available-to-unit.bc"
available_to_unit_status=$?
set -e
test "$available_to_unit_status" -eq 42

echo "compiler Available-to-unit intrinsic test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/effect-row.gr" \
  "$tmp/effect-row.ll"
llvm-as "$tmp/effect-row.ll" -o "$tmp/effect-row.bc"
grep -Eq 'define (%grandiose.effect_step|i32) @grandiose_answer\(\)' "$tmp/effect-row.ll"
set +e
lli "$tmp/effect-row.bc"
effect_row_status=$?
set -e
test "$effect_row_status" -eq 42

echo "compiler generic callable effect-row end-to-end test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/effect-row-alias.gr" \
  "$tmp/effect-row-alias.ll"
llvm-as "$tmp/effect-row-alias.ll" -o "$tmp/effect-row-alias.bc"
set +e
lli "$tmp/effect-row-alias.bc"
effect_row_alias_status=$?
set -e
test "$effect_row_alias_status" -eq 42

echo "compiler effect-row alias expansion test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/effect-request.gr" \
  "$tmp/effect-request.ll"
llvm-as "$tmp/effect-request.ll" -o "$tmp/effect-request.bc"
grep -q 'define %grandiose.effect_step @grandiose_ask_value()' \
  "$tmp/effect-request.ll"
grep -q 'define %grandiose.effect_step @grandiose_resume_ask_value_[0-9]' \
  "$tmp/effect-request.ll"
grep -q 'insertvalue %grandiose.effect_step %t3, ptr @grandiose_resume_ask_value_[0-9].*, 4' \
  "$tmp/effect-request.ll"
grep -q 'define %grandiose.effect_step @grandiose_forward_ask()' \
  "$tmp/effect-request.ll"
grep -q 'call %grandiose.effect_step @grandiose_ask_value()' \
  "$tmp/effect-request.ll"
set +e
lli "$tmp/effect-request.bc"
effect_request_status=$?
set -e
test "$effect_request_status" -eq 42

echo "compiler suspended effect-request ABI end-to-end test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/cross-call-resumption.gr" \
  "$tmp/cross-call-resumption.ll"
llvm-as "$tmp/cross-call-resumption.ll" -o "$tmp/cross-call-resumption.bc"
grep -q 'define %grandiose.effect_step @grandiose_effect_continuation_ask_plus_' \
  "$tmp/cross-call-resumption.ll"
grep -q 'call %grandiose.effect_step @grandiose_bind_step_ask_plus_' \
  "$tmp/cross-call-resumption.ll"
grep -q 'call %grandiose.effect_step @grandiose_ask_plus(i32 40, i32 0)' \
  "$tmp/cross-call-resumption.ll"
grep -q 'call i32 @grandiose_finish(i32 %t' \
  "$tmp/cross-call-resumption.ll"
grep -q 'load { i32 }, ptr' "$tmp/cross-call-resumption.ll"
grep -q '%runtime_pattern_seed_' "$tmp/cross-call-resumption.ll"
grep -q 'call void @free(ptr %t10)' "$tmp/cross-call-resumption.ll"
grep -q 'define i32 @grandiose_runtime_handler_' \
  "$tmp/cross-call-resumption.ll"
grep -q 'call %grandiose.effect_step %t' "$tmp/cross-call-resumption.ll"
set +e
lli "$tmp/cross-call-resumption.bc"
cross_call_resumption_status=$?
set -e
test "$cross_call_resumption_status" -eq 42

echo "compiler cross-call deep handler dispatch end-to-end test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/multiple-suspensions.gr" \
  "$tmp/multiple-suspensions.ll"
llvm-as "$tmp/multiple-suspensions.ll" \
  -o "$tmp/multiple-suspensions.bc"
test "$(grep -c 'define %grandiose.effect_step @grandiose_effect_continuation_twice_step_' \
  "$tmp/multiple-suspensions.ll")" -eq 2
test "$(grep -c 'call %grandiose.effect_step @grandiose_ask' \
  "$tmp/multiple-suspensions.ll")" -eq 2
grep -q '%local_offset_' "$tmp/multiple-suspensions.ll"
grep -q '%local_between_' "$tmp/multiple-suspensions.ll"
set +e
lli "$tmp/multiple-suspensions.bc"
multiple_suspensions_status=$?
set -e
test "$multiple_suspensions_status" -eq 42

echo "compiler recursive multi-suspension block-MIR test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/prefix-before-handler.gr" \
  "$tmp/prefix-before-handler.ll"
llvm-as "$tmp/prefix-before-handler.ll" \
  -o "$tmp/prefix-before-handler.bc"
grep -q '%local_adjusted_' "$tmp/prefix-before-handler.ll"
grep -q 'add i32 %pattern_value_.*, %local_adjusted_' \
  "$tmp/prefix-before-handler.ll"
set +e
lli "$tmp/prefix-before-handler.bc"
prefix_before_handler_status=$?
set -e
test "$prefix_before_handler_status" -eq 42

echo "compiler pure-prefix handler-capture block-MIR test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/discarded-suspension.gr" \
  "$tmp/discarded-suspension.ll"
llvm-as "$tmp/discarded-suspension.ll" \
  -o "$tmp/discarded-suspension.bc"
test "$(grep -c 'define %grandiose.effect_step @grandiose_resume_run_' \
  "$tmp/discarded-suspension.ll")" -eq 2
grep -q 'define %grandiose.effect_step @grandiose_effect_continuation_run_step_' \
  "$tmp/discarded-suspension.ll"
grep -q '%continuation_discard_' "$tmp/discarded-suspension.ll"
set +e
lli "$tmp/discarded-suspension.bc"
discarded_suspension_status=$?
set -e
test "$discarded_suspension_status" -eq 42

echo "compiler discarded direct-suspension block-MIR test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/effectful-expression.gr" \
  "$tmp/effectful-expression.ll"
llvm-as "$tmp/effectful-expression.ll" \
  -o "$tmp/effectful-expression.bc"
grep -q '%continuation___step_left_' "$tmp/effectful-expression.ll"
grep -q 'add i32 %continuation___step_left_.*, %continuation___step_right_' \
  "$tmp/effectful-expression.ll"
test "$(grep -c 'call %grandiose.effect_step @grandiose_ask' \
  "$tmp/effectful-expression.ll")" -eq 2
set +e
lli "$tmp/effectful-expression.bc"
effectful_expression_status=$?
set -e
test "$effectful_expression_status" -eq 42

echo "compiler effectful binary-expression CPS test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/general-handled-expression.gr" \
  "$tmp/general-handled-expression.ll"
llvm-as "$tmp/general-handled-expression.ll" \
  -o "$tmp/general-handled-expression.bc"
test "$(grep -c 'define %grandiose.effect_step @grandiose_forward_handler_' \
  "$tmp/general-handled-expression.ll")" -ge 2
grep -q 'define %grandiose.effect_step @grandiose_effect_continuation_handler_' \
  "$tmp/general-handled-expression.ll"
grep -q 'add i32 %continuation___step_left_' \
  "$tmp/general-handled-expression.ll"
set +e
lli "$tmp/general-handled-expression.bc"
general_handled_expression_status=$?
set -e
test "$general_handled_expression_status" -eq 42

echo "compiler general handled-expression continuation-MIR test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/lexical-handler-patterns.gr" \
  "$tmp/lexical-handler-patterns.ll"
llvm-as "$tmp/lexical-handler-patterns.ll" \
  -o "$tmp/lexical-handler-patterns.bc"
grep -q 'icmp eq i32 .* 0' "$tmp/lexical-handler-patterns.ll"
grep -q 'forward_runtime_clause_next_' \
  "$tmp/lexical-handler-patterns.ll"
grep -q 'define %grandiose.effect_step @grandiose_effect_continuation_handler_' \
  "$tmp/lexical-handler-patterns.ll"
set +e
lli "$tmp/lexical-handler-patterns.bc"
lexical_handler_patterns_status=$?
set -e
test "$lexical_handler_patterns_status" -eq 42

echo "compiler ordered lexical-handler pattern-MIR test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/effectful-call-argument.gr" \
  "$tmp/effectful-call-argument.ll"
llvm-as "$tmp/effectful-call-argument.ll" \
  -o "$tmp/effectful-call-argument.bc"
grep -q '%continuation___step_argument_' \
  "$tmp/effectful-call-argument.ll"
grep -q 'call i32 @grandiose_finish(i32 %continuation___step_argument_' \
  "$tmp/effectful-call-argument.ll"
set +e
lli "$tmp/effectful-call-argument.bc"
effectful_call_argument_status=$?
set -e
test "$effectful_call_argument_status" -eq 42

echo "compiler effectful call-argument CPS test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/effectful-perform-argument.gr" \
  "$tmp/effectful-perform-argument.ll"
llvm-as "$tmp/effectful-perform-argument.ll" \
  -o "$tmp/effectful-perform-argument.bc"
grep -q '%continuation___step_argument_' \
  "$tmp/effectful-perform-argument.ll"
grep -q 'store { i32 } %t.*, ptr %t' \
  "$tmp/effectful-perform-argument.ll"
set +e
lli "$tmp/effectful-perform-argument.bc"
effectful_perform_argument_status=$?
set -e
test "$effectful_perform_argument_status" -eq 42

echo "compiler effectful perform-argument CPS test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/effectful-enum-payload.gr" \
  "$tmp/effectful-enum-payload.ll"
llvm-as "$tmp/effectful-enum-payload.ll" \
  -o "$tmp/effectful-enum-payload.bc"
grep -q '%continuation___step_argument_' \
  "$tmp/effectful-enum-payload.ll"
grep -q 'insertvalue %enum.Wrapped .*%continuation___step_argument_' \
  "$tmp/effectful-enum-payload.ll"
set +e
lli "$tmp/effectful-enum-payload.bc"
effectful_enum_payload_status=$?
set -e
test "$effectful_enum_payload_status" -eq 42

echo "compiler effectful enum-payload CPS test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/effectful-struct-fields.gr" \
  "$tmp/effectful-struct-fields.ll"
llvm-as "$tmp/effectful-struct-fields.ll" \
  -o "$tmp/effectful-struct-fields.bc"
grep -q '%continuation___step_field_' \
  "$tmp/effectful-struct-fields.ll"
test "$(grep -c 'call %grandiose.effect_step @grandiose_ask' \
  "$tmp/effectful-struct-fields.ll")" -eq 2
grep -q 'insertvalue %struct.Pair .*%continuation___step_field_' \
  "$tmp/effectful-struct-fields.ll"
set +e
lli "$tmp/effectful-struct-fields.bc"
effectful_struct_fields_status=$?
set -e
test "$effectful_struct_fields_status" -eq 42

echo "compiler effectful struct-field CPS test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/cross-call-multishot.gr" \
  "$tmp/cross-call-multishot.ll"
llvm-as "$tmp/cross-call-multishot.ll" -o "$tmp/cross-call-multishot.bc"
grep -q 'define i32 @grandiose_runtime_handler_' \
  "$tmp/cross-call-multishot.ll"
test "$(grep -c 'call i32 @grandiose_runtime_handler_' \
  "$tmp/cross-call-multishot.ll")" -eq 3
grep -q 'insertvalue %grandiose.effect_step %t.*, i64 2, 7' \
  "$tmp/cross-call-multishot.ll"
grep -q 'call void @grandiose_release_resumption_environment' \
  "$tmp/cross-call-multishot.ll"
set +e
lli "$tmp/cross-call-multishot.bc"
cross_call_multishot_status=$?
set -e
test "$cross_call_multishot_status" -eq 42

echo "compiler cross-call multi-shot clause-MIR end-to-end test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/cross-call-cancel.gr" \
  "$tmp/cross-call-cancel.ll"
llvm-as "$tmp/cross-call-cancel.ll" -o "$tmp/cross-call-cancel.bc"
grep -q 'define i32 @grandiose_runtime_handler_' \
  "$tmp/cross-call-cancel.ll"
grep -q 'add i32 %continuation_ignored_.*, 1000' \
  "$tmp/cross-call-cancel.ll"
grep -q 'define void @grandiose_bind_drop_' \
  "$tmp/cross-call-cancel.ll"
grep -q 'call void %t_cancel(ptr %t9)' \
  "$tmp/cross-call-cancel.ll"
grep -q 'call void @grandiose_release_shared_environment(ptr %d2)' \
  "$tmp/cross-call-cancel.ll"
set +e
lli "$tmp/cross-call-cancel.bc"
cross_call_cancel_status=$?
set -e
test "$cross_call_cancel_status" -eq 42

echo "compiler cross-call cancellation clause-MIR end-to-end test passed"

for ownership_example in effectful-parameter-drop effectful-local-drop; do
  "$root/compiler/grc" \
    "$root/compiler/examples/$ownership_example.gr" \
    "$tmp/$ownership_example.ll"
  llvm-as "$tmp/$ownership_example.ll" \
    -o "$tmp/$ownership_example.bc"
  grep -q 'define %grandiose.effect_step @grandiose_cleanup_step' \
    "$tmp/$ownership_example.ll"
  grep -q 'define void @grandiose_effect_owner_drop_' \
    "$tmp/$ownership_example.ll"
  grep -q 'call i1 @grandiose_claim_drop_state' \
    "$tmp/$ownership_example.ll"
  set +e
  lli "$tmp/$ownership_example.bc"
  ownership_status=$?
  set -e
  test "$ownership_status" -eq 42
done

echo "compiler effectful parameter/local resume/cancel drop-state tests passed"

"$root/compiler/grc" \
  "$root/compiler/examples/effect-payload-drop.gr" \
  "$tmp/effect-payload-drop.ll"
llvm-as "$tmp/effect-payload-drop.ll" -o "$tmp/effect-payload-drop.bc"
grep -q '%drop_active_pattern_resource_' "$tmp/effect-payload-drop.ll"
grep -q 'call void @grandiose_release_drop_state' \
  "$tmp/effect-payload-drop.ll"
test "$(grep -c 'call {} @grandiose_drop_hook_struct_Resource' \
  "$tmp/effect-payload-drop.ll")" -ge 2
set +e
lli "$tmp/effect-payload-drop.bc"
effect_payload_drop_status=$?
set -e
test "$effect_payload_drop_status" -eq 42

echo "compiler bound/discarded effect-payload ownership test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/nested-effect-payload-drop.gr" \
  "$tmp/nested-effect-payload-drop.ll"
llvm-as "$tmp/nested-effect-payload-drop.ll" \
  -o "$tmp/nested-effect-payload-drop.bc"
grep -q '%drop_active_pattern_first_' \
  "$tmp/nested-effect-payload-drop.ll"
grep -q 'extractvalue %enum.Packet .* 2' \
  "$tmp/nested-effect-payload-drop.ll"
grep -q 'call void @grandiose_release_drop_state(ptr %drop_active_pattern_first_' \
  "$tmp/nested-effect-payload-drop.ll"
set +e
lli "$tmp/nested-effect-payload-drop.bc"
nested_effect_payload_drop_status=$?
set -e
test "$nested_effect_payload_drop_status" -eq 42

echo "compiler nested effect-payload projection cleanup test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/effect-result-drop.gr" \
  "$tmp/effect-result-drop.ll"
llvm-as "$tmp/effect-result-drop.ll" -o "$tmp/effect-result-drop.bc"
grep -q '%drop_active_resource_' "$tmp/effect-result-drop.ll"
grep -q 'define void @grandiose_effect_owner_drop_.*_binding' \
  "$tmp/effect-result-drop.ll"
set +e
lli "$tmp/effect-result-drop.bc"
effect_result_drop_status=$?
set -e
test "$effect_result_drop_status" -eq 42

echo "compiler destructible suspension-result binding test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/cross-call-aggregate.gr" \
  "$tmp/cross-call-aggregate.ll"
llvm-as "$tmp/cross-call-aggregate.ll" -o "$tmp/cross-call-aggregate.bc"
grep -q 'insertvalue %struct.Pair undef, i32 %t' \
  "$tmp/cross-call-aggregate.ll"
grep -q 'insertvalue %enum.Wrapped %t' \
  "$tmp/cross-call-aggregate.ll"
grep -q 'call void @free(ptr %t1)' "$tmp/cross-call-aggregate.ll"
set +e
lli "$tmp/cross-call-aggregate.bc"
cross_call_aggregate_status=$?
set -e
test "$cross_call_aggregate_status" -eq 42

echo "compiler cross-call aggregate clause-MIR end-to-end test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/nested-cross-call-handlers.gr" \
  "$tmp/nested-cross-call-handlers.ll"
llvm-as "$tmp/nested-cross-call-handlers.ll" \
  -o "$tmp/nested-cross-call-handlers.bc"
test "$(grep -c 'define i32 @grandiose_runtime_handler_' \
  "$tmp/nested-cross-call-handlers.ll")" -eq 2
set +e
lli "$tmp/nested-cross-call-handlers.bc"
nested_cross_call_status=$?
set -e
test "$nested_cross_call_status" -eq 42

echo "compiler nested cross-call handler clause-MIR end-to-end test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/cross-call-patterns.gr" \
  "$tmp/cross-call-patterns.ll"
llvm-as "$tmp/cross-call-patterns.ll" -o "$tmp/cross-call-patterns.bc"
grep -q 'icmp eq i32 %t.* 0' "$tmp/cross-call-patterns.ll"
grep -q 'runtime_clause_next_' "$tmp/cross-call-patterns.ll"
set +e
lli "$tmp/cross-call-patterns.bc"
cross_call_patterns_status=$?
set -e
test "$cross_call_patterns_status" -eq 42

echo "compiler ordered cross-call resumptive pattern test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/cross-call-nominal-patterns.gr" \
  "$tmp/cross-call-nominal-patterns.ll"
llvm-as "$tmp/cross-call-nominal-patterns.ll" \
  -o "$tmp/cross-call-nominal-patterns.bc"
test "$(grep -c 'icmp eq i32 %t' \
  "$tmp/cross-call-nominal-patterns.ll")" -eq 2
set +e
lli "$tmp/cross-call-nominal-patterns.bc"
cross_call_nominal_patterns_status=$?
set -e
test "$cross_call_nominal_patterns_status" -eq 42

echo "compiler exhaustive nominal resumptive pattern test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/nested-resumptive-pattern.gr" \
  "$tmp/nested-resumptive-pattern.ll"
llvm-as "$tmp/nested-resumptive-pattern.ll" \
  -o "$tmp/nested-resumptive-pattern.bc"
grep -q 'freeze %enum.Inner' "$tmp/nested-resumptive-pattern.ll"
grep -q '%pattern_inner_' "$tmp/nested-resumptive-pattern.ll"
test "$(grep -c 'icmp eq i32' "$tmp/nested-resumptive-pattern.ll")" -ge 4
set +e
lli "$tmp/nested-resumptive-pattern.bc"
nested_resumptive_pattern_status=$?
set -e
test "$nested_resumptive_pattern_status" -eq 42

echo "compiler nested resumptive-pattern decision test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/cross-call-forwarding.gr" \
  "$tmp/cross-call-forwarding.ll"
llvm-as "$tmp/cross-call-forwarding.ll" -o "$tmp/cross-call-forwarding.bc"
grep -q 'define %grandiose.effect_step @grandiose_forward_resume_' \
  "$tmp/cross-call-forwarding.ll"
grep -q 'define %grandiose.effect_step @grandiose_forward_handler_' \
  "$tmp/cross-call-forwarding.ll"
grep -q 'insertvalue %grandiose.effect_step %s3, ptr @grandiose_forward_resume_' \
  "$tmp/cross-call-forwarding.ll"
grep -q 'call ptr @grandiose_new_resumption' \
  "$tmp/cross-call-forwarding.ll"
grep -q 'call %grandiose.effect_step @grandiose_finalize_resumption_step' \
  "$tmp/cross-call-forwarding.ll"
grep -q 'define void @grandiose_forward_drop_' \
  "$tmp/cross-call-forwarding.ll"
grep -q 'insertvalue %grandiose.effect_step %s7, ptr @grandiose_forward_drop_' \
  "$tmp/cross-call-forwarding.ll"
set +e
lli "$tmp/cross-call-forwarding.bc"
cross_call_forwarding_status=$?
set -e
test "$cross_call_forwarding_status" -eq 42

echo "compiler unmatched cross-call request forwarding test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/effect-after-resume.gr" \
  "$tmp/effect-after-resume.ll"
llvm-as "$tmp/effect-after-resume.ll" \
  -o "$tmp/effect-after-resume.bc"
grep -q 'call %grandiose.effect_step @grandiose_resume_resumption' \
  "$tmp/effect-after-resume.ll"
grep -q 'call %grandiose.effect_step @grandiose_outer_value()' \
  "$tmp/effect-after-resume.ll"
grep -q 'define %grandiose.effect_step @grandiose_effect_continuation_run_step_' \
  "$tmp/effect-after-resume.ll"
set +e
lli "$tmp/effect-after-resume.bc"
effect_after_resume_status=$?
set -e
test "$effect_after_resume_status" -eq 42

echo "compiler effectful post-resume clause continuation test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/repeated-forwarding-resumption.gr" \
  "$tmp/repeated-forwarding-resumption.ll"
llvm-as "$tmp/repeated-forwarding-resumption.ll" \
  -o "$tmp/repeated-forwarding-resumption.bc"
grep -q 'call ptr @grandiose_new_resumption' \
  "$tmp/repeated-forwarding-resumption.ll"
grep -q 'call %grandiose.effect_step @grandiose_resume_resumption' \
  "$tmp/repeated-forwarding-resumption.ll"
grep -q 'call %grandiose.effect_step @grandiose_finalize_resumption_step' \
  "$tmp/repeated-forwarding-resumption.ll"
set +e
lli "$tmp/repeated-forwarding-resumption.bc"
repeated_forwarding_resumption_status=$?
set -e
test "$repeated_forwarding_resumption_status" -eq 42

echo "compiler first-class repeated forwarding resumption test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/cross-call-forward-cancel.gr" \
  "$tmp/cross-call-forward-cancel.ll"
llvm-as "$tmp/cross-call-forward-cancel.ll" \
  -o "$tmp/cross-call-forward-cancel.bc"
grep -q 'call void @grandiose_cancel_resumption(ptr %t' \
  "$tmp/cross-call-forward-cancel.ll"
grep -q 'call %grandiose.effect_step @grandiose_finalize_resumption_step' \
  "$tmp/cross-call-forward-cancel.ll"
grep -q 'add i32 %continuation_ignored_.*, 1000' \
  "$tmp/cross-call-forward-cancel.ll"
set +e
lli "$tmp/cross-call-forward-cancel.bc"
cross_call_forward_cancel_status=$?
set -e
test "$cross_call_forward_cancel_status" -eq 42

echo "compiler outward-handler cancellation cleanup test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/cross-call-forward-drop.gr" \
  "$tmp/cross-call-forward-drop.ll"
llvm-as "$tmp/cross-call-forward-drop.ll" \
  -o "$tmp/cross-call-forward-drop.bc"
grep -q 'call %grandiose.effect_step @grandiose_finalize_resumption_step' \
  "$tmp/cross-call-forward-drop.ll"
set +e
lli "$tmp/cross-call-forward-drop.bc"
cross_call_forward_drop_status=$?
set -e
test "$cross_call_forward_drop_status" -eq 42

echo "compiler implicit outward-continuation drop test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/cross-call-forward-patterns.gr" \
  "$tmp/cross-call-forward-patterns.ll"
llvm-as "$tmp/cross-call-forward-patterns.ll" \
  -o "$tmp/cross-call-forward-patterns.bc"
test "$(grep -Ec '^forward_runtime_clause_[0-9]+:$' \
  "$tmp/cross-call-forward-patterns.ll")" -eq 2
grep -q 'label %forward_runtime_clause_' \
  "$tmp/cross-call-forward-patterns.ll"
set +e
lli "$tmp/cross-call-forward-patterns.bc"
cross_call_forward_patterns_status=$?
set -e
test "$cross_call_forward_patterns_status" -eq 42

echo "compiler exhaustive outward-handler pattern dispatch test passed"

"$root/compiler/grc" \
  "$root/compiler/examples/cross-call-partial-handler.gr" \
  "$tmp/cross-call-partial-handler.ll"
llvm-as "$tmp/cross-call-partial-handler.ll" \
  -o "$tmp/cross-call-partial-handler.bc"
grep -q 'forward_runtime_clause_next_.*:' \
  "$tmp/cross-call-partial-handler.ll"
grep -A1 'forward_runtime_clause_next_.*:' \
  "$tmp/cross-call-partial-handler.ll" | grep -q 'br label %unmatched'
grep -q 'define %grandiose.effect_step @grandiose_forward_resume_' \
  "$tmp/cross-call-partial-handler.ll"
set +e
lli "$tmp/cross-call-partial-handler.bc"
cross_call_partial_handler_status=$?
set -e
test "$cross_call_partial_handler_status" -eq 42

echo "compiler partial outward-handler forwarding test passed"

for resumption_example in resumption deep-resumption multishot-resumption \
  cancel-resumption; do
  "$root/compiler/grc" \
    "$root/compiler/examples/${resumption_example}.gr" \
    "$tmp/${resumption_example}.ll"
  llvm-as "$tmp/${resumption_example}.ll" -o "$tmp/${resumption_example}.bc"
  set +e
  lli "$tmp/${resumption_example}.bc"
  resumption_status=$?
  set -e
  test "$resumption_status" -eq 42
done
grep -q 'add i32 40, 2' "$tmp/resumption.ll"
if grep -q 'grandiose_forward_handler_' "$tmp/resumption.ll"; then
  echo "irrefutable lexical handler unexpectedly used runtime control MIR" >&2
  exit 1
fi
test "$(grep -c 'add i32' "$tmp/deep-resumption.ll")" -eq 3
test "$(grep -c 'add i32' "$tmp/multishot-resumption.ll")" -eq 2
if grep -q '1000' "$tmp/cancel-resumption.ll"; then
  echo "cancelled continuation was emitted" >&2
  exit 1
fi

echo "compiler deep/multi-shot/cancel resumptive LLVM tests passed"

# `compiler/grc` runs this legacy compiler source through the Rust bootstrap
# interpreter. This padding is therefore an interpreter lexer-traversal stress
# test; it does not prove tail-call formation in the generated LLVM output.
{
  printf 'main() -> i64 { 42'
  head -c 10000 /dev/zero | tr '\0' ' '
  printf '}\n'
} >"$tmp/tail-call-stress.gr"
"$root/compiler/grc" "$tmp/tail-call-stress.gr" "$tmp/stress.ll" >/dev/null
llvm-as "$tmp/stress.ll" -o "$tmp/stress.bc"

echo "bootstrap-interpreter lexer stress test passed"
