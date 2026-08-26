#!/usr/bin/env bash
# Fails closed if the bootstrap harness acquires ambient semantic authority.
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
readonly support="$root/self-host-stage0/runtime/compiler_support.glorious"
readonly canonical_check="$root/tooling/self-host-stage0-check.sh"
readonly branch_bool_check="$root/tooling/self-host-stage0-branch-bool-check.sh"
readonly wrapping_add_check="$root/tooling/self-host-stage0-wrapping-add-check.sh"
readonly bootstrap_indirection_check="$root/tooling/self-host-stage0-bootstrap-indirection-check.sh"
readonly blake3_check="$root/tooling/self-host-stage0-blake3-check.sh"
readonly cancellation_check="$root/tooling/self-host-stage0-cancellation-check.sh"
readonly cancellation_result_check="$root/tooling/self-host-stage0-cancellation-result-check.sh"
readonly budget_check="$root/tooling/self-host-stage0-budget-check.sh"
readonly budget_charge_check="$root/tooling/self-host-stage0-budget-charge-check.sh"
readonly transaction_check="$root/tooling/self-host-stage0-transaction-check.sh"
readonly publication_check="$root/tooling/self-host-stage0-publication-check.sh"
readonly quantity_check="$root/tooling/self-host-stage0-quantity-check.sh"
readonly quantity_contains_check="$root/tooling/self-host-stage0-quantity-contains-check.sh"
readonly quantity_hull_check="$root/tooling/self-host-stage0-quantity-hull-check.sh"
readonly quantity_intersection_check="$root/tooling/self-host-stage0-quantity-intersection-check.sh"
readonly quantity_sequence_check="$root/tooling/self-host-stage0-quantity-sequence-check.sh"
readonly quantity_construction_check="$root/tooling/self-host-stage0-quantity-construction-check.sh"
readonly diagnostic_check="$root/tooling/self-host-stage0-diagnostic-check.sh"
readonly request_check="$root/tooling/self-host-stage0-request-check.sh"
readonly bootstrap_stage_check="$root/tooling/self-host-stage0-bootstrap-stage-check.sh"
readonly interface_check="$root/tooling/self-host-stage0-interface-check.sh"
readonly fixity_check="$root/tooling/self-host-stage0-fixity-check.sh"
readonly module_graph_check="$root/tooling/self-host-stage0-module-graph-check.sh"
readonly resolution_check="$root/tooling/self-host-stage0-resolution-check.sh"
readonly types_check="$root/tooling/self-host-stage0-types-check.sh"
readonly signature_check="$root/tooling/self-host-stage0-signature-check.sh"
readonly coherence_check="$root/tooling/self-host-stage0-coherence-check.sh"
readonly trait_solver_check="$root/tooling/self-host-stage0-trait-solver-check.sh"
readonly output_check="$root/tooling/self-host-stage0-output-check.sh"
readonly output_write_check="$root/tooling/self-host-stage0-output-write-check.sh"
readonly bootstrap_artifact_check="$root/tooling/self-host-stage0-bootstrap-artifact-check.sh"
readonly g1_default_artifact_check="$root/tooling/self-host-stage0-g1-default-artifact-check.sh"
readonly g1_source_unit_artifact_check="$root/tooling/self-host-stage0-g1-source-unit-artifact-check.sh"
readonly g1_file_unit_artifact_check="$root/tooling/self-host-stage0-g1-file-unit-artifact-check.sh"
readonly g1_cli_emit_vm_check="$root/tooling/self-host-stage0-g1-cli-emit-vm-check.sh"
readonly process_args_check="$root/tooling/self-host-stage0-process-args-check.sh"
readonly main_process_args_check="$root/tooling/self-host-stage0-main-process-args-check.sh"
readonly file_read_check="$root/tooling/self-host-stage0-file-read-check.sh"
readonly service_file_read_check="$root/tooling/self-host-stage0-service-file-read-check.sh"
readonly diagnostic_write_check="$root/tooling/self-host-stage0-diagnostic-write-check.sh"
readonly source_check="$root/tooling/self-host-stage0-source-check.sh"
readonly scanner_check="$root/tooling/self-host-stage0-scanner-check.sh"

[[ -f "$support" && -x "$canonical_check" && -x "$branch_bool_check" && -x "$wrapping_add_check" && -x "$bootstrap_indirection_check" && -x "$blake3_check" && -x "$cancellation_check" && -x "$cancellation_result_check" && -x "$budget_check" && -x "$budget_charge_check" && -x "$transaction_check" && -x "$publication_check" && -x "$quantity_check" && -x "$quantity_contains_check" && -x "$quantity_hull_check" && -x "$quantity_intersection_check" && -x "$quantity_sequence_check" && -x "$quantity_construction_check" && -x "$diagnostic_check" && -x "$request_check" && -x "$bootstrap_stage_check" && -x "$interface_check" && -x "$fixity_check" && -x "$module_graph_check" && -x "$resolution_check" && -x "$types_check" && -x "$signature_check" && -x "$coherence_check" && -x "$trait_solver_check" && -x "$output_check" && -x "$output_write_check" && -x "$bootstrap_artifact_check" && -x "$g1_default_artifact_check" && -x "$g1_file_unit_artifact_check" && -x "$g1_cli_emit_vm_check" && -x "$process_args_check" && -x "$main_process_args_check" && -x "$file_read_check" && -x "$service_file_read_check" && -x "$diagnostic_write_check" && -x "$source_check" && -x "$scanner_check" ]] || {
    echo "self-host fallback audit: required harness files are missing" >&2
    exit 1
}
# A compiler-support declaration is never ordinary source authority. Every
# private support leaf must be selected by an exact `--runtime-leaf` binding
# in each harness that admits that support package.
mapfile -t support_leaves < <(
    sed -n 's/^pub fn \(__g1_[a-z0-9_]*\)(.*/\1/p' "$support" | LC_ALL=C sort -u
)
[[ "${#support_leaves[@]}" -gt 0 ]] || {
    echo "self-host fallback audit: no private support leaves found" >&2
    exit 1
}

for harness in "$canonical_check" "$branch_bool_check" "$blake3_check"; do
    grep -Fq -- '--runtime-standard-library' "$harness" || {
        echo "self-host fallback audit: $(basename "$harness") lacks explicit runtime package" >&2
        exit 1
    }
    for leaf in "${support_leaves[@]}"; do
        grep -Fq -- " $leaf" "$harness" || {
            echo "self-host fallback audit: $(basename "$harness") leaves $leaf unbound" >&2
            exit 1
        }
    done
done

for harness in "$canonical_check" "$branch_bool_check" "$blake3_check"; do
    grep -Fq -- '--runtime-leaf branch-bool crate branch_bool' "$harness" || {
        echo "self-host fallback audit: $(basename "$harness") leaves branch_bool unbound" >&2
        exit 1
    }
done

grep -Fq $'compiler_support@0.1.0\tsrc/lib.glorious' "$root/self-host-stage0/sources.tsv" || {
    echo "self-host fallback audit: canonical source world lacks compiler support identity" >&2
    exit 1
}

mapfile -t all_check_harnesses < <(
    find "$root/tooling" -maxdepth 1 -type f -name 'self-host-stage0-*-check.sh' ! -name 'self-host-stage0-output-write-check.sh' ! -name 'self-host-stage0-bootstrap-artifact-check.sh' ! -name 'self-host-stage0-g1-default-artifact-check.sh' ! -name 'self-host-stage0-g1-source-unit-artifact-check.sh' ! -name 'self-host-stage0-g1-file-unit-artifact-check.sh' ! -name 'self-host-stage0-g1-cli-emit-vm-check.sh' ! -name 'self-host-stage0-process-args-check.sh' ! -name 'self-host-stage0-main-process-args-check.sh' ! -name 'self-host-stage0-file-read-check.sh' ! -name 'self-host-stage0-service-file-read-check.sh' ! -name 'self-host-stage0-diagnostic-write-check.sh' -print | LC_ALL=C sort
)
[[ "${#all_check_harnesses[@]}" -gt 0 ]] || {
    echo "self-host fallback audit: no self-host check harnesses found" >&2
    exit 1
}

# Harnesses must not bypass the source CLI by acquiring host authority or
# invoking Cargo.  The source CLI is allowed to *parse* `--runtime-host` and
# `--capability`: those spellings are policy data, not an authority grant.
if rg -n -- '--runtime-host|--capability|cargo run' \
    "${all_check_harnesses[@]}" >/dev/null; then
    echo "self-host fallback audit: ambient host or cargo-run route is forbidden" >&2
    exit 1
fi

grep -Fq -- '--runtime-host process_args __g1_process_args_get crate process_args_get --capability process_args' "$bootstrap_artifact_check" || { echo "self-host fallback audit: bootstrap execution lacks explicit process-args binding" >&2; exit 1; }
grep -Fq -- '--runtime-host file_read __g1_fs_read crate read_file --capability file_read' "$bootstrap_artifact_check" || { echo "self-host fallback audit: bootstrap execution lacks explicit file-read binding" >&2; exit 1; }
grep -Fq -- '--runtime-host file_write_atomic __g1_fs_write_atomic crate write_file_atomically --capability file_write_atomic' "$bootstrap_artifact_check" || { echo "self-host fallback audit: bootstrap execution lacks explicit atomic-write binding" >&2; exit 1; }
grep -Fq -- '--runtime-host diagnostic_write __g1_diagnostic_write crate write_diagnostic --capability diagnostic_write' "$bootstrap_artifact_check" || { echo "self-host fallback audit: bootstrap execution lacks explicit diagnostic binding" >&2; exit 1; }
grep -Fq -- 'run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 emit-vm' "$bootstrap_artifact_check" || { echo "self-host fallback audit: bootstrap execution lacks separated source-owned guest argv" >&2; exit 1; }
grep -Fq -- 'run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 check' "$bootstrap_artifact_check" || { echo "self-host fallback audit: bootstrap execution lacks the source-owned check driver path" >&2; exit 1; }
grep -Fq -- 'run-vm "$artifact" -- --root-package self-host-stage0@0.1.0 run' "$bootstrap_artifact_check" || { echo "self-host fallback audit: bootstrap execution lacks the source-owned run driver path" >&2; exit 1; }
grep -Fq -- 'stage_select_run_output=' "$bootstrap_artifact_check" || { echo "self-host fallback audit: bootstrap execution lacks conditional source-run coverage" >&2; exit 1; }
grep -Fq -- 'stage_unsupported_bool_output=' "$bootstrap_artifact_check" || { echo "self-host fallback audit: bootstrap execution lacks strict unsupported-run coverage" >&2; exit 1; }
grep -Fq -- 'stage_bool_run_output=' "$bootstrap_artifact_check" || { echo "self-host fallback audit: bootstrap execution lacks strict Bool source-run coverage" >&2; exit 1; }
grep -Fq -- 'stage_unsupported_command_output=' "$bootstrap_artifact_check" || { echo "self-host fallback audit: bootstrap execution lacks unsupported-command coverage" >&2; exit 1; }

# M06 may perform a real publication, but only through one checked-in
# capability grant. Keep this exception narrow: it must bind precisely the
# standard host ABI and the source output facade must own the decision before
# the boundary is reached.
grep -Fq -- '--runtime-host file_write_atomic __g1_fs_write_atomic crate write_file_atomically' "$output_write_check" || {
    echo "self-host fallback audit: output write check lacks exact atomic file-write binding" >&2
    exit 1
}
grep -Fq -- '--capability file_write_atomic' "$output_write_check" || {
    echo "self-host fallback audit: output write check lacks explicit atomic file-write capability" >&2
    exit 1
}
grep -Fq 'pub fn write_file_atomically(path: Text, bytes: Bytes) -> () { () }' "$support" || {
    echo "self-host fallback audit: output host declaration is not an opaque standard-library boundary" >&2
    exit 1
}
rg -q 'pub fn write_to\(publication: Publication, path: Text\)' "$root/self-host-stage0/src/output/output.glorious" || {
    echo "self-host fallback audit: output module lacks source-owned publication policy" >&2
    exit 1
}

grep -Fq -- '--runtime-host file_write_atomic __g1_fs_write_atomic crate write_file_atomically' "$g1_default_artifact_check" || {
    echo "self-host fallback audit: G1 artifact check lacks exact atomic file-write binding" >&2
    exit 1
}
grep -Fq -- '--runtime-host file_write_atomic __g1_fs_write_atomic crate write_file_atomically' "$g1_source_unit_artifact_check" || {
    echo "semantic fallback audit: source-unit G1 artifact gate lacks explicit atomic-write binding" >&2
    exit 1
}
grep -Fq -- '--runtime-host file_read __g1_fs_read crate read_file' "$g1_file_unit_artifact_check" || {
    echo "semantic fallback audit: file-unit G1 artifact gate lacks explicit file-read binding" >&2
    exit 1
}
grep -Fq -- '--runtime-host file_write_atomic __g1_fs_write_atomic crate write_file_atomically' "$g1_file_unit_artifact_check" || {
    echo "semantic fallback audit: file-unit G1 artifact gate lacks explicit atomic-write binding" >&2
    exit 1
}
grep -Fq -- '--capability file_read' "$g1_file_unit_artifact_check" || {
    echo "semantic fallback audit: file-unit G1 artifact gate lacks explicit file-read capability" >&2
    exit 1
}
grep -Fq -- '--capability file_write_atomic' "$g1_file_unit_artifact_check" || {
    echo "semantic fallback audit: file-unit G1 artifact gate lacks explicit atomic-write capability" >&2
    exit 1
}
grep -Fq -- '--runtime-host file_read __g1_fs_read crate read_file' "$g1_cli_emit_vm_check" || {
    echo "semantic fallback audit: CLI emit-vm gate lacks explicit file-read binding" >&2
    exit 1
}
grep -Fq -- '--runtime-host file_write_atomic __g1_fs_write_atomic crate write_file_atomically' "$g1_cli_emit_vm_check" || {
    echo "semantic fallback audit: CLI emit-vm gate lacks explicit atomic-write binding" >&2
    exit 1
}
rg -q 'pub fn emit_vm_entry_from_argv\(argv: Array<Text>\)' "$root/self-host-stage0/src/service/service.glorious" || {
    echo "semantic fallback audit: service lacks the source-owned argv-to-emit-vm entrypoint" >&2
    exit 1
}
rg -q 'parse_argv_emit_vm_request\(argv\)' "$root/self-host-stage0/src/service/service.glorious" || {
    echo "semantic fallback audit: service emit-vm entrypoint bypasses source command selection" >&2
    exit 1
}
grep -Fq -- '--capability file_write_atomic' "$g1_default_artifact_check" || {
    echo "self-host fallback audit: G1 artifact check lacks explicit atomic file-write capability" >&2
    exit 1
}

grep -Fq -- '--runtime-host process_args __g1_process_args_get crate process_args_get' "$process_args_check" || {
    echo "self-host fallback audit: process-args check lacks exact argv binding" >&2
    exit 1
}
grep -Fq -- '--capability process_args' "$process_args_check" || {
    echo "self-host fallback audit: process-args check lacks explicit argv capability" >&2
    exit 1
}
grep -Fq -- '--runtime-host process_args __g1_process_args_get crate process_args_get' "$main_process_args_check" || {
    echo "self-host fallback audit: main process-args check lacks exact argv binding" >&2
    exit 1
}
grep -Fq -- '--capability process_args' "$main_process_args_check" || {
    echo "self-host fallback audit: main process-args check lacks explicit argv capability" >&2
    exit 1
}
rg -q 'pub fn parse_process_argv_command_at\(index: usize\)' "$root/self-host-stage0/src/main_cli/main_cli.glorious" || {
    echo "self-host fallback audit: main CLI lacks the source-owned process argv boundary" >&2
    exit 1
}
rg -q 'pub fn parse_process_argv_emit_vm\(\) -> EmitVmArguments' "$root/self-host-stage0/src/main_cli/main_cli.glorious" || {
    echo "self-host fallback audit: main CLI lacks the source-owned process emit-vm boundary" >&2
    exit 1
}
grep -Fq 'pub fn process_args_get() -> Array<Text> { [] }' "$support" || {
    echo "self-host fallback audit: argv host declaration is not an opaque standard-library boundary" >&2
    exit 1
}

grep -Fq -- '--runtime-host file_read __g1_fs_read crate read_file' "$file_read_check" || {
    echo "self-host fallback audit: file-read check lacks exact read binding" >&2
    exit 1
}
grep -Fq -- '--capability file_read' "$file_read_check" || {
    echo "self-host fallback audit: file-read check lacks explicit read capability" >&2
    exit 1
}
grep -Fq -- '--runtime-host file_read __g1_fs_read crate read_file' "$service_file_read_check" || {
    echo "self-host fallback audit: service file-read check lacks exact read binding" >&2
    exit 1
}
grep -Fq -- '--capability file_read' "$service_file_read_check" || {
    echo "self-host fallback audit: service file-read check lacks explicit read capability" >&2
    exit 1
}
grep -Fq 'pub fn read_file(path: Text) -> Bytes { __g1_text_as_bytes(path) }' "$support" || {
    echo "self-host fallback audit: file-read declaration lacks its typed no-authority fallback" >&2
    exit 1
}

grep -Fq -- '--runtime-host diagnostic __g1_diagnostic_write crate write_diagnostic' "$diagnostic_write_check" || {
    echo "self-host fallback audit: diagnostic check lacks exact diagnostic binding" >&2
    exit 1
}
grep -Fq -- '--capability diagnostic' "$diagnostic_write_check" || {
    echo "self-host fallback audit: diagnostic check lacks explicit diagnostic capability" >&2
    exit 1
}
grep -Fq 'pub fn write_diagnostic(text: Text) -> () { () }' "$support" || {
    echo "self-host fallback audit: diagnostic declaration is not an opaque standard-library boundary" >&2
    exit 1
}

if rg -n -- 'cargo run' "$root/self-host-stage0" >/dev/null; then
    echo "self-host fallback audit: source tree contains a cargo-run route" >&2
    exit 1
fi

# G1 artifacts must remain assembled from the source backend's schema
# encoders. Small fixed wire fields (magic, tags, zero padding) are normal;
# an opaque whole-library candidate would make later code generation drift
# independently from the encoder and must not return.
if rg -n 'g1_default_library_artifact|default G1 library image' "$root/self-host-stage0/src/vm_backend" >/dev/null; then
    echo "self-host fallback audit: vm backend contains a retired opaque default-library artifact" >&2
    exit 1
fi

rg -q 'pub fn emit_g1_named_unit_entry\(name: Bytes\)' "$root/self-host-stage0/src/vm_backend/vm_backend.glorious" || {
    echo "self-host fallback audit: vm backend lacks source-owned named unit-entry emission" >&2
    exit 1
}
rg -q 'emit_g1_named_unit_entry\(__g1_bytes_slice\(bytes, token_start\(name\), token_end\(name\)\)\)' "$root/self-host-stage0/src/service/service.glorious" || {
    echo "self-host fallback audit: service does not carry scanner-derived entry names to G1 emission" >&2
    exit 1
}
