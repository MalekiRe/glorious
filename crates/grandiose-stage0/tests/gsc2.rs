//! Source-owned replacement tests. This harness supplies immutable source
//! bytes to C0, then independently decodes/verifies its serialized program.
//! No old self-host implementation is part of the source closure.
use std::{collections::BTreeMap, fs, path::Path, sync::OnceLock};

use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath, PackageKey,
    SourceInput, StageZeroCompiler, decode_and_verify_program,
};

fn source_case(case: &str) -> i64 {
    source_case_with(case, &[])
}

fn source_case_with(case: &str, replacements: &[(&str, String)]) -> i64 {
    let program = source_program(case, replacements);
    let result = program
        .run_i64()
        .expect("verified source program must execute");
    record_execution(case, &program, result, None);
    result
}

fn source_batch<'a>(
    slot: &'a OnceLock<Result<Vec<i64>, String>>,
    case: &str,
    replacements: &[(&str, String)],
    evidence_name: &str,
    expected: &[i64],
) -> &'a [i64] {
    let results = slot
        .get_or_init(|| {
            std::panic::catch_unwind(|| {
                let program = source_program(case, replacements);
                let (results, profile) = program
                    .run_tuple_i64_for_authoring(Default::default())
                    .map_err(|error| format!("{case} batch execution failed: {error:?}"))?;
                // One execution uses one unchanged budget and produces one
                // profile, not a repeated aggregate for each named comparator.
                record_execution_values(
                    evidence_name,
                    &program,
                    "",
                    &format!("{results:?}"),
                    Some(&profile),
                );
                Ok(results)
            })
            .unwrap_or_else(|_| {
                Err(format!(
                    "{case} compilation panicked; see diagnostics above"
                ))
            })
        })
        .as_ref()
        .expect("source batch must compile and execute");
    // Selecting only one libtest entry still checks every executed result.
    assert_eq!(results.as_slice(), expected, "{evidence_name}");
    results
}

fn record_execution(
    case: &str,
    program: &grandiose_stage0::VerifiedVmProgram,
    result: i64,
    profile: Option<&grandiose_stage0::vm_backend::VmAuthoringProfile>,
) {
    record_execution_values(case, program, &result.to_string(), "", profile);
}

fn record_execution_values(
    case: &str,
    program: &grandiose_stage0::VerifiedVmProgram,
    result: &str,
    tuple: &str,
    profile: Option<&grandiose_stage0::vm_backend::VmAuthoringProfile>,
) {
    let Some(directory) = std::env::var_os("GSC2_EVIDENCE_DIR") else {
        return;
    };
    let bytes = program.canonical_bytes();
    let (ticks, allocations, depth, tails, inspected) = profile
        .map(|p| {
            (
                p.work_ticks.to_string(),
                p.charged_allocation_elements.to_string(),
                p.peak_call_depth.to_string(),
                p.recycled_tail_calls.to_string(),
                p.inspected_tail_argument_elements.to_string(),
            )
        })
        .unwrap_or_default();
    let record = format!(
        "fixture\tartifact_digest\tartifact_bytes\tresult_i64\tresult_i64_tuple\tprofiled\twork_ticks\tcharged_allocation_elements\tpeak_call_depth\trecycled_tail_calls\tinspected_tail_argument_elements\n{case}\t{}\t{}\t{result}\t{tuple}\t{}\t{ticks}\t{allocations}\t{depth}\t{tails}\t{inspected}\n",
        Digest::of_bytes(&bytes),
        bytes.len(),
        profile.is_some()
    );
    fs::write(
        Path::new(&directory).join(case.replace('/', "__") + ".tsv"),
        record,
    )
    .unwrap();
}

fn source_program(
    case: &str,
    replacements: &[(&str, String)],
) -> grandiose_stage0::VerifiedVmProgram {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let package = PackageKey("gsc2@0.1.0".into());
    let mut application = fs::read_to_string(root.join("compiler/tests").join(case)).unwrap();
    for (needle, replacement) in replacements {
        assert_eq!(
            application.matches(needle).count(),
            1,
            "oracle placeholder must be unique"
        );
        application = application.replace(needle, replacement);
    }
    // Every fixture checks the complete production module closure, even when
    // its entry point only exercises the kernel. Keep this explicit list in
    // sync with new top-level modules; C0 rejects any unclaimed supplied file.
    for module in ["kernel", "source", "registry", "request", "types", "runtime_manifest"] {
        let declaration = format!("pub mod {module};");
        if !application.lines().any(|line| line.trim() == declaration) {
            application.insert_str(0, &(declaration + "\n"));
        }
    }
    let mut sources = vec![
        SourceInput::new(
            package.clone(),
            LogicalPath::parse("src/main.glorious").unwrap(),
            application.as_bytes(),
        ),
        SourceInput::new(
            PackageKey("std@0.1.0".into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            include_bytes!("../../../stdlib/src/lib.glorious").as_slice(),
        ),
    ];
    fn add_sources(
        root: &Path,
        directory: &Path,
        package: &PackageKey,
        sources: &mut Vec<SourceInput>,
    ) {
        let mut entries: Vec<_> = fs::read_dir(directory)
            .unwrap()
            .map(|e| e.unwrap().path())
            .collect();
        entries.sort();
        for path in entries {
            if path.is_dir() {
                add_sources(root, &path, package, sources);
            } else if path.extension().is_some_and(|e| e == "glorious") {
                let logical = path.strip_prefix(root).unwrap().to_str().unwrap();
                // The fixture supplies the application entry point. Production
                // modules otherwise belong to the same complete source closure.
                if logical == "src/main.glorious" {
                    continue;
                }
                sources.push(SourceInput::new(
                    package.clone(),
                    LogicalPath::parse(logical).unwrap(),
                    fs::read(path).unwrap(),
                ));
            }
        }
    }
    add_sources(
        &root.join("compiler"),
        &root.join("compiler/src"),
        &package,
        &mut sources,
    );
    let request = CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"gsc2-authoring-capabilities-v1")),
        mode: CompilationMode::Build,
        root_package: package,
        sources,
        target: "stage0-vm".into(),
        semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::new(),
        capability_manifest: vec![],
        runtime_manifest: None,
    };
    let source_names: Vec<_> = request
        .sources
        .iter()
        .map(|s| (s.key, s.logical_path.as_str().to_owned()))
        .collect();
    let oracle_world = request.clone().normalize().unwrap();
    let outcome = StageZeroCompiler::new()
        .compile(request)
        .unwrap_or_else(|e| {
            for diagnostic in e.diagnostics() {
                let location = diagnostic
                    .primary
                    .and_then(|span| {
                        oracle_world
                            .sources
                            .iter()
                            .find(|s| s.key == span.file)
                            .map(|source| {
                                let snippet = source
                                    .bytes
                                    .get(span.start as usize..span.end as usize)
                                    .unwrap_or(&[]);
                                format!(
                                    "{}:{}: {}",
                                    source.logical_path.as_str(),
                                    span.start,
                                    String::from_utf8_lossy(snippet)
                                )
                            })
                    })
                    .unwrap_or_default();
                eprintln!("{}: {}\n  {location}", diagnostic.code, diagnostic.message);
            }
            panic!("{case}: source compilation failed; sources: {source_names:?}")
        });
    assert!(
        outcome.diagnostics.is_empty(),
        "{case}: {:#?}",
        outcome.diagnostics
    );
    let bytes = outcome.artifact.unwrap().canonical_bytes();
    assert_eq!(&bytes[..8], b"G0VP\r\n\x1a\n");
    decode_and_verify_program(&bytes).expect("serialized source program must independently verify")
}

#[test]
fn gsc2_storage_generations_survive_remove_and_reinsert() {
    assert_eq!(source_case("runtime/storage.glorious"), 42);
}

#[test]
fn gsc2_bounded_bytes_roundtrip_and_fail_without_partial_mutation() {
    assert_eq!(source_case("runtime/bytes.glorious"), 42);
}

#[test]
fn gsc2_byte_buffer_writes_a_complete_word() {
    assert_eq!(source_case("runtime/byte_write.glorious"), 42);
}

#[test]
fn gsc2_byte_buffer_borrows_its_backing_storage() {
    assert_eq!(source_case("runtime/byte_view.glorious"), 42);
}

#[test]
fn gsc2_authoring_snapshots_nested_shared_loans_in_the_owning_frame() {
    assert_eq!(source_case("runtime/borrowed_aggregate.glorious"), 42);
}

#[test]
fn gsc2_controls_preserve_limits_overflow_and_cancellation_cleanup() {
    assert_eq!(source_case("runtime/operation.glorious"), 42);
}

#[test]
fn gsc2_file_identity_matches_all_256_frozen_oracle_bits() {
    let expected =
        grandiose_stage0::FileKey::new(&PackageKey("app@0.1.0".into()), "src/main.glorious").0;
    let literal: String = expected
        .as_bytes()
        .iter()
        .map(|b| format!("\\x{b:02x}"))
        .collect();
    assert_eq!(
        source_case_with("runtime/identity.glorious", &[("@ORACLE@", literal)]),
        42
    );
}

#[test]
fn gsc2_revision_deduplication_pins_retirement_and_collection() {
    assert_eq!(source_case("engine/revision.glorious"), 42);
}

#[test]
fn gsc2_nested_transactions_retain_outer_undo_and_cancel_publication() {
    assert_eq!(source_case("engine/transaction.glorious"), 42);
}

#[test]
fn gsc2_dependency_keys_preserve_canonical_byte_and_variant_order() {
    let mut callable = [0; 32];
    callable[1] = 1;
    let expected = grandiose_stage0::InstanceKey::new(
        grandiose_stage0::DefKey(Digest::from_bytes(callable)),
        &[grandiose_stage0::GenericKind::Const(
            grandiose_stage0::ConstKind::U32,
        )],
        vec![grandiose_stage0::GenericArgument::ConstU32(1)],
    )
    .unwrap()
    .fingerprint();
    let literal: String = expected
        .as_bytes()
        .iter()
        .map(|b| format!("\\x{b:02x}"))
        .collect();
    assert_eq!(
        source_case_with(
            "runtime/dependency_keys.glorious",
            &[("@INSTANCE_ORACLE@", literal)]
        ),
        42
    );
}

#[test]
fn gsc2_dependency_ledger_canonicalizes_edges_and_separates_value_change_from_execution() {
    assert_eq!(source_case("engine/dependency.glorious"), 42);
}

#[test]
fn gsc2_dependency_ledger_rejects_cycles_and_prioritizes_missing_evidence() {
    assert_eq!(source_case("engine/dependency_structure.glorious"), 42);
}

#[test]
fn gsc2_dependency_ledger_aborts_cancelled_over_budget_and_stale_parent_transactions() {
    assert_eq!(source_case("engine/dependency_transactions.glorious"), 42);
}

#[test]
fn gsc2_package_staging_validates_all_packages_and_cleans_up_owned_scratch() {
    assert_eq!(source_case("engine/packages.glorious"), 42);
}

#[test]
fn gsc2_package_sessions_authenticate_worlds_handles_and_shared_request_controls() {
    assert_eq!(source_case("engine/package_sessions.glorious"), 42);
}

fn diagnostic_reference(mode: u32) -> Vec<grandiose_stage0::CompileDiagnostic> {
    use grandiose_stage0::{CompileDiagnostic, DiagnosticClass, FileKey, Severity, SourceSpan};
    let file = FileKey(Digest::of_bytes(b"diagnostic-file"));
    let first = Digest::of_bytes(b"first-world");
    let later = Digest::of_bytes(b"later-world");
    let span = |start| SourceSpan {
        file,
        start,
        end: start + 1,
    };
    let value = |code, message: &str, severity, primary, input_fingerprint| CompileDiagnostic {
        code,
        message: message.into(),
        class: DiagnosticClass::Source,
        severity,
        primary,
        input_fingerprint,
        related: vec![],
        facts: vec![],
        explanation: vec![],
    };
    let base = |fingerprint, right| {
        let mut item = value(
            "G1000",
            "shared failure",
            Severity::Error,
            Some(span(4)),
            Some(fingerprint),
        )
        .with_related_location("z site", span(12))
        .with_related_location("a site", span(16))
        .with_related_location("z site", span(12))
        .with_fact("observed", "open")
        .with_explanation("type", "closed ABI");
        if right {
            item = item
                .with_fact("expected", "closed")
                .with_explanation("effect", "entry boundary");
        }
        item
    };
    let mut note = value("A0000", "request note", Severity::Note, None, None);
    note.class = DiagnosticClass::Request;
    let bad = value(
        "G9999",
        "bad related span",
        Severity::Error,
        Some(span(20)),
        Some(later),
    )
    .with_related_location(
        "missing",
        SourceSpan {
            file: FileKey(later),
            start: 0,
            end: 1,
        },
    );
    let mut values = vec![
        value(
            "G0000",
            "later error",
            Severity::Error,
            Some(span(10)),
            None,
        ),
        base(first, false),
        value("A1000", "warning", Severity::Warning, Some(span(4)), None),
        base(later, true),
        note,
        bad,
    ];
    if mode == 0 {
        return CompileDiagnostic::canonicalize(values);
    }
    for (start, message) in [(0, "early zero"), (1, "early one"), (2, "early two")] {
        values.push(value(
            "G2000",
            message,
            Severity::Error,
            Some(span(start)),
            None,
        ));
    }
    let mut values =
        CompileDiagnostic::validate_primary_spans(values, &BTreeMap::from([(file, 32)]));
    for value in &mut values {
        value.input_fingerprint = Some(first);
    }
    let mut values = if mode == 3 {
        CompileDiagnostic::canonicalize(values)
    } else {
        CompileDiagnostic::limit_errors(values, if mode == 2 { 0 } else { 3 })
    };
    for value in &mut values {
        value.input_fingerprint = Some(first);
    }
    values
}

fn diagnostic_fingerprint(values: &[grandiose_stage0::CompileDiagnostic]) -> Digest {
    fn word(bytes: &mut Vec<u8>, value: usize) {
        bytes.extend_from_slice(&(value as u64).to_le_bytes());
    }
    fn string(bytes: &mut Vec<u8>, value: &str) {
        word(bytes, value.len());
        bytes.extend_from_slice(value.as_bytes());
    }
    fn span(bytes: &mut Vec<u8>, value: grandiose_stage0::SourceSpan) {
        bytes.extend_from_slice(&value.file.0.as_bytes());
        word(bytes, value.start as usize);
        word(bytes, value.end as usize);
    }
    let mut bytes = vec![];
    word(&mut bytes, values.len());
    for value in values {
        string(&mut bytes, value.code);
        word(&mut bytes, value.class as usize);
        word(&mut bytes, value.severity as usize);
        string(&mut bytes, &value.message);
        word(&mut bytes, usize::from(value.primary.is_some()));
        if let Some(primary) = value.primary {
            span(&mut bytes, primary);
        }
        word(&mut bytes, usize::from(value.input_fingerprint.is_some()));
        if let Some(fingerprint) = value.input_fingerprint {
            bytes.extend_from_slice(&fingerprint.as_bytes());
        }
        word(&mut bytes, value.related.len());
        for related in &value.related {
            string(&mut bytes, &related.label);
            span(&mut bytes, related.span);
        }
        word(&mut bytes, value.facts.len());
        for fact in &value.facts {
            string(&mut bytes, &fact.name);
            string(&mut bytes, &fact.value);
        }
        word(&mut bytes, value.explanation.len());
        for frame in &value.explanation {
            string(&mut bytes, &frame.kind);
            string(&mut bytes, &frame.message);
        }
    }
    Digest::of_bytes(&bytes)
}

// Each compiled batch occupies one libtest worker. Its original named
// comparator functions all still execute, without blocking other workers on
// the same OnceLock while unrelated source fixtures are waiting to compile.

#[test]
fn gsc2_diagnostic_batch_matches_all_reference_publication_policies() {
    gsc2_diagnostic_canonicalization_matches_every_reference_field();
    gsc2_diagnostic_publication_validation_and_error_limit_match_the_reference();
    gsc2_diagnostic_zero_error_limit_preserves_the_terminal_resource_fact();
    gsc2_diagnostic_invalid_related_locations_publish_the_exact_invariant_fact();
}

#[test]
fn gsc2_request_publication_batch_preserves_all_lifecycle_and_failure_comparators() {
    gsc2_request_publication_combines_owned_results_diagnostics_packages_and_revision_traces();
    gsc2_request_publication_rejects_unstaged_packages_invalid_spans_work_exhaustion_and_active_queries();
    gsc2_request_publication_rejects_stale_parent_and_session_authority_without_touching_new_owners(
    );
}

#[test]
fn gsc2_registry_batch_preserves_all_eight_source_histories() {
    gsc2_registry_computes_tracked_source_children_and_collects_typed_products();
    gsc2_registry_reuses_real_source_products_and_reclaims_only_the_last_owner();
    gsc2_registry_waiters_take_over_cancelled_owners_and_close_discards_abandoned_builders();
    gsc2_registry_failed_admission_and_provider_work_leave_no_unowned_products();
    gsc2_registry_key_slots_are_reclaimed_across_pinned_retirement_and_generation_reuse();
    gsc2_registry_keys_from_failed_queries_are_reclaimed_without_retiring_the_world();
    gsc2_registry_collection_preserves_pending_roots_and_blocks_mutation_through_key_sweeping();
    gsc2_registry_suspended_replay_owns_keys_after_parent_collection_until_recomputation();
}

fn diagnostic_case(mode: u32, evidence_name: &str) {
    static RESULTS: OnceLock<Result<Vec<i64>, String>> = OnceLock::new();
    let replacements = ["@ORACLE0@", "@ORACLE1@", "@ORACLE2@", "@ORACLE3@"]
        .into_iter()
        .enumerate()
        .map(|(mode, placeholder)| {
            let expected = diagnostic_fingerprint(&diagnostic_reference(mode as u32));
            let literal = expected
                .as_bytes()
                .iter()
                .map(|b| format!("\\x{b:02x}"))
                .collect::<String>();
            (placeholder, literal)
        })
        .collect::<Vec<_>>();
    let results = source_batch(
        &RESULTS,
        "engine/diagnostics.glorious",
        &replacements,
        "engine/diagnostics-batch",
        &[42, 42, 42, 42],
    );
    assert_eq!(results[mode as usize], 42, "{evidence_name}");
}

fn gsc2_diagnostic_canonicalization_matches_every_reference_field() {
    diagnostic_case(0, "engine/diagnostics_canonical");
}

fn gsc2_diagnostic_publication_validation_and_error_limit_match_the_reference() {
    diagnostic_case(1, "engine/diagnostics_validated");
}

fn gsc2_diagnostic_zero_error_limit_preserves_the_terminal_resource_fact() {
    diagnostic_case(2, "engine/diagnostics_zero_limit");
}

fn gsc2_diagnostic_invalid_related_locations_publish_the_exact_invariant_fact() {
    diagnostic_case(3, "engine/diagnostics_invalid_span");
}

#[test]
fn gsc2_diagnostic_failure_paths_discard_unpublished_batches() {
    assert_eq!(source_case("engine/diagnostic_failures.glorious"), 30);
}

fn gsc2_request_publication_combines_owned_results_diagnostics_packages_and_revision_traces() {
    publication_case(0, "engine/publication_lifecycle", 27);
}

fn gsc2_request_publication_rejects_unstaged_packages_invalid_spans_work_exhaustion_and_active_queries()
 {
    publication_case(1, "engine/publication_failures", 23);
}

fn gsc2_request_publication_rejects_stale_parent_and_session_authority_without_touching_new_owners()
{
    publication_case(2, "engine/publication_authority", 26);
}

fn publication_case(mode: u32, evidence_name: &str, expected: i64) {
    static RESULTS: OnceLock<Result<Vec<i64>, String>> = OnceLock::new();
    let results = source_batch(
        &RESULTS,
        "engine/publication.glorious",
        &[],
        "engine/publication-batch",
        &[27, 23, 26],
    );
    assert_eq!(results[mode as usize], expected, "{evidence_name}");
}

#[test]
fn gsc2_product_release_waits_for_the_last_owner_and_rejects_foreign_acknowledgments() {
    let case = "engine/product_release.glorious";
    let program = source_program(case, &[]);
    let (result, profile) = program.run_i64_for_authoring(Default::default()).unwrap();
    record_execution(case, &program, result, Some(&profile));
    assert_eq!(result, 30);
}

#[test]
fn gsc2_source_products_match_reference_bytes_lines_and_every_utf16_position() {
    use grandiose_stage0::LineIndex;
    let samples = [
        "",
        "a",
        "\n",
        "\n\n",
        "\r",
        "a\r\nb\rc\n",
        "\0a\0\n\0",
        "éλ中",
        "a😀b\n🦀\n",
        "e\u{301}\t👩\u{200d}💻",
        "\u{7f}\u{80}\u{7ff}\u{800}\u{d7ff}\u{e000}\u{ffff}\u{10000}\u{10ffff}",
        "\u{2028}\u{2029}\r\nlast line",
    ];
    fn word(bytes: &mut Vec<u8>, value: u32) {
        bytes.extend_from_slice(&u64::from(value).to_le_bytes());
    }
    fn escaped(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("\\x{b:02x}")).collect()
    }
    let file = Digest::of_bytes(b"line-fixture");
    let mut expected = Vec::new();
    let mut cases = String::new();
    for sample in samples {
        cases.push_str(&format!(
            "Vec::push(&mut inputs, owned(b\"{}\"));\n",
            escaped(sample.as_bytes())
        ));
        let fingerprint = Digest::of_bytes(sample.as_bytes());
        word(&mut expected, sample.len() as u32);
        expected.extend_from_slice(sample.as_bytes());
        expected.extend_from_slice(&file.as_bytes());
        expected.extend_from_slice(&fingerprint.as_bytes());
        // This is the source product's internal projection, not a Stage0 wire
        // commitment or a substitute for the normalized-world fingerprint.
        let domain = b"grandiose-line-index-v1";
        let mut projection = (domain.len() as u64).to_le_bytes().to_vec();
        projection.extend_from_slice(domain);
        projection.extend_from_slice(&file.as_bytes());
        projection.extend_from_slice(&fingerprint.as_bytes());
        expected.extend_from_slice(&Digest::of_bytes(&projection).as_bytes());
        let index = LineIndex::new(sample);
        word(&mut expected, index.line_count());
        word(&mut expected, 0);
        for (offset, byte) in sample.bytes().enumerate() {
            if byte == b'\n' {
                word(&mut expected, (offset + 1) as u32);
            }
        }
        for offset in (0..=sample.len() as u32 + 1).chain([u32::MAX]) {
            match index.position(sample, offset) {
                None => word(&mut expected, 0),
                Some(position) => {
                    word(&mut expected, 1);
                    word(&mut expected, position.line);
                    word(&mut expected, position.utf16_column);
                }
            }
        }
    }
    assert!(
        expected.len() < 65536,
        "source fixture's encoder must not truncate"
    );
    let case = "source/positions.glorious";
    let program = source_program(
        case,
        &[
            ("@CASES@", cases),
            ("@ORACLE@", escaped(&Digest::of_bytes(&expected).as_bytes())),
        ],
    );
    let (result, profile) = program.run_i64_for_authoring(Default::default()).unwrap();
    record_execution(case, &program, result, Some(&profile));
    assert_eq!(result, 42);
}

fn gsc2_registry_computes_tracked_source_children_and_collects_typed_products() {
    registry_history(0, 35, "registry/cold-hit-collection");
}

fn gsc2_registry_reuses_real_source_products_and_reclaims_only_the_last_owner() {
    registry_history(1, 96, "registry/reuse-retention");
}

fn gsc2_registry_waiters_take_over_cancelled_owners_and_close_discards_abandoned_builders() {
    registry_history(2, 47, "registry/interleaving-cancellation");
}

fn gsc2_registry_failed_admission_and_provider_work_leave_no_unowned_products() {
    registry_history(3, 235, "registry/capacity-work-cleanup");
}

fn registry_history(mode: i64, expected: i64, evidence_name: &str) {
    // Each scenario keeps its named comparator, but compilation and the
    // eight independent source histories run once per process. A compile
    // failure is retained too, rather than repeating the same expensive panic.
    static RESULTS: OnceLock<Result<Vec<i64>, String>> = OnceLock::new();
    let results = source_batch(
        &RESULTS,
        "registry/source.glorious",
        &[],
        "registry/source-batch",
        &[35, 96, 47, 235, 750, 466, 91, 91],
    );
    assert_eq!(
        results[usize::try_from(mode).unwrap()],
        expected,
        "{evidence_name}"
    );
}

#[test]
fn gsc2_registry_projects_committed_reads_into_atomic_public_dependency_facts() {
    use grandiose_stage0::{DependencyNode, DependencyStatus};
    fn literal(value: &[u8]) -> String {
        format!("b\"{}\"", value.iter().map(|byte| format!("\\x{byte:02x}")).collect::<String>())
    }
    fn source_digest(value: Digest) -> String {
        format!("digest(b\"{}\")", value.as_bytes().iter().map(|byte| format!("\\x{byte:02x}")).collect::<String>())
    }
    let support = fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("../../compiler/tests/registry/source.glorious")).unwrap();
    let support = support.split("fn retained(").next().unwrap().to_owned();
    let original = b"pub fn main() -> i64 { 42 }\n";
    let changed = b"pub fn main() -> i64 { 43 }\n";
    let package = PackageKey("app".into());
    let input = SourceInput::new(package.clone(), LogicalPath::parse("src/main.glorious").unwrap(), original.as_slice());
    let file = input.key;
    let mut request = CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"provider-dependency-reference")),
        mode: CompilationMode::Build, root_package: package.clone(), sources: vec![input],
        target: "stage0-vm".into(), semantic_options: BTreeMap::new(), codegen_options: BTreeMap::new(),
        capability_manifest: vec![], runtime_manifest: None,
    };
    let compiler = StageZeroCompiler::new();
    let mut parent = None;
    for (index, bytes) in [original.as_slice(), original.as_slice(), original.as_slice(), changed.as_slice()].into_iter().enumerate() {
        request.sources[0] = SourceInput::new(package.clone(), LogicalPath::parse("src/main.glorious").unwrap(), bytes);
        request.semantic_options.insert("unrelated".into(), index.to_string());
        let revision = compiler.import_revision(request.clone(), parent).unwrap();
        compiler.compile_revision(revision).unwrap();
        let trace = compiler.dependency_trace(revision, &DependencyNode::Input(file)).unwrap();
        assert_eq!(trace.revision, revision);
        assert_eq!(trace.node, DependencyNode::Input(file));
        assert_eq!(trace.fingerprint, Digest::of_bytes(bytes));
        assert!(trace.dependencies.is_empty());
        assert_eq!(trace.status, match index {
            0 => DependencyStatus::Cold,
            1 | 2 => DependencyStatus::Green { parent: parent.unwrap() },
            _ => DependencyStatus::Red { parent: parent.unwrap(), first_changed: DependencyNode::Input(file) },
        });
        parent = Some(revision);
    }
    let case = "registry/dependencies.glorious";
    let program = source_program(case, &[
        ("@SUPPORT@", support),
        ("@FILE@", source_digest(file.0)),
        ("@SECOND@", source_digest(Digest::of_bytes(b"dependency-unobserved-file"))),
        ("@DIGEST0@", source_digest(Digest::of_bytes(original))),
        ("@DIGEST1@", source_digest(Digest::of_bytes(changed))),
        ("@ORIGINAL@", literal(original)),
        ("@CHANGED@", literal(changed)),
    ]);
    let (results, profile) = program.run_tuple_i64_for_authoring(Default::default()).unwrap();
    record_execution_values(case, &program, "", &format!("{results:?}"), Some(&profile));
    assert_eq!(&results[..6], &[1, 1, 1, 1, 1, 1]);
    assert!(results[6] > 10, "every projection/preparation boundary was cancelled: {results:?}");
}

fn gsc2_registry_key_slots_are_reclaimed_across_pinned_retirement_and_generation_reuse() {
    registry_history(4, 16 * 45 + 15 * 2, "registry/key-retirement-churn");
}

fn gsc2_registry_keys_from_failed_queries_are_reclaimed_without_retiring_the_world() {
    registry_history(5, 16 * 27 + 34, "registry/failed-key-churn");
}

fn gsc2_registry_collection_preserves_pending_roots_and_blocks_mutation_through_key_sweeping() {
    registry_history(6, 91, "registry/pending-key-roots");
}

fn gsc2_registry_suspended_replay_owns_keys_after_parent_collection_until_recomputation() {
    registry_history(7, 91, "registry/replay-key-roots");
}

#[test]
fn gsc2_source_products_reject_corruption_wrong_revisions_and_discard_failed_work() {
    let invalid: &[&[u8]] = &[
        b"\x80",
        b"\xc0\xaf",
        b"\xc1\xbf",
        b"\xe0\x80\x80",
        b"\xed\xa0\x80",
        b"\xf0\x80\x80\x80",
        b"\xf4\x90\x80\x80",
        b"\xf5\x80\x80\x80",
        b"\xff",
        b"\xe2\x82",
        b"ok\xf0\x9f",
        b"a\xc2x",
    ];
    let mut cases = String::new();
    for bytes in invalid {
        let expected = std::str::from_utf8(bytes).unwrap_err().valid_up_to();
        let literal: String = bytes.iter().map(|b| format!("\\x{b:02x}")).collect();
        cases.push_str(&format!(
            "score = score + invalid(file, b\"{literal}\", {expected});\n"
        ));
    }
    let case = "source/failures.glorious";
    let program = source_program(case, &[("@INVALID@", cases)]);
    let (result, profile) = program.run_i64_for_authoring(Default::default()).unwrap();
    record_execution(case, &program, result, Some(&profile));
    // 12 UTF-8 rejections; 4 constructors; 2 admission checks; 16 line
    // failures; 3 line-budget + 3 late-cancel; 20 position failures; 3 budget;
    // 9 successful one-shot finishes; 5 identical-bytes/different-file checks.
    assert_eq!(
        result,
        invalid.len() as i64 + 4 + 2 + 16 + 3 + 3 + 20 + 3 + 9 + 5
    );
}

#[test]
fn gsc2_request_source_admission_matches_reference_validation_and_drives_real_queries() {
    use grandiose_stage0::{FileKey, InputError};
    fn escaped(bytes: &[u8]) -> String {
        bytes.iter().map(|byte| format!("\\x{byte:02x}")).collect()
    }
    let paths = [
        "",
        "/",
        "/a",
        "a/",
        "a//b",
        ".",
        "..",
        "a/./b",
        "a/../b",
        "a\\b",
        "a",
        "a.b",
        "...",
        "a/.../b",
        "C:foo",
        "a\0b",
        "é/😀",
        "src/main.glorious",
        "./a",
        "..a",
        "a..",
        "a/..x/b",
    ];
    let path_cases = paths
        .iter()
        .map(|path| {
            let rejected = i64::from(LogicalPath::parse(*path).is_err());
            format!(
                "score = score + path_case(b\"{}\", {rejected});\n",
                escaped(path.as_bytes())
            )
        })
        .collect::<String>();
    let package = PackageKey("app".into());
    let key = FileKey::new(&package, "src/main.glorious");
    let mut source_cases = String::new();
    let mut count = 0;
    // Deliberate simultaneous corruptions test the reference failure order.
    for bytes in [b"".as_slice(), b"a\n", "é😀".as_bytes(), b"\xff", b"a\xc2x"] {
        for (bad_key, bad_digest) in [(false, false), (true, false), (false, true), (true, true)] {
            let mut source = SourceInput::new(
                package.clone(),
                LogicalPath::parse("src/main.glorious").unwrap(),
                bytes,
            );
            if bad_key {
                source.key = FileKey(Digest::of_bytes(b"forged-file"));
            }
            if bad_digest {
                source.digest = Digest::of_bytes(b"forged-digest");
            }
            let request = CompilationRequest {
                build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"admission-oracle")),
                mode: CompilationMode::Check,
                root_package: package.clone(),
                sources: vec![source.clone()],
                target: "stage0-vm".into(),
                semantic_options: BTreeMap::new(),
                codegen_options: BTreeMap::new(),
                capability_manifest: vec![],
                runtime_manifest: None,
            };
            let expected = match request.normalize() {
                Ok(_) => 0,
                Err(InputError::SourceIdentityMismatch { .. }) => 1,
                Err(InputError::DigestMismatch { .. }) => 2,
                Err(InputError::InvalidUtf8(_)) => 3,
                other => panic!("unexpected reference admission result: {other:?}"),
            };
            source_cases.push_str(&format!(
                "score = score + decoded_case(b\"{}\", correct, b\"{}\", b\"{}\", b\"{}\", {expected});\n",
                escaped(&source.key.0.as_bytes()), escaped(&source.digest.as_bytes()),
                escaped(&Digest::of_bytes(bytes).as_bytes()), escaped(bytes),
            ));
            count += 1;
        }
    }
    let case = "request/admission.glorious";
    let program = source_program(
        case,
        &[
            ("@PATHS@", path_cases),
            ("@SOURCES@", source_cases),
            ("@KEY@", escaped(&key.0.as_bytes())),
        ],
    );
    let (results, profile) = program
        .run_tuple_i64_for_authoring(Default::default())
        .unwrap();
    record_execution_values(case, &program, "", &format!("{results:?}"), Some(&profile));
    assert_eq!(results, [paths.len() as i64, count, 10, 46, 2]);
}

#[test]
fn gsc2_query_journal_propagates_recovery_and_stops_obsolete_replay() {
    assert_eq!(source_case("engine/query_journal.glorious"), 42);
}

#[test]
fn gsc2_request_namespace_matches_root_alias_and_capability_set_admission() {
    use grandiose_stage0::{InputError, identity::package_module_alias};
    use std::collections::BTreeSet;
    fn literal(value: &[u8]) -> String {
        format!("b\"{}\"", value.iter().map(|byte| format!("\\x{byte:02x}")).collect::<String>())
    }
    fn witness(value: &SourceInput) -> String {
        format!("Witness {{ package: owned({}), path: owned({}), bytes: owned({}), key: owned({}), digest: owned({}) }}",
            literal(value.package.0.as_bytes()), literal(value.logical_path.as_str().as_bytes()),
            literal(&value.bytes), literal(&value.key.0.as_bytes()), literal(&value.digest.as_bytes()))
    }
    let cases: Vec<(&str, Vec<&str>, Vec<&str>)> = vec![
        ("p", vec!["p"], vec![]),
        ("p", vec!["q", "p", "q"], vec!["z", "a", "é"]),
        ("p", vec!["q", "q", "p"], vec!["é", "z", "a"]),
        ("a", vec!["q", "p"], vec!["cap:io", "\0", "猫", "a"]),
        ("z", vec!["p", "q"], vec!["b", "a"]),
        ("bad root", vec!["p"], vec![]),
        ("z bad", vec!["a@1", "a@2"], vec!["*"]),
        ("", vec!["p"], vec!["*x"]),
        ("p", vec!["-", "_"], vec![]),
        ("p@1", vec!["p@2"], vec![]),
        ("p", vec!["math-lib@a", "math_lib@b"], vec![]),
        ("p", vec!["Ab", "BA"], vec![]),
        ("p", vec!["a@💜bad version"], vec![]),
        ("p", vec!["é"], vec![]),
        ("p", vec!["1bad", "z@one", "z@two"], vec![]),
        ("p", vec!["p"], vec!["read", "read"]),
        ("p", vec!["p"], vec!["read", "read", "z *"]),
        ("p", vec!["p"], vec!["", "read"]),
        ("p", vec!["p"], vec!["é", "a\u{a0}b"]),
        ("p", vec!["p"], vec!["zero\u{200b}width", "a\0b", "读"]),
        ("p", vec!["p"], vec!["read", "*"]),
        ("p", vec!["p"], vec!["b", "a", "b", "a"]),
    ];
    let default = SourceInput::new(PackageKey("p".into()), LogicalPath::parse("0").unwrap(), b"x".as_slice());
    let mut generated = format!("fn witness_default() -> Witness {{ {} }}\n", witness(&default));
    let mut roots = Vec::new();
    for (index, (root, packages, capabilities)) in cases.iter().enumerate() {
        let inputs: Vec<_> = packages.iter().enumerate().map(|(index, package)| SourceInput::new(
            PackageKey((*package).into()), LogicalPath::parse(index.to_string()).unwrap(), b"x".as_slice(),
        )).collect();
        let request = CompilationRequest {
            build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"namespace-admission-oracle")),
            mode: CompilationMode::Check, root_package: PackageKey((*root).into()), sources: inputs.clone(),
            target: "stage0-vm".into(), semantic_options: BTreeMap::new(), codegen_options: BTreeMap::new(),
            capability_manifest: capabilities.iter().map(|value| (*value).into()).collect(), runtime_manifest: None,
        };
        generated.push_str(&format!("fn ns_oracle_{index}() -> i64 {{ let inputs = Vec<request::SourceInput>::new(); let setup = as<i64>(1);\n"));
        for input in &inputs { generated.push_str(&format!("setup = setup * push(&mut inputs, {});\n", witness(input))); }
        generated.push_str("let caps = Vec<String>::new(); let expected_caps = Vec<String>::new(); let expected_sources = Vec<Witness>::new(); let aliases = Vec<AliasWitness>::new();\n");
        for capability in capabilities { generated.push_str(&format!("Vec::push(&mut caps, text({}));\n", literal(capability.as_bytes()))); }
        let (kind, a, b, c) = match request.normalize() {
            Ok(world) => {
                for source in world.sources.iter() { generated.push_str(&format!("Vec::push(&mut expected_sources, {});\n", witness(source))); }
                let packages: BTreeSet<_> = world.sources.iter().map(|source| source.package.clone()).chain([world.root_package]).collect();
                for package in packages {
                    let alias = package_module_alias(&package).unwrap();
                    generated.push_str(&format!("Vec::push(&mut aliases, AliasWitness {{ package: owned({}), alias: owned({}) }});\n", literal(package.0.as_bytes()), literal(alias.as_bytes())));
                }
                for capability in world.capability_manifest.iter() { generated.push_str(&format!("Vec::push(&mut expected_caps, text({}));\n", literal(capability.as_bytes()))); }
                (0, String::new(), String::new(), String::new())
            }
            Err(InputError::InvalidPackageModuleAlias(package)) => (1, package.0, String::new(), String::new()),
            Err(InputError::DuplicatePackageModuleAlias { alias, first, second }) => (2, alias, first.0, second.0),
            Err(InputError::InvalidCapability(value)) => (3, value, String::new(), String::new()),
            Err(InputError::DuplicateCapability(value)) => (4, value, String::new(), String::new()),
            other => panic!("unexpected namespace oracle: {other:?}"),
        };
        generated.push_str(&format!("setup * ns_case(text({}), inputs, caps, NamespaceExpected {{ kind: {kind}, a: owned({}), b: owned({}), c: owned({}), root: owned({}), sources: expected_sources, aliases: aliases, capabilities: expected_caps }}) }}\n",
            literal(root.as_bytes()), literal(a.as_bytes()), literal(b.as_bytes()), literal(c.as_bytes()), literal(root.as_bytes())));
        roots.push(format!("ns_oracle_{index}()"));
    }
    generated.push_str(&format!("fn ns_oracles() -> i64 {{ {} }}\n", roots.join(" + ")));
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let support = fs::read_to_string(root.join("compiler/tests/request/sources.glorious")).unwrap();
    // Reuse only the locked fixture's source-admission/witness helpers. They
    // remain Glorious code in the emitted program, not native admission calls.
    let support = support.split_once("@CASES@").unwrap().0.to_owned();
    let case = "request/namespace.glorious";
    let text_cases: Vec<Vec<String>> = vec![
        vec![], vec!["".into()], vec!["z".into(), "b".into(), "a".into()],
        vec!["ab".into(), "a".into(), "a".into(), "".into(), "ab".into()],
        ["猫", "e\u{301}", "é", "a\0b", "a", "\0", "💜"].map(str::to_owned).to_vec(),
        ["b", "a", "", "c"].map(|suffix| "x".repeat(80) + suffix).to_vec(),
        (0..32).rev().map(|index| format!("key-{index:02}")).collect(),
    ];
    let mut text_generated = String::new();
    for (index, inputs) in text_cases.iter().enumerate() {
        text_generated.push_str(&format!("fn text_oracle_{index}() -> i64 {{ let inputs = Vec<String>::new(); let expected = Vec<String>::new();\n"));
        for value in inputs { text_generated.push_str(&format!("Vec::push(&mut inputs, text({}));\n", literal(value.as_bytes()))); }
        let mut expected = inputs.clone(); expected.sort();
        for value in &expected { text_generated.push_str(&format!("Vec::push(&mut expected, text({}));\n", literal(value.as_bytes()))); }
        text_generated.push_str("text_case(inputs, expected) }\n");
    }
    text_generated.push_str(&format!("fn text_oracles() -> i64 {{ {} }}\n", (0..text_cases.len()).map(|index| format!("text_oracle_{index}()")).collect::<Vec<_>>().join(" + ")));
    let program = source_program(case, &[("@SUPPORT@", support), ("@CASES@", generated), ("@TEXT_CASES@", text_generated)]);
    let (results, profile) = program.run_tuple_i64_for_authoring(Default::default()).unwrap();
    record_execution_values(case, &program, "", &format!("{results:?}"), Some(&profile));
    assert_eq!(results, [cases.len() as i64, 116, 8, text_cases.len() as i64, 11]);
}

#[test]
fn gsc2_request_options_preserve_map_replacement_and_canonical_key_order() {
    fn literal(value: &str) -> String {
        format!("b\"{}\"", value.bytes().map(|byte| format!("\\x{byte:02x}")).collect::<String>())
    }
    fn set(key: &str, value: &str) -> (String, Option<String>) { (key.into(), Some(value.into())) }
    let base = [set("a", "1"), set("b", "2"), set("c", "3")];
    let mut cases = Vec::new();
    for indices in [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]] {
        cases.push(indices.map(|index| base[index].clone()).to_vec());
    }
    cases.push(vec![]);
    cases.push(vec![set("", "")]);
    cases.push(vec![set("a", "first"), set("a", "last"), set("optimization-level", "2"), set("optimization-level", "3")]);
    cases.push(vec![set("b", "2"), set("a", "1"), ("b".into(), None), ("missing".into(), None), set("b", "new")]);
    cases.push(vec![set("Ab", "first"), set("BA", "second"), set("Ab", "replaced")]);
    cases.push(vec![set("é", "x\0y"), set("e\u{301}", "💜"), set("\0", ""), set("* key", "anything\n")]);
    let mut churn = (0..32).map(|index| set(&format!("key-{index:02}"), &index.to_string())).collect::<Vec<_>>();
    churn.extend((0..16).map(|index| (format!("key-{index:02}"), None)));
    churn.extend((0..16).rev().map(|index| set(&format!("key-{index:02}"), "again")));
    cases.push(churn);
    cases.push(["z", "a", "", "b"].map(|suffix| set(&("x".repeat(80) + suffix), suffix)).to_vec());
    let mut generated = String::new();
    for (index, actions) in cases.iter().enumerate() {
        let mut expected = BTreeMap::new();
        generated.push_str(&format!("fn oracle_{index}() -> i64 {{ let values = HashMap<String, String>::new(); let expected = Vec<Pair>::new();\n"));
        for (action, (key, value)) in actions.iter().enumerate() {
            match value {
                Some(value) => {
                    expected.insert(key.clone(), value.clone());
                    generated.push_str(&format!("HashMap::insert(&mut values, text({}), text({}));\n", literal(key), literal(value)));
                }
                None => {
                    expected.remove(key);
                    generated.push_str(&format!("let removed_{action} = text({}); HashMap::remove(&mut values, &removed_{action});\n", literal(key)));
                }
            }
        }
        assert!(!expected.contains_key("missing_option_not_in_fixture"));
        for (key, value) in &expected {
            generated.push_str(&format!("Vec::push(&mut expected, Pair {{ key: text({}), value: text({}) }});\n", literal(key), literal(value)));
        }
        generated.push_str("check(values, expected) }\n");
    }
    generated.push_str(&format!("fn oracles() -> i64 {{ {} }}\n", (0..cases.len()).map(|index| format!("oracle_{index}()")).collect::<Vec<_>>().join(" + ")));
    let case = "request/options.glorious";
    let program = source_program(case, &[("@CASES@", generated)]);
    let (results, profile) = program.run_tuple_i64_for_authoring(Default::default()).unwrap();
    record_execution_values(case, &program, "", &format!("{results:?}"), Some(&profile));
    assert_eq!(results, [cases.len() as i64, 108, 10]);
}

fn world_request_reference_cases(group: usize) -> Vec<CompilationRequest> {
    use grandiose_stage0::{BootstrapLimits, BootstrapStage};
    use grandiose_stage0::runtime_manifest::{FloatBinaryOp, FloatPrimitive, FloatWidth, HostImportSelector, PrimitiveRole, PrimitiveSelector, RuntimeManifestInput};
    let base = CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"normalized-world-author")),
        mode: CompilationMode::Check, root_package: PackageKey("app@1".into()),
        sources: vec![SourceInput::new(PackageKey("app@1".into()), LogicalPath::parse("src/main.glorious").unwrap(), b"abc\n".as_slice())],
        target: "stage0-vm".into(), semantic_options: BTreeMap::from([("a".into(), "one".into())]),
        codegen_options: BTreeMap::from([("optimization-level".into(), "2".into())]),
        capability_manifest: vec!["file.read".into(), "file.write".into()], runtime_manifest: None,
    };
    let runtime = RuntimeManifestInput { standard_library: PackageKey("std@1".into()),
        selectors: vec![
            PrimitiveSelector { role: PrimitiveRole::IntCheckedDiv, module_path: "std::math".into(), name: "divide".into() },
            PrimitiveSelector { role: PrimitiveRole::Blake3, module_path: "std::hash".into(), name: "digest".into() },
            PrimitiveSelector { role: PrimitiveRole::Abort, module_path: "std".into(), name: "abort".into() },
            // Derived role order puts Float before Blake3, unlike wire-tag order.
            PrimitiveSelector { role: PrimitiveRole::Float(FloatPrimitive::Binary { width: FloatWidth::F32, operation: FloatBinaryOp::Add }), module_path: "std::float".into(), name: "add".into() },
        ], host_imports: vec![
            HostImportSelector { module_path: "z".into(), name: "read".into(), capability: "file.read".into(), symbol: "host_read".into() },
            HostImportSelector { module_path: "a".into(), name: "write".into(), capability: "file.write".into(), symbol: "host_write".into() },
        ] };
    let mut cases = Vec::new();
    match group {
        0 => {
            for mode in [CompilationMode::Check, CompilationMode::Build, CompilationMode::Test, CompilationMode::Inspect, CompilationMode::Ide] {
                let mut value = base.clone(); value.mode = mode; cases.push(value);
            }
            let mut value = base.clone(); value.build.compiler = Digest::of_bytes(b"another-author"); cases.push(value);
            for field in 0..6 {
                let mut value = base.clone();
                match field {
                    0 => value.build.language_generation = 0x12345678,
                    1 => value.build.query_generation = 0x89abcdef,
                    2 => value.build.interface_generation = u32::MAX,
                    3 => value.build.cache_generation = 0,
                    4 => value.build.bytecode_generation = 0x11223344,
                    _ => value.build.verifier_generation = 0x55667788,
                }
                cases.push(value);
            }
        }
        1 => {
            cases.push(base.clone());
            let mut value = base.clone(); value.root_package = PackageKey("root-only@9".into()); cases.push(value);
            let mut value = base.clone(); value.target = "x".repeat(31) + "😀\0é"; cases.push(value);
            let mut value = base.clone(); value.target.clear(); cases.push(value);
            for (package, path, bytes) in [
                ("math-lib@2", "src/main.glorious", b"abc\n".as_slice()),
                ("app@1", "other/é.glorious", b"abc\n".as_slice()),
                ("app@1", "src/main.glorious", "é😀\r\n".as_bytes()),
                ("app@1", "src/main.glorious", b"".as_slice()),
            ] {
                let mut value = base.clone(); value.sources[0] = SourceInput::new(PackageKey(package.into()), LogicalPath::parse(path).unwrap(), bytes); cases.push(value);
            }
            let mut multiple = base.clone();
            multiple.sources.push(SourceInput::new(PackageKey("math-lib@2".into()), LogicalPath::parse("src/lib.glorious").unwrap(), b"library".as_slice()));
            cases.push(multiple.clone()); multiple.sources.reverse(); multiple.capability_manifest.reverse(); cases.push(multiple);
            let mut value = base.clone(); value.semantic_options.insert("a".into(), "changed".into()); cases.push(value);
            let mut value = base.clone(); value.semantic_options = BTreeMap::from([("b".into(), "one".into())]); cases.push(value);
            let mut value = base.clone(); value.semantic_options.insert("".into(), "\0".into()); cases.push(value);
            let mut value = base.clone(); value.semantic_options.clear(); cases.push(value);
            let mut value = base.clone(); value.codegen_options.insert("optimization-level".into(), "3".into()); cases.push(value);
            let mut value = base.clone(); value.codegen_options = BTreeMap::from([("different".into(), "2".into())]); cases.push(value);
            let mut value = base.clone(); value.codegen_options.clear(); cases.push(value);
            let mut value = base.clone(); value.capability_manifest.clear(); cases.push(value);
            let mut value = base.clone(); value.capability_manifest[0] = "another.capability".into(); cases.push(value);
        }
        2 => {
            cases.push(base.clone());
            let mut populated = base.clone(); populated.runtime_manifest = Some(runtime.clone()); cases.push(populated.clone());
            let mut value = base.clone(); value.runtime_manifest = Some(RuntimeManifestInput { standard_library: PackageKey("".into()), selectors: vec![], host_imports: vec![] }); cases.push(value);
            for field in 0..10 {
                let mut value = populated.clone(); let manifest = value.runtime_manifest.as_mut().unwrap();
                match field {
                    0 => manifest.standard_library = PackageKey("different-stdlib@9".into()),
                    1 => manifest.selectors[0].module_path = "x".repeat(31) + "😀\0é",
                    2 => manifest.selectors[0].name.clear(),
                    3 => manifest.selectors[0].role = PrimitiveRole::U32CheckedDiv,
                    4 => manifest.host_imports[0].module_path = "module\0suffix".into(),
                    5 => manifest.host_imports[0].name = "renamed".into(),
                    6 => manifest.host_imports[0].capability = "other.capability".into(),
                    7 => manifest.host_imports[0].symbol = "symbol\0suffix".into(),
                    8 => manifest.selectors.clear(),
                    _ => manifest.host_imports.clear(),
                }
                cases.push(value);
            }
            let mut value = populated; let manifest = value.runtime_manifest.as_mut().unwrap();
            manifest.selectors.reverse(); manifest.host_imports.reverse(); cases.push(value);
        }
        3 => {
            let seed = BootstrapStage { ordinal: 1, producer: base.build.compiler, optimization_level: 2,
                limits: BootstrapLimits { max_sources: 10, max_total_source_bytes: 10000 }, expected_artifact: None };
            let mut value = base.clone(); value.mode = CompilationMode::Bootstrap(seed.clone()); cases.push(value);
            for ordinal in [2, 3, u32::MAX] {
                let mut value = base.clone(); let mut stage = seed.clone(); stage.ordinal = ordinal; stage.expected_artifact = Some(stage.producer);
                value.mode = CompilationMode::Bootstrap(stage); cases.push(value);
            }
            for level in [0, 1, 3] {
                let mut value = base.clone(); let mut stage = seed.clone(); stage.optimization_level = level;
                value.codegen_options.insert("optimization-level".into(), level.to_string()); value.mode = CompilationMode::Bootstrap(stage); cases.push(value);
            }
            let mut value = base.clone(); let mut stage = seed.clone(); stage.limits.max_sources = 1; value.mode = CompilationMode::Bootstrap(stage); cases.push(value);
            let mut value = base.clone(); let mut stage = seed.clone(); stage.limits.max_total_source_bytes = u64::MAX; value.mode = CompilationMode::Bootstrap(stage); cases.push(value);
            let mut value = base.clone(); value.mode = CompilationMode::Bootstrap(seed.clone()); value.codegen_options.clear(); cases.push(value);
            let mut value = base; value.mode = CompilationMode::Bootstrap(seed); value.runtime_manifest = Some(runtime); cases.push(value);
        }
        _ => unreachable!(),
    }
    cases
}

fn world_request_witness(value: &CompilationRequest, name: &str) -> String {
    fn literal(bytes: &[u8]) -> String { format!("b\"{}\"", bytes.iter().map(|byte| format!("\\x{byte:02x}")).collect::<String>()) }
    fn text(value: &str) -> String { format!("text({})", literal(value.as_bytes())) }
    fn digest(value: Digest) -> String { format!("digest({})", literal(&value.as_bytes())) }
    fn emit(value: &CompilationRequest, name: &str) -> String {
        use grandiose_stage0::runtime_manifest::{FloatPrimitive, PrimitiveRole};
        let build = &value.build;
        let mode = match &value.mode {
            CompilationMode::Bootstrap(stage) => format!("request::CompilationMode::Bootstrap(request::BootstrapStage {{ ordinal: {}, producer: {}, optimization_level: {}, limits: request::BootstrapLimits {{ max_sources: {}, max_total_source_bytes: {} }}, expected_artifact: {} }})",
                stage.ordinal, digest(stage.producer), stage.optimization_level, stage.limits.max_sources, stage.limits.max_total_source_bytes,
                stage.expected_artifact.map(|value| format!("Result::Ok({})", digest(value))).unwrap_or("None".into())),
            other => format!("request::CompilationMode::{other:?}"),
        };
        let mut result = format!("fn {name}() -> Witness {{ let values = Vec<request::SourceInput>::new(); let valid = 1;\n");
        for source in &value.sources {
            result.push_str(&format!("valid = valid * add_source(&mut values, {}, {}, {}, {}, {});\n",
                text(&source.package.0), text(source.logical_path.as_str()), literal(&source.bytes), digest(source.key.0), digest(source.digest)));
        }
        result.push_str("let semantic = HashMap<String, String>::new(); let codegen = HashMap<String, String>::new(); let caps = Vec<String>::new();\n");
        for (binding, options) in [("semantic", &value.semantic_options), ("codegen", &value.codegen_options)] {
            // Reverse canonical order so the source implementation must create
            // its own canonical index. Values remain ordinary map inputs.
            for (key, value) in options.iter().rev() { result.push_str(&format!("HashMap::insert(&mut {binding}, {}, {});\n", text(key), text(value))); }
        }
        for capability in &value.capability_manifest { result.push_str(&format!("Vec::push(&mut caps, {});\n", text(capability))); }
        let runtime = match &value.runtime_manifest {
            None => "None".to_owned(),
            Some(manifest) => {
                result.push_str("let selectors = Vec<PrimitiveSelector>::new(); let hosts = Vec<HostImportSelector>::new();\n");
                for selector in &manifest.selectors {
                    let role = match selector.role {
                        PrimitiveRole::Float(FloatPrimitive::Binary { width, operation }) => format!("PrimitiveRole::Float(FloatPrimitive::Binary {{ width: FloatWidth::{width:?}, operation: FloatBinaryOp::{operation:?} }})"),
                        PrimitiveRole::Float(FloatPrimitive::Convert { from, to, checked }) => format!("PrimitiveRole::Float(FloatPrimitive::Convert {{ from: ScalarType::{from:?}, to: ScalarType::{to:?}, checked: {checked} }})"),
                        PrimitiveRole::Float(_) => panic!("add an exact source witness for this floating fixture role"),
                        role => format!("PrimitiveRole::{role:?}"),
                    };
                    result.push_str(&format!("Vec::push(&mut selectors, PrimitiveSelector {{ role: {role}, module_path: {}, name: {} }});\n", text(&selector.module_path), text(&selector.name)));
                }
                for host in &manifest.host_imports { result.push_str(&format!("Vec::push(&mut hosts, HostImportSelector {{ module_path: {}, name: {}, capability: {}, symbol: {} }});\n", text(&host.module_path), text(&host.name), text(&host.capability), text(&host.symbol))); }
                format!("Result::Ok(RuntimeManifestInput {{ standard_library: identity::PackageKey {{ value: {} }}, selectors: selectors, host_imports: hosts }})", text(&manifest.standard_library.0))
            }
        };
        result.push_str(&format!("Witness {{ valid: valid, input: request::CompilationRequest {{ build: request::CompilerBuildIdentity {{ compiler: {}, language_generation: {}, query_generation: {}, interface_generation: {}, cache_generation: {}, bytecode_generation: {}, verifier_generation: {} }}, mode: {mode}, root_package: identity::PackageKey {{ value: {} }}, sources: values, target: {}, semantic_options: semantic, codegen_options: codegen, capability_manifest: caps, runtime_manifest: {runtime} }} }} }}\n",
            digest(build.compiler), build.language_generation, build.query_generation, build.interface_generation, build.cache_generation, build.bytecode_generation, build.verifier_generation, text(&value.root_package.0), text(&value.target)));
        result
    }
    emit(value, name)
}

fn world_request_reference_run(group: usize) {
    fn digest(value: Digest) -> String { format!("digest(b\"{}\")", value.as_bytes().iter().map(|byte| format!("\\x{byte:02x}")).collect::<String>()) }
    let cases = world_request_reference_cases(group); let mut generated = String::new();
    for (index, raw) in cases.iter().enumerate() {
        let expected = raw.clone().normalize().expect("reference case must be a valid complete request");
        let canonical = CompilationRequest { build: expected.build.clone(), mode: expected.mode.clone(), root_package: expected.root_package.clone(),
            sources: expected.sources.to_vec(), target: expected.target.clone(), semantic_options: expected.semantic_options.clone(),
            codegen_options: expected.codegen_options.clone(), capability_manifest: expected.capability_manifest.to_vec(), runtime_manifest: expected.runtime_manifest.clone() };
        generated.push_str(&world_request_witness(raw, &format!("raw_{index}")));
        generated.push_str(&world_request_witness(&canonical, &format!("expected_{index}")));
        generated.push_str(&format!("fn case_{index}() -> i64 {{ check(raw_{index}(), expected_{index}(), {}) }}\n", digest(expected.fingerprint)));
    }
    generated.push_str(&format!("fn oracles() -> i64 {{ {} }}\n", (0..cases.len()).map(|index| format!("case_{index}()")).collect::<Vec<_>>().join(" + ")));
    let case = "request/world.glorious";
    let program = source_program(case, &[("@CASES@", generated)]);
    let (result, profile) = program.run_i64_for_authoring(Default::default()).unwrap();
    record_execution(&format!("request/world-{group}"), &program, result, Some(&profile));
    assert_eq!(result, cases.len() as i64, "complete world reference group {group}");
}

#[test]
fn gsc2_request_world_build_identity_and_modes_match_reference() { world_request_reference_run(0); }
#[test]
fn gsc2_request_world_sources_options_and_capabilities_match_reference() { world_request_reference_run(1); }
#[test]
fn gsc2_request_world_complete_runtime_input_matches_reference() { world_request_reference_run(2); }
#[test]
fn gsc2_request_world_bootstrap_provenance_matches_reference() { world_request_reference_run(3); }

fn world_fixture_support() -> String {
    include_str!("../../../compiler/tests/request/world.glorious").split_once("@CASES@").unwrap().0.to_owned()
}

#[test]
fn gsc2_normalized_world_registry_preserves_admission_reuse_and_retirement() {
    use grandiose_stage0::{CompilerDatabase, LineIndex, RevisionError, RevisionId};
    fn literal(value: &[u8]) -> String {
        format!("b\"{}\"", value.iter().map(|byte| format!("\\x{byte:02x}")).collect::<String>())
    }
    fn digest(value: Digest) -> String { format!("digest({})", literal(&value.as_bytes())) }
    let original_text = "first é😀\r\nsecond\0line\n";
    let changed_text = "first é😀\r\nchanged\nlast 🦀";
    let mut original = world_request_reference_cases(2).remove(1);
    original.sources[0] = SourceInput::new(original.root_package.clone(),
        LogicalPath::parse("src/main.glorious").unwrap(), original_text.as_bytes());
    let file = original.sources[0].key;
    original.sources.push(SourceInput::new(PackageKey("helper@2".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(), b"other file\n".as_slice()));
    let mut equivalent = original.clone();
    equivalent.sources.reverse();
    equivalent.capability_manifest.reverse();
    let runtime = equivalent.runtime_manifest.as_mut().unwrap();
    runtime.selectors.reverse();
    runtime.host_imports.reverse();
    let mut child = original.clone();
    child.target = "other-target".into();
    child.semantic_options.insert("unrelated".into(), "changed".into());
    child.codegen_options.insert("optimization-level".into(), "3".into());
    child.capability_manifest.push("another.capability".into());
    let mut changed = child.clone();
    changed.sources[0] = SourceInput::new(changed.root_package.clone(),
        LogicalPath::parse("src/main.glorious").unwrap(), changed_text.as_bytes());
    let cases = [original, equivalent, child, changed];
    let worlds = cases.iter().cloned().map(|value| value.normalize().unwrap()).collect::<Vec<_>>();
    assert_eq!(worlds[0].fingerprint, worlds[1].fingerprint);
    assert_ne!(worlds[0].fingerprint, worlds[2].fingerprint);
    assert_ne!(worlds[2].fingerprint, worlds[3].fingerprint);

    // The real Stage0 database supplies the admission/retention oracle, not
    // a mock of the source registry. Source/line query storage is separately
    // checked by the production source engine's execution and retained counts.
    let reference = CompilerDatabase::new();
    let root = reference.import(cases[0].clone(), None).unwrap();
    let pinned = reference.open(root).unwrap();
    let foreign = RevisionId { database: root.database.wrapping_add(1), ordinal: root.ordinal };
    let unknown = RevisionId { database: root.database, ordinal: 1000 };
    assert!(matches!(reference.import(cases[1].clone(), Some(foreign)),
        Err(RevisionError::StaleRevision(actual)) if actual == foreign));
    assert!(matches!(reference.import(cases[1].clone(), Some(unknown)),
        Err(RevisionError::UnknownRevision(actual)) if actual == unknown));
    assert_eq!(reference.import(cases[1].clone(), Some(root)).unwrap(), root);
    let child = reference.import(cases[2].clone(), Some(root)).unwrap();
    let changed = reference.import(cases[3].clone(), Some(child)).unwrap();
    let child_pin = reference.open(child).unwrap();
    let changed_pin = reference.open(changed).unwrap();
    assert_ne!(root, child);
    assert_ne!(child, changed);
    assert_eq!(child_pin.parent(), Some(root));
    assert_eq!(changed_pin.parent(), Some(child));
    for (snapshot, expected) in [(&pinned, original_text), (&child_pin, original_text), (&changed_pin, changed_text)] {
        let source = snapshot.world().sources.iter().find(|source| source.key == file).unwrap();
        assert_eq!(source.bytes.as_ref(), expected.as_bytes());
    }
    reference.retire_revision(root).unwrap();
    assert!(matches!(reference.import(cases[2].clone(), Some(root)), Err(RevisionError::RetiredRevision(actual)) if actual == root));
    assert_eq!(reference.collect_retired().collected, 0);
    drop(pinned);
    assert_eq!(reference.collect_retired().collected, 1);
    assert_eq!(child_pin.world().fingerprint, worlds[2].fingerprint);
    reference.retire_revision(child).unwrap();
    drop(child_pin);
    assert_eq!(reference.collect_retired().collected, 1);
    assert_eq!(changed_pin.world().fingerprint, worlds[3].fingerprint);
    reference.retire_revision(changed).unwrap();
    drop(changed_pin);
    assert_eq!(reference.collect_retired().collected, 1);
    assert_eq!(reference.retention_stats().retained_revisions, 0);

    let mut generated = String::new();
    for (index, raw) in cases.iter().enumerate() {
        generated.push_str(&world_request_witness(raw, &format!("fixture_{index}")));
    }
    generated.push_str("fn fixture(index: usize) -> Witness { handle index { 0 => fixture_0(), 1 => fixture_1(), 2 => fixture_2(), _ => fixture_3() } }\n");
    generated.push_str(&format!("fn fixture_file() -> identity::FileKey {{ identity::FileKey {{ digest: {} }} }}\n", digest(file.0)));
    generated.push_str(&format!("fn fixture_digest(index: usize) -> identity::Digest {{ handle index {{ {} }} }}\n",
        worlds.iter().enumerate().map(|(index, world)| format!("{} => {}", if index == 3 { "_".into() } else { index.to_string() }, digest(world.fingerprint))).collect::<Vec<_>>().join(", ")));
    generated.push_str(&format!("fn fixture_contents(changed: Bool) -> Slice<'static, u8> {{ handle changed {{ false => {}, true => {} }} }}\n",
        literal(original_text.as_bytes()), literal(changed_text.as_bytes())));
    let mut fingerprints = Vec::new();
    let mut line_fingerprints = Vec::new();
    let mut line_cases = Vec::new();
    for (changed, sample) in [(false, original_text), (true, changed_text)] {
        let fingerprint = Digest::of_bytes(sample.as_bytes());
        fingerprints.push(format!("{changed} => {}", digest(fingerprint)));
        // Internal source-product projection, not a Stage0 wire commitment.
        let domain = b"grandiose-line-index-v1";
        let mut projection = (domain.len() as u64).to_le_bytes().to_vec();
        projection.extend_from_slice(domain);
        projection.extend_from_slice(&file.0.as_bytes());
        projection.extend_from_slice(&fingerprint.as_bytes());
        line_fingerprints.push(format!("{changed} => {}", digest(Digest::of_bytes(&projection))));
        let index = LineIndex::new(sample);
        let starts = std::iter::once(0).chain(sample.bytes().enumerate().filter_map(|(offset, byte)| (byte == b'\n').then_some(offset + 1))).collect::<Vec<_>>();
        assert_eq!(starts.len(), index.line_count() as usize);
        for (line, start) in starts.iter().enumerate() {
            let position = index.position(sample, *start as u32).unwrap();
            assert_eq!((position.line, position.utf16_column), (line as u32, 0));
        }
        line_cases.push(format!("{changed} => eq(as<i64>(source::line_count(index)), {}) * handle Slice::len(&starts) == {} {{ false => 0, true => {} }}",
            index.line_count(), starts.len(), starts.iter().enumerate().map(|(index, offset)| format!("eq(as<i64>(*Slice::get_unchecked(starts, {index})), {offset})")).collect::<Vec<_>>().join(" * ")));
    }
    generated.push_str(&format!("fn fixture_source_digest(changed: Bool) -> identity::Digest {{ handle changed {{ {} }} }}\n", fingerprints.join(", ")));
    generated.push_str(&format!("fn fixture_line_digest(changed: Bool) -> identity::Digest {{ handle changed {{ {} }} }}\n", line_fingerprints.join(", ")));
    generated.push_str(&format!("fn expected_lines(index: &source::LineIndex, changed: Bool) -> i64 {{ let starts = source::line_starts(index); handle changed {{ {} }} }}\n", line_cases.join(", ")));
    let case = "request/world_registry.glorious";
    let program = source_program(case, &[("@SUPPORT@", world_fixture_support()), ("@WITNESSES@", generated)]);
    let (results, profile) = program.run_tuple_i64_for_authoring(Default::default()).unwrap();
    record_execution_values(case, &program, "", &format!("{results:?}"), Some(&profile));
    assert_eq!(results, [1, 1, 1, 1, 1]);
}

#[test]
fn gsc2_request_world_lifecycle_preserves_cancellation_work_and_fingerprint_limits() {
    use grandiose_stage0::runtime_manifest::{HostImportSelector, PrimitiveRole, PrimitiveSelector, RuntimeManifestInput};
    let mut sample = world_request_reference_cases(3).remove(0);
    sample.root_package = PackageKey("app".into());
    sample.sources = vec![SourceInput::new(sample.root_package.clone(), LogicalPath::parse("a").unwrap(), b"".as_slice())];
    sample.target = "t".repeat(65);
    sample.semantic_options = BTreeMap::from([("s".into(), "v".into())]);
    sample.capability_manifest = vec!["c".into()];
    sample.runtime_manifest = Some(RuntimeManifestInput { standard_library: PackageKey("std".into()), selectors: vec![
        PrimitiveSelector { role: PrimitiveRole::Abort, module_path: "m".into(), name: "n".into() },
    ], host_imports: vec![HostImportSelector { module_path: "m".into(), name: "n".into(), capability: "c".into(), symbol: "s".into() }] });
    let expected = sample.clone().normalize().unwrap();
    // Independent extent accounting for the exact world-v2 framed fields.
    // The semantic digest itself comes from the reference normalizer.
    let field = |width: usize| 8 + width;
    let mut length = field(b"grandiose-stage0-world-v2".len()) + field(32) + 6 * field(4) + field(1);
    if let CompilationMode::Bootstrap(stage) = &expected.mode {
        length += field(b"bootstrap-stage-v2".len()) + field(4) + field(32) + field(1) + field(4) + field(8) + field(1);
        if stage.expected_artifact.is_some() { length += field(32); }
    }
    length += field(expected.root_package.0.len()) + field(expected.target.len()) + field(8);
    for source in expected.sources.iter() { length += field(source.package.0.len()) + field(source.logical_path.as_str().len()) + 2 * field(32); }
    for map in [&expected.semantic_options, &expected.codegen_options] {
        length += field(8); for (key, value) in map { length += field(key.len()) + field(value.len()); }
    }
    length += field(8); for capability in expected.capability_manifest.iter() { length += field(capability.len()); }
    length += field(1);
    if let Some(manifest) = &expected.runtime_manifest {
        length += field(manifest.standard_library.0.len()) + field(8);
        for selector in &manifest.selectors { length += field(1) + field(selector.module_path.len()) + field(selector.name.len()); }
        length += field(8);
        for host in &manifest.host_imports { length += field(host.module_path.len()) + field(host.name.len()) + field(host.capability.len()) + field(host.symbol.len()); }
    }
    let mut generated = world_request_witness(&sample, "sample");
    generated.push_str(&format!("fn transcript_bytes() -> usize {{ {length} }}\nfn expected_fingerprint() -> identity::Digest {{ digest(b\"{}\") }}\n", expected.fingerprint.as_bytes().iter().map(|byte| format!("\\x{byte:02x}")).collect::<String>()));
    let case = "request/world_lifecycle.glorious";
    let program = source_program(case, &[("@SUPPORT@", world_fixture_support()), ("@SAMPLE@", generated)]);
    let (results, profile) = program.run_tuple_i64_for_authoring(Default::default()).unwrap();
    record_execution_values(case, &program, "", &format!("{results:?}"), Some(&profile));
    assert_eq!(results, [1, 14, 3, 3, 5, 4]);
}

#[test]
fn gsc2_request_world_cross_component_failures_match_reference_fields_and_order() {
    use grandiose_stage0::{BootstrapLimits, BootstrapStage, FileKey, InputError, ScalarType};
    use grandiose_stage0::runtime_manifest::{FloatPrimitive, HostImportSelector, PrimitiveRole, PrimitiveSelector, RuntimeManifestInput};
    fn literal(value: &[u8]) -> String { format!("b\"{}\"", value.iter().map(|byte| format!("\\x{byte:02x}")).collect::<String>()) }
    fn text(value: &str) -> String { format!("text({})", literal(value.as_bytes())) }
    fn digest(value: Digest) -> String { format!("digest({})", literal(&value.as_bytes())) }
    fn file(value: FileKey) -> String { format!("identity::FileKey {{ digest: {} }}", digest(value.0)) }
    fn package(value: &PackageKey) -> String { format!("identity::PackageKey {{ value: {} }}", text(&value.0)) }
    fn error(value: &InputError) -> String {
        let variant = match value {
            InputError::EmptySources => "EmptySources".into(),
            InputError::DuplicateFileKey(value) => format!("DuplicateFileKey({})", file(*value)),
            InputError::SourceIdentityMismatch { supplied, expected } => format!("SourceIdentityMismatch {{ supplied: {}, expected: {} }}", file(*supplied), file(*expected)),
            InputError::DigestMismatch { file: key, expected, actual } => format!("DigestMismatch {{ file: {}, expected: {}, actual: {} }}", file(*key), digest(*expected), digest(*actual)),
            InputError::InvalidUtf8(value) => format!("InvalidUtf8({})", file(*value)),
            InputError::InvalidPackageModuleAlias(value) => format!("InvalidPackageModuleAlias({})", package(value)),
            InputError::DuplicatePackageModuleAlias { alias, first, second } => format!("DuplicatePackageModuleAlias {{ alias: {}, first: {}, second: {} }}", text(alias), package(first), package(second)),
            InputError::InvalidCapability(value) => format!("InvalidCapability({})", text(value)),
            InputError::DuplicateCapability(value) => format!("DuplicateCapability({})", text(value)),
            InputError::InvalidRuntimeManifest => "InvalidRuntimeManifest".into(),
            InputError::InvalidBootstrapStage { reason } => format!("InvalidBootstrapStage {{ reason: {} }}", text(reason)),
            InputError::BootstrapSourceLimit { actual, limit } => format!("BootstrapSourceLimit {{ actual: {actual}, limit: {limit} }}"),
            InputError::InvalidLogicalPath(_) => panic!("logical path validation is a separate sealed constructor"),
        };
        format!("request::InputError::{variant}")
    }
    let base = world_request_reference_cases(0).remove(0);
    let stage = BootstrapStage { ordinal: 0, producer: base.build.compiler, optimization_level: 2,
        limits: BootstrapLimits { max_sources: 10, max_total_source_bytes: 10000 }, expected_artifact: None };
    let selector = PrimitiveSelector { role: PrimitiveRole::Abort, module_path: "std".into(), name: "abort".into() };
    let bad_runtime = RuntimeManifestInput { standard_library: PackageKey("std".into()), selectors: vec![selector.clone(), selector], host_imports: vec![] };
    let mut bad_tail = base.clone(); bad_tail.mode = CompilationMode::Bootstrap(stage.clone()); bad_tail.runtime_manifest = Some(bad_runtime.clone());
    bad_tail.capability_manifest = vec!["*".into()]; bad_tail.root_package = PackageKey("9invalid".into());
    let mut cases = vec![];
    let mut value = bad_tail.clone(); value.sources.clear(); cases.push(value);
    for (bad_key, bad_digest, invalid_utf8) in [(true, true, true), (false, true, true), (false, false, true)] {
        let mut value = bad_tail.clone();
        if invalid_utf8 { value.sources[0] = SourceInput::new(base.root_package.clone(), LogicalPath::parse("src/main.glorious").unwrap(), b"\xff".as_slice()); }
        if bad_key { value.sources[0].key = FileKey(Digest::of_bytes(b"wrong-key")); }
        if bad_digest { value.sources[0].digest = Digest::of_bytes(b"wrong-digest"); }
        cases.push(value);
    }
    let mut value = bad_tail.clone(); value.sources.push(value.sources[0].clone()); cases.push(value.clone());
    value.sources[1].digest = Digest::of_bytes(b"bad-duplicate-digest"); cases.push(value);
    let mut value = bad_tail.clone();
    let mut z = SourceInput::new(PackageKey("z@1".into()), LogicalPath::parse("src/lib.glorious").unwrap(), b"z".as_slice()); z.key = FileKey(Digest::of_bytes(b"bad-z-key"));
    let a = SourceInput::new(base.root_package.clone(), LogicalPath::parse("src/main.glorious").unwrap(), b"\xff".as_slice());
    value.sources = vec![z, a]; cases.push(value.clone()); value.sources.reverse(); cases.push(value);
    cases.push(bad_tail.clone());
    let mut value = bad_tail.clone(); value.root_package = PackageKey("math_lib@2".into());
    value.sources = vec![SourceInput::new(PackageKey("math-lib@1".into()), LogicalPath::parse("src/lib.glorious").unwrap(), b"library".as_slice())]; cases.push(value);
    let mut value = bad_tail.clone(); value.root_package = base.root_package.clone();
    for caps in [vec!["*"], vec!["a", "a"], vec!["a", "a", "z*"], vec!["a", "\u{2003}"]] {
        value.capability_manifest = caps.into_iter().map(str::to_owned).collect(); cases.push(value.clone());
    }
    value.capability_manifest = base.capability_manifest.clone(); cases.push(value.clone());
    value.runtime_manifest = Some(RuntimeManifestInput { standard_library: PackageKey("std".into()), selectors: vec![PrimitiveSelector {
        role: PrimitiveRole::Float(FloatPrimitive::Convert { from: ScalarType::F32, to: ScalarType::F32, checked: false }), module_path: "std".into(), name: "bad".into() }], host_imports: vec![] }); cases.push(value.clone());
    value.runtime_manifest = Some(RuntimeManifestInput { standard_library: PackageKey("std".into()), selectors: vec![], host_imports: vec![HostImportSelector {
        module_path: "m".into(), name: "n".into(), capability: "*".into(), symbol: "s".into() }] }); cases.push(value);
    for change in 0..10 {
        let mut value = base.clone(); let mut stage = stage.clone(); stage.ordinal = 1;
        match change {
            0 => stage.ordinal = 0,
            1 => stage.optimization_level = 4,
            2 => stage.limits.max_sources = 0,
            3 => stage.producer = Digest::of_bytes(b"wrong-producer"),
            4 => stage.expected_artifact = Some(stage.producer),
            5 => stage.ordinal = 2,
            6 => { stage.ordinal = 2; stage.expected_artifact = Some(Digest::of_bytes(b"wrong-predecessor")); }
            7 => { stage.limits.max_sources = 1; let mut extra = value.sources[0].clone(); extra = SourceInput::new(extra.package, LogicalPath::parse("src/extra.glorious").unwrap(), b"extra".as_slice()); value.sources.push(extra); }
            8 => stage.limits.max_total_source_bytes = 3,
            _ => { value.codegen_options.insert("optimization-level".into(), "02".into()); }
        }
        value.mode = CompilationMode::Bootstrap(stage); cases.push(value);
    }
    let mut generated = String::new();
    for (index, value) in cases.iter().enumerate() {
        let expected = value.clone().normalize().unwrap_err();
        generated.push_str(&world_request_witness(value, &format!("input_{index}")));
        generated.push_str(&format!("fn case_{index}() -> i64 {{ reject(input_{index}(), {}) }}\n", error(&expected)));
    }
    generated.push_str(&format!("fn oracles() -> i64 {{ {} }}\n", (0..cases.len()).map(|index| format!("case_{index}()")).collect::<Vec<_>>().join(" + ")));
    let case = "request/world_failures.glorious";
    let program = source_program(case, &[("@SUPPORT@", world_fixture_support()), ("@CASES@", generated)]);
    let (result, profile) = program.run_i64_for_authoring(Default::default()).unwrap();
    record_execution(case, &program, result, Some(&profile));
    assert_eq!(result, cases.len() as i64);
}

#[test]
fn gsc2_request_runtime_manifest_matches_authority_and_host_input_canonicalization() {
    use grandiose_stage0::runtime_manifest::{FloatPrimitive, HostImportSelector, ManifestError, PrimitiveRole, PrimitiveSelector, RuntimeManifestInput};
    use grandiose_stage0::ScalarType;
    fn literal(bytes: &[u8]) -> String {
        format!("b\"{}\"", bytes.iter().map(|byte| format!("\\x{byte:02x}")).collect::<String>())
    }
    fn text(value: &str) -> String { format!("text({})", literal(value.as_bytes())) }
    fn role(value: PrimitiveRole) -> String {
        let inner = match value {
            PrimitiveRole::Float(FloatPrimitive::Binary { width, operation }) => format!("Binary {{ width: FloatWidth::{width:?}, operation: FloatBinaryOp::{operation:?} }}"),
            PrimitiveRole::Float(FloatPrimitive::Neg { width }) => format!("Neg {{ width: FloatWidth::{width:?} }}"),
            PrimitiveRole::Float(FloatPrimitive::Compare { width, operation }) => format!("Compare {{ width: FloatWidth::{width:?}, operation: FloatCompareOp::{operation:?} }}"),
            PrimitiveRole::Float(FloatPrimitive::Convert { from, to, checked }) => format!("Convert {{ from: ScalarType::{from:?}, to: ScalarType::{to:?}, checked: {checked} }}"),
            PrimitiveRole::Float(FloatPrimitive::ToBits { width }) => format!("ToBits {{ width: FloatWidth::{width:?} }}"),
            PrimitiveRole::Float(FloatPrimitive::FromBits { width }) => format!("FromBits {{ width: FloatWidth::{width:?} }}"),
            other => return format!("PrimitiveRole::{other:?}"),
        };
        format!("PrimitiveRole::Float(FloatPrimitive::{inner})")
    }
    fn selector(value: PrimitiveRole, module: &str, name: &str) -> PrimitiveSelector {
        PrimitiveSelector { role: value, module_path: module.into(), name: name.into() }
    }
    fn host(module: &str, name: &str, capability: &str, symbol: &str) -> HostImportSelector {
        HostImportSelector { module_path: module.into(), name: name.into(), capability: capability.into(), symbol: symbol.into() }
    }
    fn manifest(selectors: Vec<PrimitiveSelector>, host_imports: Vec<HostImportSelector>) -> RuntimeManifestInput {
        RuntimeManifestInput { standard_library: PackageKey("std@0.1.0".into()), selectors, host_imports }
    }
    fn emit(value: &RuntimeManifestInput, binding: &str) -> String {
        let mut result = format!("let {binding} = empty(); {binding}.standard_library = PackageKey {{ value: {} }};\n", text(&value.standard_library.0));
        for selector in &value.selectors {
            result.push_str(&format!("Vec::push(&mut {binding}.selectors, PrimitiveSelector {{ role: {}, module_path: {}, name: {} }});\n",
                role(selector.role), text(&selector.module_path), text(&selector.name)));
        }
        for host in &value.host_imports {
            result.push_str(&format!("Vec::push(&mut {binding}.host_imports, HostImportSelector {{ module_path: {}, name: {}, capability: {}, symbol: {} }});\n",
                text(&host.module_path), text(&host.name), text(&host.capability), text(&host.symbol)));
        }
        result
    }
    let base = [selector(PrimitiveRole::BranchBool, "crate", "branch"),
        selector(PrimitiveRole::Abort, "crate", "abort"),
        selector(PrimitiveRole::parse_selector_name("f32-add").unwrap(), "crate", "add")];
    let hosts = [host("m", "b", "read", "symbol-b"), host("a", "z", "write", "symbol-a"), host("m", "a", "read", "symbol-c")];
    let mut cases = Vec::new();
    for indices in [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]] {
        cases.push(manifest(indices.map(|i| base[i].clone()).to_vec(), indices.map(|i| hosts[i].clone()).to_vec()));
    }
    cases.push(manifest(vec![], vec![]));
    cases.push(manifest(vec![selector(PrimitiveRole::Abort, "", "")], vec![]));
    // Standard-library identity is retained verbatim here. Package validation
    // belongs to request admission; manifest canonicalization does not invent it.
    for package in ["", "other@2", "a\0💜"] {
        let mut input = manifest(base.to_vec(), vec![]); input.standard_library = PackageKey(package.into()); cases.push(input);
    }
    cases.push(manifest(vec![base[0].clone(), base[0].clone()], vec![]));
    cases.push(manifest(vec![base[0].clone(), selector(base[0].role, "other", "different")], vec![]));
    cases.push(manifest(vec![base[0].clone(), base[0].clone(), base[1].clone(), base[1].clone()], vec![]));
    for (from, to, checked) in [(ScalarType::F32, ScalarType::F32, false), (ScalarType::F32, ScalarType::F64, true),
        (ScalarType::Bool, ScalarType::F32, false), (ScalarType::F32, ScalarType::I64, false), (ScalarType::I64, ScalarType::F32, true)] {
        let invalid = selector(PrimitiveRole::Float(FloatPrimitive::Convert { from, to, checked }), "bad", "leaf");
        cases.push(manifest(vec![base[1].clone(), base[1].clone(), invalid.clone()], vec![host("", "", "*", "")]));
        cases.push(manifest(vec![invalid.clone(), invalid], vec![]));
    }
    for field in 0..4 {
        let mut input = host("m", "n", "read", "symbol");
        match field { 0 => input.module_path.clear(), 1 => input.name.clear(), 2 => input.capability.clear(), _ => input.symbol.clear() }
        cases.push(manifest(vec![], vec![input]));
    }
    let whitespace = ['\u{0009}', '\u{000a}', '\u{000b}', '\u{000c}', '\u{000d}', '\u{0020}', '\u{0085}', '\u{00a0}', '\u{1680}',
        '\u{2000}', '\u{2001}', '\u{2002}', '\u{2003}', '\u{2004}', '\u{2005}', '\u{2006}', '\u{2007}', '\u{2008}', '\u{2009}', '\u{200a}',
        '\u{2028}', '\u{2029}', '\u{202f}', '\u{205f}', '\u{3000}'];
    for character in whitespace { assert!(character.is_whitespace()); cases.push(manifest(vec![], vec![host("m", "n", &format!("r{character}w"), "s")])); }
    for capability in ["*", "r*w", "\0", "é", "e\u{301}", "\u{200b}", "\u{feff}", "\u{001c}", "read:💜"] {
        cases.push(manifest(vec![], vec![host("m", "n", capability, "s")]));
    }
    cases.push(manifest(vec![], vec![host("m", "n", "r", "s"), host("m", "n", "w", "different")]));
    cases.push(manifest(vec![], vec![host("a", "a", "r", "s"), host("a", "a", "r", "s"), host("z", "z", "*", "s")]));
    cases.push(manifest(vec![], vec![host("z", "z", "*", "s"), host("a", "a", "", "s")]));
    cases.push(manifest(vec![base[0].clone(), base[0].clone()], vec![host("", "", "", "")]));
    cases.push(manifest(vec![], ["b", "a", "", "猫"].map(|suffix| host(&("x".repeat(80) + suffix), "n", "r", "s")).to_vec()));
    cases.push(manifest(vec![], (0..24).rev().map(|i| host("m", &format!("n{i:02}"), "r", "s")).collect()));
    cases.push(manifest(vec![], vec![host("\0", "a b", "r", "s*\n"), host("猫", "e\u{301}", "w", "💜")]));
    let mut generated = String::new();
    for (index, input) in cases.iter().enumerate() {
        let mut canonical = input.clone();
        let (kind, rejected_role, a, b) = match canonical.canonicalize() {
            Ok(()) => (0, PrimitiveRole::Abort, String::new(), String::new()),
            Err(ManifestError::InvalidRole(role)) => (1, role, String::new(), String::new()),
            Err(ManifestError::DuplicateRole(role)) => (2, role, String::new(), String::new()),
            Err(ManifestError::InvalidHostImport { module_path, name }) => (3, PrimitiveRole::Abort, module_path, name),
            Err(ManifestError::DuplicateHostImport { module_path, name }) => (4, PrimitiveRole::Abort, module_path, name),
            other => panic!("unexpected manifest oracle: {other:?}"),
        };
        if kind != 0 { canonical = manifest(vec![], vec![]); }
        generated.push_str(&format!("fn oracle_{index}() -> i64 {{ {} {} check(actual, Expected {{ kind: {kind}, role: {}, a: {}, b: {}, value: wanted }}) }}\n",
            emit(input, "actual"), emit(&canonical, "wanted"), role(rejected_role), text(&a), text(&b)));
    }
    generated.push_str(&format!("fn oracles() -> i64 {{ {} }}\n", (0..cases.len()).map(|i| format!("oracle_{i}()")).collect::<Vec<_>>().join(" + ")));
    let mut inventory = BTreeMap::new();
    for line in include_str!("../../../compiler/spec/runtime-authority.tsv").lines().skip(1) {
        let (name, tag) = line.split_once('\t').unwrap();
        let value = PrimitiveRole::parse_selector_name(name).unwrap();
        assert_eq!(value.selector_name(), name);
        assert!(inventory.insert(value, (name, tag.parse::<u8>().unwrap())).is_none());
    }
    assert_eq!(inventory.len(), 183);
    let mut metadata = String::new();
    let mut previous = *inventory.first_key_value().unwrap().0;
    let mut checks = Vec::new();
    for (index, (&value, &(name, tag))) in inventory.iter().enumerate() {
        checks.push(format!("role_case({}, {}, {}, {}, {tag})", role(value), role(previous), index == 0, literal(name.as_bytes())));
        previous = value;
    }
    for (i, chunk) in checks.chunks(12).enumerate() { metadata.push_str(&format!("fn role_chunk_{i}() -> i64 {{ {} }}\n", chunk.join(" + "))); }
    metadata.push_str(&format!("fn roles() -> i64 {{ {} }}\n", (0..checks.chunks(12).len()).map(|i| format!("role_chunk_{i}()")).collect::<Vec<_>>().join(" + ")));
    let scalars = [ScalarType::Bool, ScalarType::U8, ScalarType::U16, ScalarType::U32, ScalarType::U64, ScalarType::U128,
        ScalarType::I8, ScalarType::I16, ScalarType::I32, ScalarType::I64, ScalarType::I128, ScalarType::Usize, ScalarType::Isize,
        ScalarType::F32, ScalarType::F64, ScalarType::Char, ScalarType::Text, ScalarType::Bytes];
    let mut conversions = Vec::new();
    for from in scalars { for to in scalars { for checked in [false, true] {
        let value = PrimitiveRole::Float(FloatPrimitive::Convert { from, to, checked });
        let mut input = manifest(vec![selector(value, "m", "n")], vec![]);
        conversions.push(match input.canonicalize() {
            Ok(()) => inventory[&value].1.checked_add(1).unwrap(),
            Err(error) => { assert_eq!(error, ManifestError::InvalidRole(value)); 0 }
        });
    } } }
    assert_eq!(conversions.len(), 648);
    assert_eq!(conversions.iter().filter(|&&tag| tag != 0).count(), 50);
    let case = "request/runtime_manifest.glorious";
    let program = source_program(case, &[("@CASES@", generated), ("@ROLES@", metadata), ("@CONVERSIONS@", literal(&conversions))]);
    let (results, profile) = program.run_tuple_i64_for_authoring(Default::default()).unwrap();
    record_execution_values(case, &program, "", &format!("{results:?}"), Some(&profile));
    assert_eq!(results, [cases.len() as i64, 183, 648, 1, 20]);
}

#[test]
fn gsc2_request_source_collection_matches_reference_ordering_and_rejection_precedence() {
    use grandiose_stage0::{FileKey, InputError};
    fn literal(bytes: &[u8]) -> String {
        format!("b\"{}\"", bytes.iter().map(|byte| format!("\\x{byte:02x}")).collect::<String>())
    }
    fn witness(source: &SourceInput) -> String {
        format!("Witness {{ package: owned({}), path: owned({}), bytes: owned({}), key: owned({}), digest: owned({}) }}",
            literal(source.package.0.as_bytes()), literal(source.logical_path.as_str().as_bytes()),
            literal(&source.bytes), literal(&source.key.0.as_bytes()), literal(&source.digest.as_bytes()))
    }
    fn source(package: &str, path: &str, bytes: &[u8]) -> SourceInput {
        SourceInput::new(PackageKey(package.into()), LogicalPath::parse(path).unwrap(), bytes)
    }
    let a = source("p", "a", b"a");
    let b = source("p", "b", "é".as_bytes());
    let c = source("q", "a", b"");
    let mut cases = Vec::new();
    let canonical = [a.clone(), b.clone(), c.clone()];
    for order in [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]] {
        cases.push(order.iter().map(|&index| canonical[index].clone()).collect::<Vec<_>>());
    }
    cases.push(vec![]);
    cases.push(vec![a.clone()]);
    cases.push(vec![a.clone(), a.clone()]);
    cases.push(vec![source("p", "a", b"different"), a.clone()]);
    let mut bad_digest = a.clone();
    bad_digest.digest = Digest::of_bytes(b"forged-digest");
    let bad_utf8 = source("p", "a", b"\xff");
    cases.push(vec![bad_digest.clone(), bad_utf8.clone()]);
    cases.push(vec![bad_utf8.clone(), bad_digest.clone()]);
    let mut bad_b = b.clone();
    bad_b.digest = Digest::of_bytes(b"other-forged-digest");
    cases.push(vec![a.clone(), a.clone(), bad_b.clone()]);
    cases.push(vec![bad_b.clone(), bad_digest.clone()]);
    cases.push(vec![bad_digest.clone(), bad_b.clone()]);
    let mut bad_key = a.clone();
    bad_key.key = FileKey(Digest::of_bytes(b"forged-key"));
    bad_key.digest = Digest::of_bytes(b"also-forged-digest");
    cases.push(vec![bad_key.clone(), bad_digest.clone()]);
    cases.push(vec![bad_digest, bad_key.clone()]);
    cases.push(vec![bad_key]);
    let mut bad_q = c;
    bad_q.key = FileKey(Digest::of_bytes(b"forged-q-key"));
    cases.push(vec![bad_q, bad_utf8]);
    cases.push(vec![source("p", "é/😀", b"unicode"), source("p", "a\0", b"nul"), a.clone()]);
    let mut generated = format!("fn witness_a() -> Witness {{ {} }}\nfn witness_b() -> Witness {{ {} }}\n", witness(&a), witness(&b));
    let mut roots = Vec::new();
    for (index, inputs) in cases.iter().enumerate() {
        let request = CompilationRequest {
            build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"source-collection-oracle")),
            mode: CompilationMode::Check, root_package: PackageKey("p".into()), sources: inputs.clone(),
            target: "stage0-vm".into(), semantic_options: BTreeMap::new(), codegen_options: BTreeMap::new(),
            capability_manifest: vec![], runtime_manifest: None,
        };
        generated.push_str(&format!("fn oracle_{index}() -> i64 {{ let inputs = Vec<request::SourceInput>::new(); let setup = as<i64>(1);\n"));
        for input in inputs { generated.push_str(&format!("setup = setup * push(&mut inputs, {});\n", witness(input))); }
        generated.push_str("let expected = Vec<Witness>::new();\n");
        let (kind, a, b, c) = match request.normalize() {
            Ok(world) => {
                for source in world.sources.iter() { generated.push_str(&format!("Vec::push(&mut expected, {});\n", witness(source))); }
                (0, vec![], vec![], vec![])
            }
            Err(InputError::EmptySources) => (1, vec![], vec![], vec![]),
            Err(InputError::DuplicateFileKey(key)) => (2, key.0.as_bytes().to_vec(), vec![], vec![]),
            Err(InputError::SourceIdentityMismatch { supplied, expected }) => (3, supplied.0.as_bytes().to_vec(), expected.0.as_bytes().to_vec(), vec![]),
            Err(InputError::DigestMismatch { file, expected, actual }) => (4, file.0.as_bytes().to_vec(), expected.as_bytes().to_vec(), actual.as_bytes().to_vec()),
            Err(InputError::InvalidUtf8(file)) => (5, file.0.as_bytes().to_vec(), vec![], vec![]),
            other => panic!("unexpected source collection result: {other:?}"),
        };
        generated.push_str(&format!("setup * check(inputs, Expected {{ kind: {kind}, a: {}, b: {}, c: {}, values: expected }}) }}\n", literal(&a), literal(&b), literal(&c)));
        roots.push(format!("oracle_{index}()"));
    }
    generated.push_str(&format!("fn oracle_cases() -> i64 {{ {} }}\n", roots.join(" + ")));
    let mut orders = String::from("fn order_cases() -> i64 { let score = as<i64>(0);\n");
    let mut order_count = 0;
    for count in [0_usize, 1, 2, 3, 5, 9, 17, 65] {
        for pattern in 0..4 {
            let values: Vec<u8> = (0..count).map(|index| match pattern {
                0 => index as u8, 1 => (count - index) as u8,
                2 => 3, _ => ((index * 13 + 7) % 11) as u8,
            }).collect();
            let mut indices: Vec<_> = (0..count).collect();
            indices.sort_by_key(|&index| values[index]);
            let expected: Vec<_> = indices.into_iter().map(|index| index as u8).collect();
            let levels = usize::BITS - count.max(1).leading_zeros();
            let bound = 12 * count * (levels as usize + 1) + 16;
            orders.push_str(&format!("score = score + order_case({}, {}, {bound});\n", literal(&values), literal(&expected)));
            order_count += 1;
        }
    }
    // The larger reversed case also runs under an explicit O(n log n)
    // scheduling-work ceiling; physical allocation/copy costs are separate.
    let large: Vec<u8> = (1..=255).rev().collect();
    let expected: Vec<u8> = (0..255).rev().collect();
    orders.push_str(&format!("score = score + order_case({}, {}, 9196);\nscore }}\n", literal(&large), literal(&expected)));
    order_count += 1;
    let case = "request/sources.glorious";
    let program = source_program(case, &[("@CASES@", generated), ("@ORDERS@", orders)]);
    let (results, profile) = program.run_tuple_i64_for_authoring(Default::default()).unwrap();
    record_execution_values(case, &program, "", &format!("{results:?}"), Some(&profile));
    assert_eq!(results, [cases.len() as i64, 238, order_count, 1, 21]);
}

#[test]
fn gsc2_request_bootstrap_admission_matches_reference_provenance_bounds_and_failure_order() {
    use grandiose_stage0::{BootstrapLimits, BootstrapStage, InputError};
    use std::collections::BTreeSet;
    #[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
    struct Case {
        ordinal: u32, level: u8, max_sources: u32, max_bytes: u64,
        producer: usize, expected: usize, option: Option<String>,
    }
    fn base(ordinal: u32) -> Case {
        Case { ordinal, level: 2, max_sources: 2, max_bytes: 4,
            producer: 0, expected: usize::from(ordinal != 1), option: Some("2".into()) }
    }
    fn corrupt(case: &mut Case, field: usize) {
        match field {
            0 => case.ordinal = 0,
            1 => case.level = 4,
            2 => case.max_sources = 0,
            3 => case.max_bytes = 0,
            4 => case.producer = 1,
            5 => case.expected = usize::from(case.ordinal == 1),
            6 => case.max_sources = 1,
            7 => case.max_bytes = 3,
            _ => case.option = Some("+2".into()),
        }
    }
    let mut cases = BTreeSet::new();
    for ordinal in [1, 2] {
        cases.insert(base(ordinal));
        // Every single corruption and every pair: the exact first rejection
        // is observed from real request normalization, not reimplemented here.
        for first in 0..9 {
            for second in first..9 {
                let mut case = base(ordinal);
                corrupt(&mut case, first);
                corrupt(&mut case, second);
                cases.insert(case);
            }
        }
    }
    for ordinal in [1, 2, u32::MAX] {
        for level in 0..=3 {
            for (max_sources, max_bytes) in [(2, 4), (u32::MAX, u64::MAX)] {
                for option in [None, Some(level.to_string())] {
                    cases.insert(Case { ordinal, level, max_sources, max_bytes, option, ..base(ordinal) });
                }
            }
        }
    }
    for option in ["", "0", "1", "3", "9", "02", "+2", " 2", "2 ", "\t2", "２", "2\0"] {
        cases.insert(Case { option: Some(option.into()), ..base(2) });
    }
    cases.insert(Case { expected: 2, ..base(2) });
    cases.insert(Case { level: u8::MAX, ..base(2) });
    let good = Digest::of_bytes(b"bootstrap-admission-producer");
    let bad = Digest::of_bytes(b"wrong-bootstrap-producer");
    let build = CompilerBuildIdentity::stage0(good);
    let package = PackageKey("app".into());
    let sources = vec![
        SourceInput::new(package.clone(), LogicalPath::parse("src/a.glorious").unwrap(), b"a\n".as_slice()),
        SourceInput::new(package.clone(), LogicalPath::parse("src/b.glorious").unwrap(), "é".as_bytes()),
    ];
    let mut calls = Vec::new();
    for case in &cases {
        let stage = BootstrapStage {
            ordinal: case.ordinal, producer: if case.producer == 0 { good } else { bad },
            optimization_level: case.level,
            limits: BootstrapLimits::new(case.max_sources, case.max_bytes),
            expected_artifact: match case.expected { 0 => None, 1 => Some(good), _ => Some(bad) },
        };
        let request = CompilationRequest {
            build: build.clone(), mode: CompilationMode::Bootstrap(stage), root_package: package.clone(),
            sources: sources.clone(), target: "stage0-vm".into(), semantic_options: BTreeMap::new(),
            codegen_options: case.option.iter().map(|value| ("optimization-level".into(), value.clone())).collect(),
            capability_manifest: vec![], runtime_manifest: None,
        };
        let (kind, reason, actual, limit) = match request.normalize() {
            Ok(_) => (0, "", 0, 0),
            Err(InputError::InvalidBootstrapStage { reason }) => (1, reason, 0, 0),
            Err(InputError::BootstrapSourceLimit { actual, limit }) => (2, "", actual, limit),
            other => panic!("unexpected bootstrap oracle result for {case:?}: {other:?}"),
        };
        calls.push(format!(
            "score = score + run_case(Case {{ ordinal: {}, level: {}, max_sources: {}, max_bytes: {}, producer: {}, expected: {}, option: {:?}, has_option: {} }}, good, bad, {kind}, b{reason:?}, {actual}, {limit});\n",
            case.ordinal, case.level, case.max_sources, case.max_bytes, case.producer, case.expected,
            case.option.as_deref().unwrap_or(""), usize::from(case.option.is_some()),
        ));
    }
    let mut generated = String::new();
    let mut roots = Vec::new();
    for (index, chunk) in calls.chunks(12).enumerate() {
        generated.push_str(&format!("fn oracle_{index}(good: Digest, bad: Digest) -> i64 {{ let score = as<i64>(0);\n{}score\n}}\n", chunk.concat()));
        roots.push(format!("oracle_{index}(good, bad)"));
    }
    generated.push_str(&format!("fn oracle_cases(good: Digest, bad: Digest) -> i64 {{ {} }}\n", roots.join(" + ")));
    let case = "request/bootstrap.glorious";
    let program = source_program(case, &[
        ("@CASES@", generated),
        ("@LANGUAGE@", build.language_generation.to_string()), ("@QUERY@", build.query_generation.to_string()),
        ("@INTERFACE@", build.interface_generation.to_string()), ("@CACHE@", build.cache_generation.to_string()),
        ("@BYTECODE@", build.bytecode_generation.to_string()), ("@VERIFIER@", build.verifier_generation.to_string()),
    ]);
    let (results, profile) = program.run_tuple_i64_for_authoring(Default::default()).unwrap();
    record_execution_values(case, &program, "", &format!("{results:?}"), Some(&profile));
    // 14 cancel histories x3 checks, six early finishes x2, seven exhausted phases x3,
    // abort x2, successful one-shot finish x3; all six mode tags + seven build fields.
    assert_eq!(results, [cases.len() as i64, 80, 13]);
}

#[test]
fn gsc2_request_name_admission_matches_reference_aliases_and_unicode_capabilities() {
    use grandiose_stage0::InputError;
    use std::{collections::BTreeSet, fmt::Write};
    fn escaped(bytes: &[u8]) -> String {
        bytes.iter().map(|byte| format!("\\x{byte:02x}")).collect()
    }
    fn grouped(name: &str, calls: &[String]) -> String {
        let mut result = String::new();
        for (index, chunk) in calls.chunks(20).enumerate() {
            writeln!(
                result,
                "fn {name}_{index}() -> i64 {{ let score = as<i64>(0);"
            )
            .unwrap();
            for call in chunk {
                result.push_str(call);
            }
            result.push_str("score\n}\n");
        }
        writeln!(result, "fn {name}() -> i64 {{ let score = as<i64>(0);").unwrap();
        for index in 0..calls.len().div_ceil(20) {
            writeln!(result, "score = score + {name}_{index}();").unwrap();
        }
        result.push_str("score\n}\n");
        result
    }
    let mut aliases = BTreeSet::new();
    for value in [
        "",
        "-",
        "_",
        "@",
        "-@?",
        "app",
        "app@0.1.0",
        "a-b_c@version@more",
        "lib@invalid♥",
        "math-lib",
        "math_lib",
        "9lives",
        "a/b",
        "a.b",
        "é",
        "app-é",
        "app@é",
        "a\0b",
        "a@\0",
        "app@ white space",
        "app space@version",
    ] {
        aliases.insert(value.to_owned());
    }
    for byte in 0_u8..=127 {
        aliases.insert(format!("{}@version", char::from(byte)));
        aliases.insert(format!("a{}@version", char::from(byte)));
    }
    let alias_calls = aliases
        .iter()
        .map(|value| {
            let alias =
                grandiose_stage0::identity::package_module_alias(&PackageKey(value.clone()));
            format!(
                "score = score + alias_case(b\"{}\", b\"{}\", {});\n",
                escaped(value.as_bytes()),
                escaped(alias.as_deref().unwrap_or("").as_bytes()),
                i64::from(alias.is_none())
            )
        })
        .collect::<Vec<_>>();

    let mut scalars = (0..=127).collect::<BTreeSet<u32>>();
    let whitespace = (0..=0x10ffff)
        .filter_map(char::from_u32)
        .filter(|c| c.is_whitespace())
        .collect::<Vec<_>>();
    assert_eq!(
        whitespace.len(),
        25,
        "review the source Unicode table if the oracle changes"
    );
    for character in whitespace {
        let scalar = u32::from(character);
        scalars.extend([scalar - 1, scalar, scalar + 1]);
    }
    scalars.extend([
        0x180e, 0x200b, 0x200c, 0x200d, 0x2060, 0xfeff, 0x1f600, 0x10ffff,
    ]);
    let mut capabilities = BTreeSet::new();
    for value in [
        "", "*", "fs.*", "fs.read", "fs/read", "fs:read", "fs\\read", "µ.读", "a\0b",
    ] {
        capabilities.insert(value.to_owned());
    }
    for scalar in scalars {
        if let Some(character) = char::from_u32(scalar) {
            capabilities.insert(character.to_string());
            capabilities.insert(format!("fs{character}read"));
        }
    }
    let capability_calls = capabilities
        .iter()
        .map(|value| {
            let package = PackageKey("app".into());
            let request = CompilationRequest {
                build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"capability-oracle")),
                mode: CompilationMode::Check,
                root_package: package.clone(),
                sources: vec![SourceInput::new(
                    package,
                    LogicalPath::parse("src/main.glorious").unwrap(),
                    b"".as_slice(),
                )],
                target: "stage0-vm".into(),
                semantic_options: BTreeMap::new(),
                codegen_options: BTreeMap::new(),
                capability_manifest: vec![value.clone()],
                runtime_manifest: None,
            };
            let rejected = match request.normalize() {
                Ok(_) => 0,
                Err(InputError::InvalidCapability(found)) => {
                    assert_eq!(&found, value);
                    1
                }
                other => panic!("unexpected capability oracle result: {other:?}"),
            };
            format!(
                "score = score + capability_case(b\"{}\", {rejected});\n",
                escaped(value.as_bytes())
            )
        })
        .collect::<Vec<_>>();
    let cases =
        grouped("alias_cases", &alias_calls) + &grouped("capability_cases", &capability_calls);
    let case = "request/names.glorious";
    let program = source_program(case, &[("@CASES@", cases)]);
    let (results, profile) = program
        .run_tuple_i64_for_authoring(Default::default())
        .unwrap();
    record_execution_values(case, &program, "", &format!("{results:?}"), Some(&profile));
    assert_eq!(
        results,
        [aliases.len() as i64, capabilities.len() as i64, 100]
    );
}

#[test]
fn gsc2_database_executes_memoizes_and_checks_cancel_before_hits() {
    assert_eq!(source_case("engine/database.glorious"), 42);
}

#[test]
fn gsc2_database_distinguishes_waiting_from_cycles_and_recovers_failed_owners() {
    assert_eq!(source_case("engine/waiting.glorious"), 42);
}

#[test]
fn gsc2_database_replays_nested_reads_and_retires_shared_products() {
    assert_eq!(source_case("engine/reuse.glorious"), 42);
}

#[test]
fn gsc2_database_preserves_committed_children_and_enforces_transitive_recovery() {
    assert_eq!(source_case("engine/recovery.glorious"), 42);
}

#[test]
fn gsc2_database_stops_changed_branches_and_rejects_forged_reuse() {
    assert_eq!(source_case("engine/branch.glorious"), 42);
}

#[test]
fn gsc2_blake3_crosses_the_canonical_library_binding() {
    let expected = u64::from_le_bytes(Digest::of_bytes(b"abc").as_bytes()[..8].try_into().unwrap());
    assert_eq!(expected, 3697813978277427044);
    assert_eq!(source_case("runtime/digest.glorious"), 42);
}

#[test]
fn gsc2_state_loop_does_not_grow_the_call_stack() {
    let limits = grandiose_stage0::VmExecutionLimits {
        max_call_depth: 64,
        ..Default::default()
    };
    let program = source_program(
        "runtime/state_loop.glorious",
        &[("@STEPS@", "10000".into())],
    );
    assert!(matches!(
        program.run_i64_with_limits(limits),
        Err(grandiose_stage0::VmArtifactError::CallDepthLimit { limit: 64 })
    ));
    let (value, profile) = program.run_i64_for_authoring(limits).unwrap();
    assert_eq!(value, 10000);
    assert_eq!(profile.recycled_tail_calls, 10000);
    assert!(profile.peak_call_depth < 64);
    record_execution("runtime/state_loop_10000", &program, value, Some(&profile));
    let small = source_program("runtime/state_loop.glorious", &[("@STEPS@", "1000".into())]);
    let (value, small_profile) = small.run_i64_for_authoring(limits).unwrap();
    assert_eq!(value, 1000);
    assert_eq!(small_profile.peak_call_depth, profile.peak_call_depth);
    assert!(profile.work_ticks < 11 * small_profile.work_ticks);
    assert!(profile.charged_allocation_elements < 11 * small_profile.charged_allocation_elements);
    record_execution(
        "runtime/state_loop_1000",
        &small,
        value,
        Some(&small_profile),
    );
    eprintln!("state-loop authoring profile: {profile:?}");
}

#[test]
fn gsc2_borrowed_state_loop_preserves_owners_without_growing_the_call_stack() {
    let limits = grandiose_stage0::VmExecutionLimits {
        max_call_depth: 64,
        ..Default::default()
    };
    let program = source_program(
        "runtime/borrowed_loop.glorious",
        &[("@STEPS@", "10000".into())],
    );
    assert!(matches!(
        program.run_i64_with_limits(limits),
        Err(grandiose_stage0::VmArtifactError::CallDepthLimit { limit: 64 })
    ));
    let (value, profile) = program.run_i64_for_authoring(limits).unwrap();
    assert_eq!(
        value, 10000,
        "the caller must observe mutation of its actual state"
    );
    assert_eq!(profile.recycled_tail_calls, 10000);
    assert!(profile.peak_call_depth < 64);
    record_execution(
        "runtime/borrowed_loop_10000",
        &program,
        value,
        Some(&profile),
    );
    assert!(matches!(
        program.run_i64_for_authoring(grandiose_stage0::VmExecutionLimits {
            max_instructions: 100,
            ..limits
        }),
        Err(grandiose_stage0::VmArtifactError::InstructionLimit { limit: 100 })
    ));
    assert!(matches!(
        program.run_i64_for_authoring(grandiose_stage0::VmExecutionLimits {
            max_allocation_elements: 1024,
            ..limits
        }),
        Err(grandiose_stage0::VmArtifactError::AllocationLimit { limit: 1024 })
    ));
    let small = source_program(
        "runtime/borrowed_loop.glorious",
        &[("@STEPS@", "1000".into())],
    );
    let (value, small_profile) = small.run_i64_for_authoring(limits).unwrap();
    assert_eq!(value, 1000);
    assert_eq!(small_profile.peak_call_depth, profile.peak_call_depth);
    assert!(profile.work_ticks < 11 * small_profile.work_ticks);
    assert!(profile.charged_allocation_elements < 11 * small_profile.charged_allocation_elements);
    record_execution(
        "runtime/borrowed_loop_1000",
        &small,
        value,
        Some(&small_profile),
    );
    eprintln!("borrowed-loop authoring profile: {profile:?}");
}

#[test]
fn gsc2_borrowed_tail_return_preserves_the_unique_loan() {
    let program = source_program("runtime/borrowed_return.glorious", &[]);
    let limits = grandiose_stage0::VmExecutionLimits {
        max_call_depth: 64,
        ..Default::default()
    };
    assert!(matches!(
        program.run_i64_with_limits(limits),
        Err(grandiose_stage0::VmArtifactError::CallDepthLimit { limit: 64 })
    ));
    let (value, profile) = program.run_i64_for_authoring(limits).unwrap();
    assert_eq!(value, 42);
    assert_eq!(profile.recycled_tail_calls, 10000);
    assert!(profile.peak_call_depth < 64);
    record_execution(
        "runtime/borrowed_return.glorious",
        &program,
        value,
        Some(&profile),
    );
}

#[test]
fn gsc2_tail_calls_keep_frames_that_own_live_local_loans() {
    let program = source_program("runtime/local_loan_loop.glorious", &[]);
    let shallow = grandiose_stage0::VmExecutionLimits {
        max_call_depth: 64,
        ..Default::default()
    };
    assert!(matches!(
        program.run_i64_with_limits(shallow),
        Err(grandiose_stage0::VmArtifactError::CallDepthLimit { limit: 64 })
    ));
    assert!(matches!(
        program.run_i64_for_authoring(shallow),
        Err(grandiose_stage0::VmArtifactError::CallDepthLimit { limit: 64 })
    ));
    let deep = grandiose_stage0::VmExecutionLimits {
        max_call_depth: 256,
        ..shallow
    };
    assert_eq!(program.run_i64_with_limits(deep).unwrap(), 42);
    let (value, profile) = program.run_i64_for_authoring(deep).unwrap();
    assert_eq!(value, 42);
    assert_eq!(profile.recycled_tail_calls, 0);
    assert!(profile.peak_call_depth > 100);
    record_execution(
        "runtime/local_loan_loop.glorious",
        &program,
        value,
        Some(&profile),
    );
}
