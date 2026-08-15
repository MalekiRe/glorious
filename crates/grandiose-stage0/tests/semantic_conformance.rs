use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

use grandiose_stage0::{
    BodySyntax, CaptureMode, CompilationMode, CompilationRequest, CompileDiagnostic,
    CompilerBuildIdentity, CoreId, CoreKind, DeclarationScan, DefinitionIndex, DiagnosticClass,
    Digest, ElaboratedInterface, FileKey, InterfaceSet, LabelBrand, LexedFile, LogicalPath,
    PackageKey, SourceInput, StageZeroCompiler, TypedBody,
};

const CORE_SPEC: &str = include_str!("../../../glorious-branded-environment-core-spec.md");
const SEMANTIC_INVENTORY: &str =
    include_str!("../../../docs/self-hosted-compiler/stage0-semantic-inventory.tsv");

fn request(source: &str) -> CompilationRequest {
    CompilationRequest {
        build: CompilerBuildIdentity {
            compiler: Digest::of_bytes(b"semantic-conformance"),
            language_generation: 1,
            query_generation: 1,
            interface_generation: 1,
            cache_generation: 1,
            bytecode_generation: 1,
            verifier_generation: 1,
        },
        mode: CompilationMode::Build,
        root_package: PackageKey("semantic-conformance@0.1.0".into()),
        sources: vec![SourceInput::new(
            PackageKey("semantic-conformance@0.1.0".into()),
            LogicalPath::parse("src/main.glorious").unwrap(),
            source.as_bytes(),
        )],
        target: "stage0-vm".into(),
        semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::new(),
        capability_manifest: vec![],
        runtime_manifest: None,
    }
}

fn core_for(package_name: &str, source: &str) -> TypedBody {
    let package = PackageKey(package_name.into());
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    assert!(scan.diagnostics.is_empty(), "{scan:#?}");
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(
        &lexed,
        source,
        definition.body.expect("main must have a body"),
    );
    TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    )
}

fn rejection(source: &str) -> Vec<CompileDiagnostic> {
    StageZeroCompiler::new()
        .compile(request(source))
        .expect_err("the semantic rejection fixture unexpectedly compiled")
        .diagnostics()
        .to_vec()
}

fn published_diagnostic_text(diagnostic: &CompileDiagnostic) -> String {
    let mut text = diagnostic.message.clone();
    for related in &diagnostic.related {
        text.push(' ');
        text.push_str(&related.label);
    }
    for fact in &diagnostic.facts {
        text.push(' ');
        text.push_str(&fact.name);
        text.push(' ');
        text.push_str(&fact.value);
    }
    for frame in &diagnostic.explanation {
        text.push(' ');
        text.push_str(&frame.kind);
        text.push(' ');
        text.push_str(&frame.message);
    }
    text
}

fn assert_semantic_rejection(source: &str, rule: &str, required_terms: &[&[&str]]) {
    let diagnostics = rejection(source);
    let source_diagnostics = diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.class == DiagnosticClass::Source)
        .collect::<Vec<_>>();
    assert!(
        !source_diagnostics.is_empty(),
        "{rule}: rejection did not publish a source diagnostic: {diagnostics:#?}"
    );
    let text = source_diagnostics
        .iter()
        .map(|diagnostic| published_diagnostic_text(diagnostic).to_ascii_lowercase())
        .collect::<Vec<_>>()
        .join("\n");
    for alternatives in required_terms {
        assert!(
            alternatives
                .iter()
                .any(|term| text.contains(&term.to_ascii_lowercase())),
            "{rule}: diagnostic must explain one of {alternatives:?}: {diagnostics:#?}"
        );
    }
}

fn crate_path(relative: impl AsRef<Path>) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(relative)
}

fn spec_section(start: &str, end: &str) -> &'static str {
    let start = CORE_SPEC
        .find(start)
        .unwrap_or_else(|| panic!("missing normative section {start:?}"));
    let end = CORE_SPEC[start..]
        .find(end)
        .map(|offset| start + offset)
        .unwrap_or_else(|| panic!("missing normative section terminator {end:?}"));
    &CORE_SPEC[start..end]
}

#[derive(Debug)]
struct InventoryRow<'a> {
    id: &'a str,
    section: &'a str,
    requirement: &'a str,
    anchor: &'a str,
    state: &'a str,
}

fn inventory_rows() -> Vec<InventoryRow<'static>> {
    SEMANTIC_INVENTORY
        .lines()
        .filter(|line| !line.is_empty() && !line.starts_with('#') && !line.starts_with("rule_id\t"))
        .map(|line| {
            let columns = line.split('\t').collect::<Vec<_>>();
            assert_eq!(
                columns.len(),
                5,
                "semantic inventory rows must have exactly five TSV columns: {line:?}"
            );
            InventoryRow {
                id: columns[0],
                section: columns[1],
                requirement: columns[2],
                anchor: columns[3],
                state: columns[4],
            }
        })
        .collect()
}

fn anchor_test_source(anchor: &str) -> (PathBuf, String, String) {
    let (file, test) = anchor
        .split_once("::")
        .unwrap_or_else(|| panic!("invalid semantic anchor {anchor:?}"));
    let path = crate_path(Path::new("tests").join(file));
    let source = fs::read_to_string(&path).unwrap_or_else(|error| {
        panic!(
            "cannot read semantic anchor file {}: {error}",
            path.display()
        )
    });
    (path, source, test.to_owned())
}

#[test]
fn semantic_inventory_is_total_enabled_and_machine_checkable() {
    let safety = spec_section(
        "## 17. Safety invariants",
        "## 18. Required rejection examples",
    );
    for index in 1..=18 {
        assert!(
            safety
                .lines()
                .any(|line| line.starts_with(&format!("{index}. "))),
            "section 17 no longer contains safety invariant {index}"
        );
    }
    let rejections = spec_section(
        "## 18. Required rejection examples",
        "## 19. Conformance checklist",
    );
    assert_eq!(
        rejections
            .lines()
            .filter(|line| line.starts_with("### "))
            .count(),
        8,
        "section 18 rejection inventory changed"
    );
    let checklist = spec_section("## 19. Conformance checklist", "## 20. Compact formulation");
    assert_eq!(
        checklist
            .lines()
            .filter(|line| line.starts_with("- "))
            .count(),
        22,
        "section 19 conformance inventory changed"
    );

    let required = (1..=22)
        .map(|index| format!("C19-{index:02}"))
        .chain((1..=18).map(|index| format!("S17-{index:02}")))
        .chain((1..=8).map(|index| format!("R18-{index:02}")))
        .collect::<BTreeSet<_>>();
    let rows = inventory_rows();
    let observed = rows
        .iter()
        .map(|row| row.id.to_owned())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        observed, required,
        "the normative semantic rule set changed"
    );
    assert_eq!(
        rows.len(),
        observed.len(),
        "semantic inventory rule IDs must be unique"
    );

    for row in &rows {
        assert!(!row.section.is_empty(), "{} has no spec section", row.id);
        assert!(
            !row.requirement.is_empty(),
            "{} has no semantic requirement",
            row.id
        );
        assert!(
            matches!(row.state, "anchor" | "red"),
            "{} has an unknown state {:?}",
            row.id,
            row.state
        );
        for anchor in row.anchor.split(',') {
            let anchor = anchor.trim();
            let (path, source, test) = anchor_test_source(anchor);
            let needle = format!("fn {test}(");
            let offset = source.find(&needle).unwrap_or_else(|| {
                panic!(
                    "{} points at missing test {test:?} in {}",
                    row.id,
                    path.display()
                )
            });
            let mut attributes = Vec::new();
            for line in source[..offset].lines().rev() {
                let line = line.trim();
                if line.starts_with("#[") {
                    attributes.push(line);
                    continue;
                }
                if line.is_empty() && attributes.is_empty() {
                    continue;
                }
                break;
            }
            assert!(
                attributes.iter().any(|attribute| *attribute == "#[test]"),
                "{test} in {} has no #[test] attribute",
                path.display()
            );
            assert!(
                !attributes
                    .iter()
                    .any(|attribute| attribute.starts_with("#[ignore")),
                "{} maps to ignored test {anchor}",
                row.id
            );
        }
    }

    let mapped = rows
        .iter()
        .flat_map(|row| row.anchor.split(',').map(str::trim))
        .collect::<BTreeSet<_>>();
    for relative in [
        "semantic_conformance.rs",
        "semantic_conformance/surface.rs",
        "semantic_conformance/ownership.rs",
        "semantic_conformance/backend.rs",
    ] {
        let source = fs::read_to_string(crate_path(Path::new("tests").join(relative))).unwrap();
        for line in source.lines() {
            let line = line.trim_start();
            let Some(name) = line
                .strip_prefix("fn semantic_")
                .and_then(|tail| tail.split_once('(').map(|(name, _)| name))
            else {
                continue;
            };
            let full_name = format!("semantic_{name}");
            if full_name == "semantic_inventory_is_total_enabled_and_machine_checkable" {
                continue;
            }
            let anchor = format!("{relative}::{full_name}");
            assert!(
                mapped.contains(anchor.as_str()),
                "new conformance test {full_name} is not mapped to a normative rule"
            );
        }
    }
}

#[path = "semantic_conformance/backend.rs"]
mod backend;
#[path = "semantic_conformance/ownership.rs"]
mod ownership;
#[path = "semantic_conformance/surface.rs"]
mod surface;
