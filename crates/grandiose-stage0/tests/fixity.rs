use std::collections::BTreeMap;

use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, DeclarationScan, Digest, FileKey,
    FixityForm, FixityTable, HeaderParse, LexedFile, LogicalPath, PackageKey, ParsedHeader,
    ServiceError, SourceInput, StageZeroCompiler,
};

fn request(source: &str) -> CompilationRequest {
    CompilationRequest {
        build: CompilerBuildIdentity {
            compiler: Digest::of_bytes(b"fixity-tests"),
            language_generation: 1,
            query_generation: 1,
            interface_generation: 1,
            cache_generation: 1,
            bytecode_generation: 1,
            verifier_generation: 1,
        },
        mode: CompilationMode::Build,
        root_package: PackageKey("fixity@0.1.0".into()),
        sources: vec![SourceInput::new(
            PackageKey("fixity@0.1.0".into()),
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

fn interface(source: &str) -> grandiose_stage0::InterfaceSet {
    let package = PackageKey("fixity@0.1.0".into());
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    grandiose_stage0::InterfaceSet::collect(package, "crate", &lexed, source, &scan)
}

#[test]
fn fixity_headers_are_typed_interface_facts() {
    let source = "pub infixr 42 **;";
    let package = PackageKey("fixity@0.1.0".into());
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    assert!(scan.diagnostics.is_empty(), "{scan:#?}");
    assert_eq!(scan.declarations[0].name.as_deref(), Some("**"));
    let parsed = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert!(parsed.diagnostics.is_empty(), "{parsed:#?}");
    let ParsedHeader::Fixity(fixity) = parsed.header else {
        panic!("expected a fixity header");
    };
    assert_eq!(fixity.form, FixityForm::InfixRight);
    assert_eq!(fixity.precedence, 42);
    assert_eq!(fixity.operator, "**");
}

#[test]
fn source_fixity_changes_semantic_grouping_and_vm_result() {
    let source = "infixr 30 -; pub fn main() -> i64 { 10 - 3 - 2 }";
    let result = StageZeroCompiler::new()
        .compile(request(source))
        .unwrap()
        .artifact
        .unwrap()
        .run_i64()
        .unwrap();
    assert_eq!(result, 9, "right-associative subtraction is 10 - (3 - 2)");
}

#[test]
fn canonical_bare_callables_follow_fixities_without_desynchronizing_the_scanner() {
    let source = "infixr 30 -; main() -> i64 { 10 - 3 - 2 }";
    let result = StageZeroCompiler::new()
        .compile(request(source))
        .unwrap()
        .artifact
        .unwrap()
        .run_i64()
        .unwrap();
    assert_eq!(
        result, 9,
        "the canonical bare callable must use infixr grouping"
    );

    let package = PackageKey("fixity-bare-scan@0.1.0".into());
    let file = FileKey::new(&package, "src/main.glorious");
    let canonical = "infixl 20 ==; encode(prefix: u8) -> u8 { prefix }";
    let lexed = LexedFile::lex(file, canonical);
    let scan = DeclarationScan::scan(&lexed, canonical);
    assert!(scan.diagnostics.is_empty(), "{scan:#?}");
    assert_eq!(scan.declarations.len(), 2);
    assert_eq!(scan.declarations[0].name.as_deref(), Some("=="));
    assert_eq!(scan.declarations[1].name.as_deref(), Some("encode"));
    let parsed = HeaderParse::parse(&lexed, canonical, &scan.declarations[0]);
    assert!(parsed.diagnostics.is_empty(), "{parsed:#?}");
}

#[test]
fn non_associative_chains_are_rejected_before_mir() {
    let source = "infix 30 -; pub fn main() -> i64 { 10 - 3 - 2 }";
    let Err(ServiceError::Failed(diagnostics)) = StageZeroCompiler::new().compile(request(source))
    else {
        panic!("non-associative chain unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4112")
    );
}

#[test]
fn conflicting_fixities_are_structured_and_table_fingerprints_track_declarations() {
    let first = interface("infixl 30 +; pub fn main() -> i64 { 1 }");
    let second = interface("infixr 30 +; pub fn main() -> i64 { 1 }");
    assert_ne!(
        FixityTable::for_module(&first.interface).fingerprint(),
        FixityTable::for_module(&second.interface).fingerprint()
    );
    let duplicate = interface("infixl 30 +; infixr 30 +; pub fn main() -> i64 { 1 }");
    assert!(
        duplicate
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3002")
    );
}
