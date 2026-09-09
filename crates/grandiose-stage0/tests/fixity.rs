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
fn explicit_fixity_targets_bind_prefix_and_infix_to_independent_functions() {
    let source = "mod numeric { pub fn negate(value: i64) -> i64 { 0 - value } pub fn subtract(left: i64, right: i64) -> i64 { left - right } } prefix 50 ~ = numeric::negate; infixl 30 ~ = numeric::subtract; pub fn main() -> i64 { ~ 2 ~ (0 - 44) }";
    for optimization in ["0", "2"] {
        let mut input = request(source);
        input.codegen_options.insert("optimization-level".into(), optimization.into());
        let artifact = StageZeroCompiler::new().compile(input)
            .unwrap_or_else(|error| panic!("{:#?}", error.diagnostics())).artifact.unwrap();
        assert_eq!(artifact.run_i64().unwrap(), 42);
        assert_eq!(grandiose_stage0::decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
    }
}

#[test]
fn imported_operator_target_is_resolved_in_its_declaring_module() {
    let source = "pub mod syntax { fn choose(left: i64, right: i64) -> i64 { left } pub infixl 30 ** = choose; } use syntax::*; fn choose(left: i64, right: i64) -> i64 { right } pub fn main() -> i64 { 42 ** 0 }";
    let artifact = StageZeroCompiler::new().compile(request(source))
        .unwrap_or_else(|error| panic!("{:#?}", error.diagnostics())).artifact.unwrap();
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn explicit_operator_targets_accept_aliases_and_preserve_operand_order() {
    let source = "fn pair(left: i64, right: i64) -> i64 { left * 10 + right } let chosen = pair; infixl 30 ** = chosen; fn next(count: &mut i64) -> i64 { *count = *count + 1; *count } pub fn main() -> i64 { let mut count = 0; let result = next(&mut count) ** next(&mut count); result + count + 28 }";
    let artifact = StageZeroCompiler::new().compile(request(source))
        .unwrap_or_else(|error| panic!("{:#?}", error.diagnostics())).artifact.unwrap();
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn explicit_target_contract_edits_invalidate_the_fixity_product() {
    let first = interface("fn pick(left: i64, right: i64) -> i64 { left } infixl 30 ** = pick;");
    let second = interface("fn pick(left: u32, right: u32) -> u32 { left } infixl 30 ** = pick;");
    assert_ne!(FixityTable::for_module(&first.interface).fingerprint(),
        FixityTable::for_module(&second.interface).fingerprint());
    let compiler = StageZeroCompiler::new();
    let source = "mod provider { fn pick(left: i64, right: i64) -> i64 { left } pub infixl 30 ** = pick; } use provider::*; pub fn main() -> i64 { 42 ** 0 }";
    assert_eq!(compiler.compile(request(source)).unwrap().artifact.unwrap().run_i64().unwrap(), 42);
    assert!(compiler.compile(request(&source.replace("fn pick(left: i64, right: i64) -> i64", "fn pick(left: u32, right: u32) -> u32"))).is_err());
}

#[test]
fn exported_operator_seals_its_private_target_contract() {
    let before = interface("fn pick(left: i64, right: i64) -> i64 { left } pub infixl 30 ** = pick;");
    let after = interface("fn pick(left: u32, right: u32) -> u32 { left } pub infixl 30 ** = pick;");
    let before_index = grandiose_stage0::DefinitionIndex::from_interface(&before.interface);
    let after_index = grandiose_stage0::DefinitionIndex::from_interface(&after.interface);
    assert_ne!(before_index.sealed_public_fingerprint(&before.interface),
        after_index.sealed_public_fingerprint(&after.interface));
    let before = interface("fn pick(left: i64, right: i64) -> i64 { left } let chosen = pick; pub infixl 30 ** = chosen;");
    let after = interface("fn pick(left: u32, right: u32) -> u32 { left } let chosen = pick; pub infixl 30 ** = chosen;");
    let before_index = grandiose_stage0::DefinitionIndex::from_interface(&before.interface);
    let after_index = grandiose_stage0::DefinitionIndex::from_interface(&after.interface);
    assert_ne!(before_index.sealed_public_fingerprint(&before.interface),
        after_index.sealed_public_fingerprint(&after.interface));
    assert_ne!(FixityTable::for_module(&before.interface).fingerprint(),
        FixityTable::for_module(&after.interface).fingerprint());
}

#[test]
fn explicit_operator_targets_preserve_generic_borrowed_and_safety_contracts() {
    for source in [
        "fn first<T>(left: T, right: i64) -> T { left } infixl 30 ** = first; pub fn main() -> i64 { 42 ** 0 }",
        "fn first(left: &i64, right: &i64) -> i64 { *left } infixl 30 ** = first; pub fn main() -> i64 { let left = 42; let right = 0; &left ** &right }",
        "unsafe fn first(left: i64, right: i64) -> i64 { left } infixl 30 ** = first; pub fn main() -> i64 { unsafe { 42 ** 0 } }",
        "effect Read { read() -> i64; } fn first(left: i64, right: i64) -> i64 / Read { Read::read() } infixl 30 ** = first; pub fn main() -> i64 { handle 0 ** 0 { Read::read() => 42 } }",
    ] {
        let artifact = StageZeroCompiler::new().compile(request(source))
            .unwrap_or_else(|error| panic!("{source}\n{:#?}", error.diagnostics())).artifact.unwrap();
        // SAFETY: the only unsafe fixture returns a scalar argument and has
        // no memory operations, external imports, or other caller obligations.
        assert_eq!(unsafe { artifact.run_i64_with_unsafe(grandiose_stage0::VmExecutionLimits::default()) }.unwrap(), 42);
    }
    for source in [
        "fn first(left: &i64, right: &i64) -> i64 { *left } infixl 30 ** = first; pub fn main() -> i64 { 42 ** 0 }",
        "unsafe fn first(left: i64, right: i64) -> i64 { left } infixl 30 ** = first; pub fn main() -> i64 { 42 ** 0 }",
        "effect Read { read() -> i64; } fn first(left: i64, right: i64) -> i64 / Read { Read::read() } infixl 30 ** = first; pub fn main() -> i64 { 0 ** 0 }",
    ] {
        StageZeroCompiler::new().compile(request(source)).expect_err(
            "operator binding must not supply implicit borrows, unsafe permission, or effects");
    }
}

#[test]
fn invalid_explicit_operator_targets_do_not_fall_back_to_other_dispatch() {
    for source in [
        "infixl 30 + = absent; pub fn main() -> i64 { 20 + 22 }",
        "fn unary(value: i64) -> i64 { value } infixl 30 + = unary; pub fn main() -> i64 { 20 + 22 }",
        "const value: i64 = 42; infixl 30 + = value; pub fn main() -> i64 { 20 + 22 }",
        "infixl 30 ** = absent; pub fn main() -> i64 { 42 }",
        "infixl 30 ** = ; pub fn main() -> i64 { 42 }",
        "infixl 30 ** = source::; pub fn main() -> i64 { 42 }",
    ] {
        let error = StageZeroCompiler::new().compile(request(source))
            .expect_err("an explicit target is an interface obligation even when unused");
        assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G3214"),
            "{source}\n{:#?}", error.diagnostics());
    }
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
