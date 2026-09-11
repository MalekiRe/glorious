//! Default distributed prelude and source-owned opt-outs (language §2.5).

use grandiose_stage0::{
    CompilationMode, CompilationOutcome, CompilationRequest, CompilerBuildIdentity,
    DeclarationScan, Digest, FileKey, LexedFile, LogicalPath, PackageKey, SourceInput,
    StageZeroCompiler, decode_and_verify_program,
};

fn request(source: &str) -> CompilationRequest {
    let package = PackageKey("prelude-tests@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"prelude-tests")),
        mode: CompilationMode::Build,
        root_package: package.clone(),
        sources: vec![SourceInput::new(
            package,
            LogicalPath::parse("src/main.glorious").unwrap(),
            source.as_bytes(),
        )],
        target: "stage0-vm".into(),
        semantic_options: Default::default(),
        codegen_options: Default::default(),
        capability_manifest: vec![],
        runtime_manifest: None,
    }
}

fn runs(source: &str) -> CompilationOutcome {
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:?}", outcome.diagnostics);
    let program = outcome.artifact.as_ref().unwrap();
    assert_eq!(program.run_i64().unwrap(), 42);
    assert_eq!(
        decode_and_verify_program(&program.canonical_bytes())
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
    outcome
}

#[test]
fn default_prelude_resolves_source_defined_arithmetic_without_an_import() {
    runs("pub fn main() -> i64 { 40 + 2 }");
}

#[test]
fn prelude_reexport_cycle_preserves_green_interfaces_after_private_edits() {
    use grandiose_stage0::{DependencyNode, DependencyStatus, ModuleKey};
    let compiler = StageZeroCompiler::new();
    let parent = compiler
        .import_revision(
            request("fn unused() -> i64 { 0 } pub fn main() -> i64 { 40 + 2 }"),
            None,
        )
        .unwrap();
    compiler.compile_revision(parent).unwrap();
    let child = compiler
        .import_revision(
            request("fn unused() -> i64 { 1 } pub fn main() -> i64 { 40 + 2 }"),
            Some(parent),
        )
        .unwrap();
    let outcome = compiler.compile_revision(child).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
    let interface = DependencyNode::Interface(ModuleKey {
        package: PackageKey("prelude-tests@0.1.0".into()),
        path: "crate".into(),
    });
    assert!(matches!(
        compiler.dependency_trace(child, &interface).unwrap().status,
        DependencyStatus::Green { .. }
    ));
}

#[test]
fn default_prelude_resolves_result_based_boolean_types_and_constants() {
    runs(
        "fn yes() -> Bool { true } pub fn main() -> i64 { handle yes() { true => 42, false => 7 } }",
    );
}

#[test]
fn unit_patterns_execute_in_completions_nested_values_and_operation_payloads() {
    for source in [
        "pub fn main() -> i64 { handle () { () => 42 } }",
        "pub fn main() -> i64 { handle ((), [(), ()]) { ((), [(), ()]) => 42, _ => 0 } }",
        "fn value() -> Result<(), i64> { Ok(()) } pub fn main() -> i64 { handle value() { Result::Ok(()) => 42, Result::Err(_) => 0 } }",
        "effect Pick { [1, 1] pick(()) -> i64; } pub fn main() -> i64 { handle Pick::pick(()) { Pick::pick((), k) => k(42) } }",
    ] {
        runs(source);
    }
}

#[test]
fn unit_patterns_do_not_accept_nonunit_subjects_or_nonempty_tuple_patterns() {
    for source in [
        "pub fn main() -> i64 { handle 7 { () => 42 } }",
        "pub fn main() -> i64 { handle ((), 7) { () => 42 } }",
        "pub fn main() -> i64 { handle () { (value,) => 42 } }",
    ] {
        let input = request(source);
        let file = input.sources[0].key;
        let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = StageZeroCompiler::new().compile(input) else {
            panic!("mismatched unit pattern compiled: {source}");
        };
        assert!(diagnostics.iter().any(|d| matches!(d.code, "G4202" | "G4203")
            && d.primary.is_some_and(|span| span.file == file)), "{diagnostics:#?}");
    }
}

#[test]
fn boolean_constants_infer_closed_types_without_context() {
    runs(
        "pub fn main() -> i64 { let yes = true; let no = false; handle (yes, no) { (true, false) => 42, _ => 0 } }",
    );
}

#[test]
fn boolean_constants_infer_inside_unannotated_nested_tuples() {
    runs(
        "pub fn main() -> i64 { handle ((true, true), false) { ((true, true), false) => 42, _ => 0 } }",
    );
}

#[test]
fn boolean_constants_infer_inside_unannotated_arrays() {
    runs("pub fn main() -> i64 { handle [true, true] { [true, true] => 42, _ => 0 } }");
}

#[test]
fn boolean_constants_cannot_inhabit_other_result_instantiations() {
    for source in [
        "pub fn main() -> Result<(), i64> { true }",
        "pub fn main() -> Option<i64> { false }",
        "pub fn main() -> i64 { handle Result<(), i64>::Ok(()) { true => 42, _ => 0 } }",
        "pub fn main() -> i64 { handle Result<i64, ()>::Err(()) { false => 42, _ => 0 } }",
    ] {
        let input = request(source);
        let file = input.sources[0].key;
        let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
            StageZeroCompiler::new().compile(input)
        else {
            panic!("Boolean constant widened to another Result instantiation: {source}");
        };
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| matches!(diagnostic.code, "G4107" | "G4201")
                    && diagnostic.primary.is_some_and(|span| span.file == file)),
            "{diagnostics:#?}"
        );
    }
}

#[test]
fn none_remains_generic_across_distinct_option_instantiations() {
    runs(
        "fn number() -> Option<i64> { None } fn flag() -> Option<Bool> { None } pub fn main() -> i64 { handle (number(), flag()) { (None, None) => 42, _ => 0 } }",
    );
}

#[test]
fn explicit_result_constructors_remain_polymorphic() {
    runs(
        "fn yes() -> Result<(), i64> { Ok(()) } fn no() -> Option<i64> { Err(()) } pub fn main() -> i64 { handle (yes(), no()) { (Result::Ok(_), Result::Err(_)) => 42, _ => 0 } }",
    );
}

#[test]
fn selected_prelude_tracks_public_contracts_but_not_private_provider_bodies() {
    use grandiose_stage0::{DependencyNode, DependencyStatus, ModuleKey};
    let compiler = StageZeroCompiler::new();
    let with_provider = |provider: &str| {
        let mut input = request("pub fn chosen() -> Pick { 42 } pub fn main() -> i64 { 42 }");
        input.sources.push(SourceInput::new(
            PackageKey("std@9.0.0".into()),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            provider.as_bytes(),
        ));
        input
    };
    let original =
        "pub type Pick = i64; pub mod prelude { pub use crate::Pick; } fn private() -> i64 { 0 }";
    let parent = compiler
        .import_revision(with_provider(original), None)
        .unwrap();
    compiler.compile_revision(parent).unwrap();
    let private_edit = compiler
        .import_revision(
            with_provider(&original.replace("{ 0 }", "{ 1 }")),
            Some(parent),
        )
        .unwrap();
    compiler.compile_revision(private_edit).unwrap();
    let interface = DependencyNode::Interface(ModuleKey {
        package: PackageKey("prelude-tests@0.1.0".into()),
        path: "crate".into(),
    });
    let before = compiler.dependency_trace(parent, &interface).unwrap();
    let private = compiler.dependency_trace(private_edit, &interface).unwrap();
    assert_eq!(before.fingerprint, private.fingerprint);
    assert!(matches!(private.status, DependencyStatus::Green { .. }));
    let public_edit = compiler
        .import_revision(
            with_provider(&original.replace("Pick = i64", "Pick = u64")),
            Some(parent),
        )
        .unwrap();
    compiler.compile_revision(public_edit).unwrap();
    let public = compiler.dependency_trace(public_edit, &interface).unwrap();
    assert_ne!(before.fingerprint, public.fingerprint);
    assert!(matches!(public.status, DependencyStatus::Red { .. }));
}

#[test]
fn default_prelude_is_inherited_by_nested_modules() {
    runs(
        "mod nested { pub fn value() -> i64 { 40 + 2 } } pub fn main() -> i64 { nested::value() }",
    );
}

#[test]
fn lexical_and_explicit_type_bindings_outrank_the_prelude() {
    runs("type Bool = i64; pub fn main() -> Bool { 42 }");
    runs(
        "mod custom { pub type Bool = i64; } use crate::custom::Bool; pub fn main() -> Bool { 42 }",
    );
}

#[test]
fn no_std_suppresses_automatic_library_inclusion() {
    let outcome = runs("#![no_std]\npub fn main() -> i64 { 42 }");
    assert!(outcome.runtime_manifest.is_none());
}

#[test]
fn opt_outs_reject_implicit_library_names() {
    for attribute in ["no_std", "no_implicit_prelude"] {
        let source = format!("#![{attribute}]\npub fn main() -> Bool {{ true }}");
        let error = StageZeroCompiler::new()
            .compile(request(&source))
            .unwrap_err();
        assert!(
            error
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == "G3304"),
            "{error:?}"
        );
    }
}

#[test]
fn no_implicit_prelude_preserves_explicit_dependency_imports() {
    runs(
        "#![no_implicit_prelude]\nuse std::{Bool, true, false}; fn yes() -> Bool { true } pub fn main() -> i64 { handle yes() { true => 42, false => 7 } }",
    );
}

#[test]
fn comments_do_not_select_library_opt_outs() {
    let source = "// #![no_std]\n/* #![no_implicit_prelude] */ pub fn main() -> i64 { let text = \"#![no_std]\"; 40 + 2 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:?}", outcome.diagnostics);
    let program = outcome.artifact.unwrap();
    let decoded = decode_and_verify_program(&program.canonical_bytes()).unwrap();
    // SAFETY: this local fixture now materializes its unannotated literal
    // through the bundled library's native-memory-backed static Str wrapper.
    assert_eq!(unsafe { program.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
    assert_eq!(unsafe { decoded.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
}

#[test]
fn an_opted_out_module_can_explicitly_import_the_source_prelude() {
    runs("#![no_implicit_prelude]\nuse std::prelude::*; pub fn main() -> i64 { 40 + 2 }");
}

#[test]
fn nested_module_opt_outs_suppress_inherited_automatic_imports() {
    let source = "mod nested { #![no_implicit_prelude] pub fn value() -> Bool { true } } pub fn main() -> i64 { 42 }";
    let error = StageZeroCompiler::new()
        .compile(request(source))
        .unwrap_err();
    assert!(
        error
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == "G3304"),
        "{error:?}"
    );
}

#[test]
fn no_std_keeps_explicitly_supplied_dependencies_available() {
    let mut request = request("#![no_std]\nuse provider::value; pub fn main() -> i64 { value() }");
    request.sources.push(SourceInput::new(
        PackageKey("provider@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub fn value() -> i64 { 42 }".as_slice(),
    ));
    let outcome = StageZeroCompiler::new().compile(request).unwrap();
    assert!(outcome.runtime_manifest.is_none());
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn the_default_prelude_does_not_implicitly_reexport_through_user_modules() {
    let source = "mod user {} pub fn main() -> user::Bool { true }";
    let error = StageZeroCompiler::new()
        .compile(request(source))
        .unwrap_err();
    assert!(
        error
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == "G3304"),
        "{error:?}"
    );
}

#[test]
fn module_attributes_preserve_original_declaration_spans() {
    let package = PackageKey("attributes@0.1.0".into());
    let source = "#![no_std]\n#![no_implicit_prelude]\npub fn main() -> i64 { 42 }";
    let lexed = LexedFile::lex(FileKey::new(&package, "src/main.glorious"), source);
    assert!(lexed.diagnostics.is_empty(), "{:?}", lexed.diagnostics);
    let scan = DeclarationScan::scan(&lexed, source);
    assert!(scan.diagnostics.is_empty(), "{scan:?}");
    assert!(scan.module_attributes.no_std && scan.module_attributes.no_implicit_prelude);
    assert_eq!(
        scan.declarations[0].span.start as usize,
        source.find("pub fn").unwrap()
    );
}

#[test]
fn unknown_or_argument_bearing_opt_out_attributes_are_rejected() {
    for attribute in ["unknown", "no_std(yes)", "no_implicit_prelude = true"] {
        let source = format!("#![{attribute}]\npub fn main() -> i64 {{ 42 }}");
        let error = StageZeroCompiler::new()
            .compile(request(&source))
            .unwrap_err();
        assert!(
            error
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == "G2004"),
            "{error:?}"
        );
    }
}
