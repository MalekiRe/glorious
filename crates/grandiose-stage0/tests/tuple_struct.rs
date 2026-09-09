use grandiose_stage0::{CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest,
    LogicalPath, PackageKey, SourceInput, StageZeroCompiler, decode_and_verify_program};

fn compile(source: &str) -> Result<grandiose_stage0::CompilationOutcome, grandiose_stage0::ServiceError> {
    let package = PackageKey("tuple-struct@1".into());
    StageZeroCompiler::new().compile(CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"tuple-struct")),
        mode: CompilationMode::Build, root_package: package.clone(),
        sources: vec![SourceInput::new(package, LogicalPath::parse("src/main.glorious").unwrap(), source.as_bytes())],
        target: "stage0-vm".into(), semantic_options: Default::default(), codegen_options: Default::default(),
        capability_manifest: vec![], runtime_manifest: None,
    })
}

fn run(source: &str, expected: i64) {
    let artifact = compile(source).unwrap_or_else(|error| panic!("{source}: {error:?}")).artifact.unwrap();
    assert_eq!(artifact.run_i64().unwrap(), expected);
    assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), expected);
}

#[test]
fn tuple_structs_preserve_nominal_identity_and_numeric_places() {
    run("struct Pair<A,B>(A,B); fn make() -> Pair<i64,i64> { Pair(40,1) }
        pub fn main() -> i64 { let mut value = make(); value.1 = 2; value.0 + value.1 }", 42);
    for source in [
        "struct Pair(i64,i64); pub fn main() -> i64 { let value: Pair = (40,2); value.0 }",
        "struct Pair(i64,i64); struct Other(i64,i64); pub fn main() -> i64 { let value: Pair = Other(40,2); value.0 }",
        "struct Pair(i64,i64); pub fn main() -> i64 { Pair(40,2).2 }",
        "struct Pair(i64,i64); pub fn main() -> i64 { Pair(40).0 }",
        "struct Pair(i64); pub fn main() -> i64 { Pair(40,2).0 }",
    ] { assert!(compile(source).is_err(), "{source}"); }
}

#[test]
fn tuple_struct_constructor_values_and_import_aliases_are_callable() {
    run("mod model { pub struct Pair(pub i64,pub i64); }
        use model::Pair as Renamed;
        fn apply(make: (i64,i64) -> Renamed) -> Renamed { make(40,2) }
        pub fn main() -> i64 { let make = Renamed; let value = apply(make); value.0 + value.1 }", 42);
}

#[test]
fn tuple_struct_patterns_transfer_and_discard_fields_lawfully() {
    run("struct Pair<T>(T,i64); pub fn main() -> i64 { let Pair(first, second) = Pair(40,2); first + second }", 42);
    run("struct Marker(); pub fn main() -> i64 { handle Marker() { Marker() => 42 } }", 42);
    run("struct Pair(i64,i64); pub fn main() -> i64 { handle Pair(40,2) { Pair(first, second) => first + second } }", 42);
}

#[test]
fn tuple_struct_fields_keep_declaring_module_and_restricted_authority() {
    run("mod outer { pub mod model { pub struct Pair(pub(super) i64,pub(crate) i64);
        pub fn make() -> Pair { Pair(40,2) } }
        pub fn read() -> i64 { let value = model::make(); value.0 + value.1 }
    } pub fn main() -> i64 { outer::read() }", 42);
    let prefix = "pub mod model { pub struct Hidden(i64); pub fn make() -> Hidden { Hidden(42) }
        pub mod child { pub fn read() -> i64 { super::make().0 } } }";
    run(&format!("{prefix} pub fn main() -> i64 {{ model::child::read() }}"), 42);
    for body in ["model::Hidden(42).0", "model::make().0", "handle model::make() { model::Hidden(value) => value }",
        "let constructor = model::Hidden; 42"] {
        let source = format!("{prefix} pub fn main() -> i64 {{ {body} }}");
        let error = compile(&source).unwrap_err();
        assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.message.contains("private field")), "{body}: {error:?}");
    }
}

#[test]
fn tuple_struct_arguments_execute_left_to_right() {
    run("struct Pair(i64,i64); effect Trace { [1,1] value(i64) -> i64; }
        fn make() -> Pair / {Trace} { Pair(Trace::value(1), Trace::value(2)) }
        pub fn main() -> i64 { let mut seen = 0; let pair = handle make() {
            Trace::value(value) with k => { seen = seen * 10 + value; k(value) }
        }; seen + pair.0 + pair.1 }", 15);
}
