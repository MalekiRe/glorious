use std::collections::BTreeMap;
use grandiose_stage0::{CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest,
    LogicalPath, PackageKey, SourceInput, StageZeroCompiler, decode_and_verify_program};

fn request(source: &str, optimization: &str) -> CompilationRequest {
    let package = PackageKey("borrowed-temporaries@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"borrowed-temporaries")),
        mode: CompilationMode::Build, root_package: package.clone(),
        sources: vec![SourceInput::new(package, LogicalPath::parse("src/main.glorious").unwrap(), source.as_bytes())],
        target: "stage0-vm".into(), semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::from([("optimization-level".into(), optimization.into())]),
        capability_manifest: vec![], runtime_manifest: None,
    }
}

fn assert_callable_ownership_across_engines(source: &str) {
    let input = request(source, "0");
    let artifact = StageZeroCompiler::new().compile(input.clone())
        .unwrap_or_else(|error| panic!("{source}: {error:?}")).artifact.unwrap();
    assert_eq!(artifact.run_i64().unwrap_or_else(|error| panic!("{source}: {error:?}")), 42);
    assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
    use grandiose_stage0::vm_backend::llvm::{LlvmCompileOptions, LlvmTarget};
    let ir = StageZeroCompiler::new().compile_llvm(input, LlvmTarget::host().unwrap()).unwrap();
    for optimization in [0, 2] {
        let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
        assert_eq!(native.run_i64_with_limits(Default::default()).unwrap(), 42, "O{optimization}: {source}");
    }
}

#[test]
fn borrowed_temporaries_have_local_storage_and_can_be_read_or_reborrowed() {
    for source in [
        "fn read(value: &i64) -> i64 { *value } pub fn main() -> i64 { read(&42) }",
        "fn read(value: &i64) -> i64 { *value } pub fn main() -> i64 { let value = &42; read(value) }",
        "fn read(value: &i64) -> i64 { *value } pub fn main() -> i64 { let value = &42; read(& *value) }",
        "fn make() -> (i64, i64) { (42, 0) } fn read(value: &(i64, i64)) -> i64 { value.0 } pub fn main() -> i64 { read(&make()) }",
        "fn read(value: &i64) -> i64 { *value } pub fn main() -> i64 { read(&(42, 0).0) }",
        "fn set(value: &mut i64) -> i64 { *value = 42; *value } pub fn main() -> i64 { set(&mut 0) }",
        "fn read(value: &u128) -> i64 { handle *value { 340282366920938463463374607431768211455 => 42, _ => 0 } } pub fn main() -> i64 { read(&340282366920938463463374607431768211455) }",
        "effect Stop { stop() -> !; } fn read(value: &i64) -> i64 { *value } pub fn main() -> i64 { handle read(&Stop::stop()) { Stop::stop() => 42 } }",
        "pub fn main() -> i64 { label done { let value = &{ transfer done 42 }; *value } }",
    ] {
        for optimization in ["0", "2"] {
            let outcome = StageZeroCompiler::new().compile(request(source, optimization))
                .unwrap_or_else(|error| panic!("{source}: {:#?}", error.diagnostics()));
            let artifact = outcome.artifact.unwrap();
            let program = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
            assert_eq!(program.run_i64().unwrap(), 42, "{source}");
        }
    }
}

#[test]
fn inferred_completion_references_remain_readable_and_assignable() {
    for source in [
        "enum Wrapped<T> { Value(T) } pub fn main() -> i64 { let mut value = 0; let place = handle Wrapped::Value(&mut value) { Wrapped::Value(found) => found }; *place = 42; value }",
        "enum Wrapped<T> { Value(T) } pub fn main() -> i64 { let value = 42; let place = handle Wrapped::Value(&value) { Wrapped::Value(found) => found }; *place }",
        "enum Wrapped<T> { Value(T) } pub fn main() -> i64 { let mut value = 0; *(handle Wrapped::Value(&mut value) { Wrapped::Value(found) => found }) = 42; value }",
        "enum Wrapped<T> { Value(T) } struct Cell { value: i64 } pub fn main() -> i64 { let mut cell = Cell { value: 0 }; (*(handle Wrapped::Value(&mut cell) { Wrapped::Value(found) => found })).value = 42; cell.value }",
        "pub fn main() -> i64 { let mut value = 0; let mut order = 0; *{ order = order * 10 + 2; &mut value } = { order = order * 10 + 4; 0 }; order }",
        "pub fn main() -> i64 { let mut value = 0; label done { *{ value = 1; &mut value } = { transfer done 0 }; 0 }; value + 42 }",
        "pub fn main() -> i64 { let mut value = 0; label done { *(handle true { true => transfer done 0, false => &mut value }) = 1; 0 }; value + 42 }",
        "enum Wrapped<T> { Value(T) } struct Cell { value: i64 } pub fn main() -> i64 { let mut cell = handle Wrapped::Value(Cell { value: 0 }) { Wrapped::Value(found) => found }; cell.value = 42; cell.value }",
        "enum Wrapped<T> { Value(T) } fn answer() -> i64 { 42 } pub fn main() -> i64 { let callback = handle Wrapped::Value(answer) { Wrapped::Value(found) => found }; callback() }",
    ] {
        for optimization in ["0", "2"] {
            let artifact = StageZeroCompiler::new().compile(request(source, optimization))
                .unwrap_or_else(|error| panic!("{source}: {:#?}", error.diagnostics())).artifact.unwrap();
            assert_eq!(artifact.run_i64().unwrap_or_else(|error| panic!("{source}: {error:?}")), 42);
            assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
        }
    }
}

#[test]
fn completion_transfers_preserve_callable_resident_ownership() {
    for source in [
        "enum Wrapped<T> { Value(T) } fn answer() -> i64 { 42 }
        pub fn main() -> i64 {
            let callback = handle Wrapped::Value(answer) { Wrapped::Value(found) => found }; callback()
        }",
        "fn answer() -> i64 { 21 } pub fn main() -> i64 {
            let wrapped=(answer,); let first=wrapped.0; let second=wrapped.0; first()+second() }",
        "fn answer() -> i64 { 21 } pub fn main() -> i64 {
            let original=answer; let reference = &original; let copied = *reference; copied()+original() }",
        "struct Pair<T> { first:T, second:i64 } fn answer() -> i64 { 21 }
        pub fn main() -> i64 { let wrapped=Pair { first:answer, second:0 };
            let first=wrapped.first; let second=wrapped.first; first()+second() }",
        "enum Wrapped<T> { Value(T) } struct Pair<T> { first:T, second:i64 }
        pub fn main() -> i64 { let value=40; let task=move (value) { value+2 };
            let outer=Wrapped::Value(Pair { first:task, second:0 });
            let callback=handle outer { Wrapped::Value(Pair { first:found, second:_ }) => found }; callback() }",
    ] {
        assert_callable_ownership_across_engines(source);
    }
}

#[test]
fn projected_stateful_callable_copies_have_independent_environments() {
    for source in [
        "pub fn main() -> i64 { let mut count=0; let task=move (count) { count=count+1; count };
            let wrapped=(task,); let first=wrapped.0; let second=wrapped.0; first()+second()+40 }",
        "pub fn main() -> i64 { let mut count=0; let task=move (count) { count=count+1; count };
            let wrapped=((task,),); let first=wrapped.0.0; let second=wrapped.0.0; first()+first()+second()+38 }",
        "struct Wrapped<T> { value:T } pub fn main() -> i64 {
            let mut count=0; let task=move (count) { count=count+1; count };
            let wrapped=Wrapped { value:task }; let first=wrapped.value; let second=wrapped.value;
            first()+first()+second()+38 }",
    ] {
        assert_callable_ownership_across_engines(source);
    }
}

#[test]
fn projected_callable_residents_do_not_duplicate_owned_unique_references() {
    let source = "pub fn main() -> i64 { let mut value = 21; let reference = &mut value;
        let task = move (reference) { *reference }; let wrapped = (task,);
        let first = wrapped.0; let second = wrapped.0; first()+second() }";
    let diagnostics = match StageZeroCompiler::new().compile(request(source, "0")) {
        Err(error) => error.diagnostics(),
        Ok(outcome) => panic!("accepted duplicate unique-capture projection; execution: {:?}",
            outcome.artifact.unwrap().run_i64()),
    };
    assert!(diagnostics.iter().any(|diagnostic| matches!(diagnostic.code, "G5001" | "G5003")), "{diagnostics:#?}");
}

#[test]
fn inferred_completion_reference_shapes_do_not_grant_mutability_or_escape() {
    for (source, required) in [
        ("enum Wrapped<T> { Value(T) } pub fn main() -> i64 { let value = 0; let place = handle Wrapped::Value(&value) { Wrapped::Value(found) => found }; *place = 42; value }", "G4141"),
        ("enum Wrapped<T> { Value(T) } fn bad() -> &'static i64 { let value = 42; handle Wrapped::Value(&value) { Wrapped::Value(found) => found } } pub fn main() -> i64 { 42 }", "G5017"),
        ("enum Wrapped<T> { Value(T) } pub fn main() -> i64 { let mut value = 0; let first = &mut value; *(handle Wrapped::Value(&mut value) { Wrapped::Value(found) => found }) = 42; *first }", "G5006"),
    ] {
        let diagnostics = StageZeroCompiler::new().compile(request(source, "0"))
            .expect_err("inference resolves a type, not additional borrow authority").diagnostics();
        assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == required), "{source}: {diagnostics:#?}");
    }
}

#[test]
fn borrowed_temporary_initializers_and_destructors_execute_once() {
    for source in [
        "fn make(count: &mut i64) -> i64 { *count = *count + 1; 42 } fn read(value: &i64) -> i64 { *value } pub fn main() -> i64 { let mut count = 0; let result = read(&make(&mut count)); handle count { 1 => result, _ => 0 } }",
        "use std::*; struct Probe<'a> { count: &'a mut i64 } impl<'a> Use<[0,1]> for Probe<'a> {} impl<'a> Drop for Probe<'a> { drop(&mut self) -> { *self.count = *self.count + 1; } } fn read(value: &Probe) -> i64 { 42 } pub fn main() -> i64 { let mut count = 41; { read(&Probe { count: &mut count }); () }; count }",
        "use std::*; struct Probe<'a> { count: &'a mut i64, value: i64 } impl<'a> Use<[0,1]> for Probe<'a> {} impl<'a> Drop for Probe<'a> { drop(&mut self) -> { *self.count = *self.count + self.value; } } fn read(value: &i64) -> i64 { *value } pub fn main() -> i64 { let mut count = 0; { read(&Probe { count: &mut count, value: 42 }.value); () }; count }",
    ] {
        for optimization in ["0", "2"] {
            let artifact = StageZeroCompiler::new().compile(request(source, optimization))
                .unwrap_or_else(|error| panic!("{source}: {:#?}", error.diagnostics())).artifact.unwrap();
            assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
        }
    }
}

#[test]
fn borrowed_temporaries_cannot_escape_their_storage_scope_or_tail_frame() {
    for source in [
        "pub fn main() -> &'static i64 { &42 }",
        "pub fn main() -> &'static i64 { let value = &42; value }",
        "fn same<'a>(value: &'a i64) -> &'a i64 { value } pub fn main() -> &'static i64 { same(&42) }",
        "fn read(value: &i64) -> i64 { *value } pub fn main() -> i64 { let value = { &42 }; read(value) }",
        "fn read(value: &i64) -> i64 { *value } pub fn main() -> i64 { let original = 0; let mut value = &original; { value = &42; () }; read(value) }",
        "fn read(value: &i64) -> i64 { *value } pub fn main() -> i64 { let original = 0; let mut value = (&original,); { value.0 = &42; () }; read(value.0) }",
        "fn read(value: &i64) -> i64 { *value } pub fn main() -> i64 { tail read(&42) }",
    ] {
        let diagnostics = StageZeroCompiler::new().compile(request(source, "0"))
            .expect_err(source).diagnostics();
        assert!(diagnostics.iter().any(|diagnostic| matches!(diagnostic.code, "G5013" | "G4403")), "{source}: {diagnostics:#?}");
    }
}

#[test]
fn borrowed_temporary_destructors_keep_their_input_loans_live() {
    let source = "use std::*; struct Probe<'a> { count: &'a mut i64 } impl<'a> Use<[0,1]> for Probe<'a> {} impl<'a> Drop for Probe<'a> { drop(&mut self) -> { *self.count = *self.count + 1; } } fn read(value: &Probe) -> i64 { 42 } pub fn main() -> i64 { let mut count = 0; { read(&Probe { count: &mut count }); count = 41; () }; count }";
    let diagnostics = StageZeroCompiler::new().compile(request(source, "0")).expect_err(source).diagnostics();
    assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G5007"), "{diagnostics:#?}");
}

#[test]
fn expected_static_references_do_not_promote_temporary_storage() {
    for source in [
        "fn need(value: &'static u128) -> i64 { 42 } pub fn main() -> i64 { need(&340282366920938463463374607431768211455) }",
        "fn need(value: &'static Str) -> i64 { 42 } pub fn main() -> i64 { need(&\"text\") }",
    ] {
        let diagnostics = StageZeroCompiler::new().compile(request(source, "0")).expect_err(source).diagnostics();
        assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G5017"), "{diagnostics:#?}");
    }
}
