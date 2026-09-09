use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath,
    PackageKey, SourceInput, StageZeroCompiler, decode_and_verify_program,
};

fn compile(source: &str) -> Result<grandiose_stage0::CompilationOutcome, grandiose_stage0::ServiceError> {
    let package = PackageKey("mutable-bindings@0.1.0".into());
    StageZeroCompiler::new().compile(CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"mutable-bindings")),
        mode: CompilationMode::Build,
        root_package: package.clone(),
        sources: vec![SourceInput::new(package, LogicalPath::parse("src/main.glorious").unwrap(), source.as_bytes())],
        target: "stage0-vm".into(), semantic_options: Default::default(), codegen_options: Default::default(),
        capability_manifest: vec![], runtime_manifest: None,
    })
}

fn executes(source: &str, expected: i64) {
    let artifact = compile(source).unwrap().artifact.unwrap();
    assert_eq!(artifact.run_i64().unwrap(), expected);
    assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), expected);
}

#[test]
fn explicit_mutable_bindings_execute_replacement_and_reinitialization() {
    executes("pub fn main() -> i64 { let mut value = 1; let previous = move value; value = 42; value }", 42);
    executes("struct Cell { value: i64 } pub fn main() -> i64 { let mut cell = Cell { value: 1 }; cell.value = 42; cell.value }", 42);
}

#[test]
fn immutable_reference_bindings_preserve_unique_referent_authority() {
    executes("fn write(value: &mut i64) -> () { let child = &mut *value; *child = 42; } pub fn main() -> i64 { let mut value = 1; let reference = &mut value; write(reference); value }", 42);
    executes("struct Cell { value: i64 } fn write(cell: &mut Cell) -> () { let field = &mut cell.value; *field = 42; } pub fn main() -> i64 { let mut cell = Cell { value: 1 }; write(&mut cell); cell.value }", 42);
}

#[test]
fn mutable_permission_follows_binding_identity_across_shadowing() {
    executes("pub fn main() -> i64 { let mut value = 1; { let value = 0; }; value = 42; value }", 42);
    executes("pub fn main() -> i64 { let value = 1; let mut value = value; value = 42; value }", 42);
}

#[test]
fn closures_preserve_mutable_capture_authority() {
    executes("pub fn main() -> i64 { let mut value = 1; let write = () -> () { value = 42; }; write(); value }", 42);
}

#[test]
fn immutable_bindings_fail_before_lowering() {
    for source in [
        "pub fn main() -> i64 { let value = 1; value = 42; value }",
        "pub fn main() -> i64 { let value = 1; let reference = &mut value; *reference }",
        "struct Cell { value: i64 } pub fn main() -> i64 { let cell = Cell { value: 1 }; cell.value = 42; cell.value }",
        "pub fn main() -> i64 { let mut value = 1; { let value = 0; value = 42; }; value }",
        "pub fn main() -> i64 { let value = 1; { let mut value = 0; }; value = 42; value }",
        "pub fn main() -> i64 { let value = 1; let write = () -> () { value = 42; }; write(); value }",
        "fn overwrite(value: i64) -> i64 { value = 42; value } pub fn main() -> i64 { overwrite(1) }",
        "pub fn main() -> i64 { let mut first = 1; let mut second = 2; let reference = &mut first; reference = &mut second; *reference }",
    ] {
        let error = compile(source).expect_err(source);
        assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4220"), "{source}: {error:?}");
        assert!(!error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G7042"), "{source}: {error:?}");
    }
}

#[test]
fn mutability_does_not_override_shared_loan_authority() {
    let error = compile("pub fn main() -> i64 { let mut value = 1; let mut shared = &value; let unique = &mut *shared; *unique }").unwrap_err();
    assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4141"), "{error:?}");
}

#[test]
fn explicit_local_types_constrain_initializers_and_preserve_write_authority() {
    executes("pub fn main() -> i64 { let mut value: i64 = 1; value = 42; value }", 42);
    executes("fn widen(value: u8) -> i64 { 42 } pub fn main() -> i64 { let value: u8 = 255; widen(value) }", 42);
    executes("pub fn main() -> i64 { let pair: (i64, i64) = (1, 42); handle pair { (_, second) => second } }", 42);
    executes("pub fn main() -> i64 { let mut value: i64 = 1; let reference: &mut i64 = &mut value; *reference = 42; value }", 42);
}

#[test]
fn explicit_local_types_reject_mismatches_and_short_lifetimes() {
    for (source, code) in [
        ("pub fn main() -> i64 { let value: i64 = (); 0 }", "G4221"),
        ("pub fn main() -> i64 { let value: i64 = 1; value = 42; value }", "G4220"),
        ("fn bad<'a>() -> () { let value = 1; let reference: &'a i64 = &value; } pub fn main() -> i64 { bad(); 0 }", "G5017"),
    ] {
        let error = compile(source).expect_err(source);
        assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == code), "{source}: {error:?}");
    }
}

#[test]
fn tuple_projections_preserve_place_and_reference_authority() {
    executes("pub fn main() -> i64 { let nested = ((1, 42), 0); nested.0.1 }", 42);
    executes("pub fn main() -> i64 { let pair = (1, 42); pair.1 }", 42);
    executes("pub fn main() -> i64 { let mut pair = (1, 2); pair.1 = 42; pair.1 }", 42);
    executes("pub fn main() -> i64 { let mut pair = (1, 2); let field = &mut pair.1; *field = 42; pair.1 }", 42);
    executes("fn write(pair: &mut (i64, i64)) -> () { (*pair).1 = 42; } pub fn main() -> i64 { let mut pair = (1, 2); write(&mut pair); pair.1 }", 42);
    executes("fn read(pair: &(i64, i64)) -> i64 { pair.1 } pub fn main() -> i64 { let pair = (1, 42); read(&pair) }", 42);
    executes("pub fn main() -> i64 { let mut pair = (1, 2); let previous = move pair.1; pair.1 = 42; pair.1 }", 42);
}

#[test]
fn tuple_projection_rejects_invalid_indices_and_immutable_writes() {
    for (source, code) in [
        ("pub fn main() -> i64 { let pair = (1, 2); pair.2 }", "G4129"),
        ("pub fn main() -> i64 { let mut pair = (1, 2); pair.2 = 42; 0 }", "G4139"),
        ("pub fn main() -> i64 { let pair = (1, 2); pair.1 = 42; 0 }", "G4220"),
        ("pub fn main() -> i64 { let pair = (1, 2); let field = &mut pair.1; 0 }", "G4220"),
        ("pub fn main() -> i64 { let pair = (1, 2); pair.first }", "G4129"),
    ] {
        let error = compile(source).expect_err(source);
        assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == code), "{source}: {error:?}");
    }
}

#[test]
fn destructuring_bindings_execute_in_their_lexical_continuation() {
    executes("pub fn main() -> i64 { let (first, second) = (1, 42); second }", 42);
    executes("pub fn main() -> i64 { let (first, (second, third)): (i64, (i64, i64)) = (1, (2, 42)); third }", 42);
    executes("struct Pair { first: i64, second: i64 } pub fn main() -> i64 { let Pair { first, second } = Pair { first: 1, second: 42 }; second }", 42);
    executes("pub fn main() -> i64 { let mut (first, second) = (1, 2); second = 42; second }", 42);
    executes("pub fn main() -> i64 { let first = 42; { let (first, second) = (1, 2); }; first }", 42);
    executes("pub fn main() -> i64 { let (first, second) = (1, 42); let (third, fourth) = (first, second); fourth }", 42);
    executes("pub fn main() -> i64 { let () = (); let _ = 1; 42 }", 42);
    executes("pub fn main() -> i64 { let mut value = 1; let (reference, _) = (&mut value, 0); *reference = 42; value }", 42);
    let artifact = compile("unsafe fn answer() -> i64 { 42 } pub fn main() -> i64 { unsafe { let (first, second) = (1, 2); answer() } }").unwrap().artifact.unwrap();
    let verified = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
    // SAFETY: this closed source's sole unsafe function only returns a literal;
    // no pointer or foreign capability is admitted by the test request.
    unsafe {
        assert_eq!(artifact.run_i64_with_unsafe(Default::default()).unwrap(), 42);
        assert_eq!(verified.run_i64_with_unsafe(Default::default()).unwrap(), 42);
    }
    executes("effect Ask { [1, 1] ask() -> (i64, i64); } pub fn main() -> i64 { handle { let (first, second) = Ask::ask(); second } { Ask::ask() with resume => resume((1, 42)) } }", 42);
}

#[test]
fn destructuring_bindings_reject_refutable_patterns_and_scope_escape() {
    for (source, code) in [
        ("pub fn main() -> i64 { let (1, value) = (1, 42); value }", "G4222"),
        ("enum Choice { First(i64), Second } pub fn main() -> i64 { let Choice::First(value) = Choice::First(42); value }", "G4222"),
        ("pub fn main() -> i64 { let (first, second) = (1, 2); second = 42; second }", "G4220"),
        ("pub fn main() -> i64 { { let (first, second) = (1, 42); }; second }", "G4104"),
        ("pub fn main() -> i64 { let (first, first) = (1, 42); first }", "G4017"),
    ] {
        let error = compile(source).expect_err(source);
        assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == code), "{source}: {error:?}");
    }
}

#[test]
fn destructuring_bindings_preserve_linear_and_borrow_obligations() {
    executes("use std::*; struct Ticket { value: i64 } impl Use<[1, 1]> for Ticket {} pub fn main() -> i64 { let (ticket, _) = (Ticket { value: 42 }, 0); let Ticket { value } = ticket; value }", 42);
    for source in [
        "use std::*; struct Ticket { value: i64 } impl Use<[1, 1]> for Ticket {} pub fn main() -> i64 { let (_, value) = (Ticket { value: 0 }, 42); value }",
        "use std::*; struct Ticket { value: i64 } impl Use<[1, 1]> for Ticket {} pub fn main() -> i64 { let _ = Ticket { value: 42 }; 0 }",
        "pub fn main() -> i64 { let mut value = 1; let (reference, _) = (&value, 0); value = 42; *reference }",
        "pub fn main() -> &i64 { let (reference, _) = { let value = 42; (&value, 0) }; reference }",
    ] {
        let error = compile(source).expect_err(source);
        assert!(!error.diagnostics().iter().any(|diagnostic| matches!(diagnostic.code, "G4003" | "G7006")), "ownership checks must receive valid binding syntax: {source}: {error:?}");
    }
}
