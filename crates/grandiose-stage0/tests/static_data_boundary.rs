use std::collections::BTreeMap;

use grandiose_stage0::{
    CandidateVmArtifact, CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest,
    InferContext, LogicalPath, PackageKey, STAGE0_VM_SCHEMA, ScalarType, SourceInput,
    StageZeroCompiler, Type, VmFunction, VmInstruction, VmType, decode_and_verify_program,
    decode_artifact, encode_artifact, verify_vm,
};

fn raw(tag: u128, alignment: u32) -> Type {
    Type::StaticData {
        element: Box::new(Type::Scalar(ScalarType::U8)),
        tag,
        alignment,
    }
}

fn bundled_request(application: &str) -> CompilationRequest {
    let app = PackageKey("static-data-app@0.1.0".into());
    let standard = PackageKey("std@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"static-data-alias")),
        mode: CompilationMode::Build,
        root_package: app.clone(),
        sources: vec![
            SourceInput::new(
                app,
                LogicalPath::parse("src/main.glorious").unwrap(),
                application.as_bytes(),
            ),
            SourceInput::new(
                standard,
                LogicalPath::parse("src/lib.glorious").unwrap(),
                include_bytes!("../../../stdlib/src/lib.glorious").as_slice(),
            ),
        ],
        target: "stage0-vm".into(),
        semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::new(),
        capability_manifest: vec![],
        runtime_manifest: None,
    }
}

fn run_bundled_usize(source: &str) -> u64 {
    let outcome = StageZeroCompiler::new()
        .compile(bundled_request(source))
        .unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let program = decode_and_verify_program(&outcome.artifact.unwrap().canonical_bytes()).unwrap();
    // SAFETY: only the local source above and the trusted bundled stdlib enter
    // this runner, after independent decoding/verification. Static views retain
    // their immutable backing for this one execution's native-memory domain.
    let result = unsafe { program.run_display_with_unsafe(Default::default(), None) }.unwrap();
    result
        .parse()
        .expect("usize fixture must return a decimal integer")
}

#[test]
fn static_data_identity_includes_its_sealed_tag_and_alignment() {
    let first = raw(0x7574_6638, 1);
    let same = raw(0x7574_6638, 1);
    let different_tag = raw(0x706e_6730, 1);
    let different_alignment = raw(0x7574_6638, 8);

    let mut inference = InferContext::default();
    assert_eq!(inference.unify(first.clone(), same).unwrap(), first);
    assert!(inference.unify(first.clone(), different_tag).is_err());
    assert!(inference.unify(first.clone(), different_alignment).is_err());

    let mut fingerprints = InferContext::default();
    assert_ne!(
        fingerprints.type_fingerprint(first).unwrap(),
        fingerprints.type_fingerprint(raw(0x706e_6730, 1)).unwrap(),
        "static artifact tags must participate in frozen type identity",
    );
}

#[test]
fn source_cannot_name_the_compiler_static_data_handle() {
    let app = PackageKey("static-data-boundary@0.1.0".into());
    let request = CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"static-data-boundary")),
        mode: CompilationMode::Check,
        root_package: app.clone(),
        sources: vec![SourceInput::new(
            app,
            LogicalPath::parse("src/main.glorious").unwrap(),
            br#"pub fn main(value: __StaticData<u8>) -> i64 { 0 }"#.as_slice(),
        )],
        target: "stage0-vm".into(),
        semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::new(),
        capability_manifest: vec![],
        runtime_manifest: None,
    };

    assert!(
        StageZeroCompiler::new().compile(request).is_err(),
        "ordinary source must not gain a name for the sealed static-data type"
    );
}

#[test]
fn bundled_standard_library_may_hide_static_data_behind_a_public_alias() {
    let source = "use std::Str; pub fn identity(value: Str<'static>) -> Str<'static> { value } pub fn main() -> i64 { 42 }";
    let outcome = StageZeroCompiler::new().compile(bundled_request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn quoted_literal_lowers_to_sealed_static_data_through_str() {
    let source = "use std::Str; pub fn main() -> usize { Str::len(\"sealed UTF-8\") }";
    assert_eq!(run_bundled_usize(source), 12);
}

#[test]
fn static_str_literal_wrapper_is_not_an_application_api() {
    let source = "pub fn main() -> std::Str<'static> { std::__g1_wrap_static_str(\"hi\") }";
    assert!(
        StageZeroCompiler::new().compile(bundled_request(source)).is_err(),
        "the compiler may select the private literal wrapper, but source may not call it"
    );
}

#[test]
fn byte_literal_lowers_to_a_distinct_raw_static_data_tag() {
    let standard = PackageKey("std@0.1.0".into());
    let request = CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"raw-static-data-literal")),
        mode: CompilationMode::Build,
        root_package: standard.clone(),
        sources: vec![SourceInput::new(
            standard,
            LogicalPath::parse("src/lib.glorious").unwrap(),
            br#"pub fn main() -> __StaticData<u8> { b"\x00\xff" }"#.as_slice(),
        )],
        target: "stage0-vm".into(),
        semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::new(),
        capability_manifest: vec![],
        runtime_manifest: None,
    };

    let outcome = StageZeroCompiler::new().compile(request).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(
        outcome.artifact.unwrap().run_display().unwrap(),
        "static<0x4752414e44494f53455f52415755385f, align 1>([0, 255])"
    );
}

#[test]
fn bundled_static_views_preserve_static_bounds_and_subslice_length() {
    let source = "use std::{Result, Str}; pub fn main() -> usize { handle Str::subslice(\"sealed\", 1, 4) { Result::Ok(value) => Str::len(value), Result::Err(_) => 0 } }";
    assert_eq!(run_bundled_usize(source), 4);
}

#[test]
fn static_str_bytes_uses_the_same_public_slice_view_as_vec() {
    let source = "use std::*; pub fn main() -> usize { let view = Str::as_bytes(\"hi\"); Slice::len(&view) }";
    assert_eq!(run_bundled_usize(source), 2);
}

#[test]
fn raw_byte_literal_lowers_to_the_public_static_slice_view() {
    let source = r#"
        use std::*;
        pub fn byte_count(value: Slice<'static, u8>) -> usize { Slice::len(&value) }
        pub fn main() -> usize { byte_count(b"\x00\xffA") }
    "#;
    assert_eq!(run_bundled_usize(source), 3);
}


#[test]
fn stage0_artifact_preserves_a_sealed_static_data_type() {
    let static_type = VmType::StaticData {
        element: Box::new(VmType::U8),
        tag: 0x7574_6638,
        alignment: 1,
    };
    let mut artifact = CandidateVmArtifact {
        schema: STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: VmFunction {
            safety: grandiose_stage0::Safety::Safe,
            unsafe_execution: false,
            definition: grandiose_stage0::DefKey(Digest::of_bytes(b"static-data-type-artifact")),
            nominal_copy_descriptors: vec![],
            captures: 0,
            parameters: 0,
            // The static register is deliberately unused here: the test is
            // about immutable type identity crossing the artifact boundary,
            // not about manufacturing a handle outside trusted lowering.
            registers: vec![VmType::Unit, static_type.clone()],
            instructions: vec![
                VmInstruction::ConstUnit { dst: 0 },
                VmInstruction::Return { value: 0 },
            ],
        },
        fingerprint: Digest::of_bytes(b"uninitialized"),
    };
    artifact.fingerprint = artifact.computed_fingerprint();

    let decoded = decode_artifact(&encode_artifact(&artifact)).unwrap();
    assert_eq!(decoded.function.registers[1], static_type);
    verify_vm(decoded).expect("a sealed static type must survive verification");
}
